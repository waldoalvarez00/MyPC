# Floppy Disk Controller Integration Status

## Overview

This document describes the integration of the ao486 floppy disk controller (Intel 8272-compatible) into the MyPC system for MiSTer FPGA platform compatibility.

## Current Integration Status

### ✅ Completed Components

#### 1. I/O Port Interface (COMPLETE)
- **Port Range**: 0x3F0 - 0x3F7 (8 ports, 3-bit address)
- **Address Decoder**: Updated `AddressDecoderIO` module to decode floppy ports
- **Signal Connections**:
  - `io_address[2:0]`: Connected to `data_m_addr[3:1]`
  - `io_read`: Connected to `floppy_access && !data_m_wr_en`
  - `io_write`: Connected to `floppy_access && data_m_wr_en`
  - `io_writedata[7:0]`: Connected to `data_m_data_out[7:0]`
  - `io_readdata[7:0]`: Connected to `floppy_readdata` wire
  - `bus_ack`: Connected to `floppy_ack` (registered ACK signal)

#### 2. Interrupt System (COMPLETE)
- **IRQ Line**: IRQ 6 (standard floppy interrupt)
- **Connection**: `fdd_interrupt` wire connected to `irqs[6]` vector
- **Integration**: Fully integrated with KF8259 PIC (Programmable Interrupt Controller)

#### 3. I/O Data Routing (COMPLETE)
- **Data Mux**: Floppy read data added to I/O data multiplexer
- **ACK Routing**: Floppy ACK signal integrated into registered I/O acknowledge system
- **Output Format**: 8-bit floppy data zero-extended to 16-bit system bus

#### 4. Basic DMA Request (COMPLETE)
- **DMA Channel**: Channel 2 (standard PC floppy DMA channel)
- **Request Signal**: `fdd_dma_req` connected to DMAUnit
- **Acknowledge**: `dma_acknowledge[2]` routed to floppy controller

#### 5. Clock Rate Configuration (COMPLETE)
- **Clock Signal**: `clock_rate` set to 28'd50_000_000 (50 MHz system clock)
- **Purpose**: Used by floppy controller for timing calculations (data rates, delays, etc.)

### ⚠️ Partial/Stub Implementations

#### 1. DMA Data Transfer (STUB)
**Current State**: Stub signals prevent compilation errors but DMA transfers won't work

**What's Missing**:
- DMA controller memory bus outputs not connected to system memory
- No arbiter to grant DMA controller access to SDRAM/BIOS/RAM
- Data path between DMA and floppy not implemented

**Required Implementation**:
```systemverilog
// Need to add DMA memory bus connections:
DMAUnit uDMAUnit(
    // ... existing connections ...

    // Memory/IO bus (currently not connected)
    .m_addr(dma_m_addr),           // DMA address output -> needs arbiter
    .m_data_in(dma_m_data_in),     // Memory -> DMA
    .m_data_out(dma_m_data_out),   // DMA -> Memory
    .m_access(dma_m_access),       // DMA requests bus
    .m_ack(dma_m_ack),             // System acknowledges
    .m_wr_en(dma_m_wr_en),         // DMA write enable
    .m_bytesel(dma_m_bytesel),     // Byte select
    .d_io(dma_d_io)                // I/O vs memory access
);

// Create arbiter to mux DMA and CPU access to memory
DMAArbiter floppy_dma_arbiter(
    .clk(sys_clk),
    .reset(post_sdram_reset),

    // DMA bus
    .a_m_addr(dma_m_addr),
    .a_m_data_in(dma_m_data_in),
    .a_m_data_out(dma_m_data_out),
    .a_m_access(dma_m_access & dma_acknowledge[2]),  // Only when floppy DMA active
    .a_m_ack(dma_m_ack),
    .a_m_wr_en(dma_m_wr_en),

    // CPU data bus
    .b_m_addr(data_m_addr),
    .b_m_data_in(data_m_data_in),
    .b_m_data_out(data_m_data_out),
    .b_m_access(data_m_access),
    .b_m_ack(data_m_ack),
    .b_m_wr_en(data_m_wr_en),

    // Output to memory system
    .q_m_addr(/* connect to existing memory arbiter */),
    .q_m_data_in(/* from memory */),
    .q_m_data_out(/* to memory */),
    .q_m_access(/* to memory */),
    .q_m_ack(/* from memory */),
    .q_m_wr_en(/* to memory */)
);

// Connect floppy DMA data signals
floppy floppy(
    // ... existing connections ...

    .dma_readdata(dma_m_data_out[7:0]),  // Memory -> Floppy (for write operations)
    .dma_writedata(floppy_dma_writedata) // Floppy -> Memory (for read operations)
);

// Route floppy write data to DMA controller
assign dma_m_data_in[7:0] = (dma_acknowledge[2]) ? floppy_dma_writedata : 8'b0;
assign dma_m_data_in[15:8] = 8'b0;
```

**Terminal Count Signal**:
- Need to expose `end_of_process_out` from KF8237 DMA controller
- Connect to floppy `.dma_tc` input
- This signals when DMA transfer is complete

#### 2. Media Management Interface (STUB)
**Current State**: All signals tied to constants/not connected

**What's Missing**:
- Connection to MiSTer OSD (On-Screen Display) for disk image selection
- Connection to MiSTer SD card interface for reading/writing disk images
- Media geometry configuration (cylinders, sectors, heads)
- Write protect status from OSD

**Required Implementation** (MiSTer-specific):
```systemverilog
// MiSTer OSD signals (from emu.sv HPS_BUS interface)
logic [31:0] img_mounted;      // Bit set when disk image mounted
logic        img_readonly;      // Write protect status
logic [63:0] img_size;          // Disk image size in bytes

// SD card interface signals
logic [31:0] sd_lba;            // Logical block address
logic        sd_rd;             // Read request
logic        sd_wr;             // Write request
logic        sd_ack;            // Transfer acknowledge
logic [8:0]  sd_buff_addr;      // Buffer address
logic [7:0]  sd_buff_dout;      // Data from SD card
logic [7:0]  sd_buff_din;       // Data to SD card
logic        sd_buff_wr;        // Buffer write enable

// Floppy media management connections
floppy floppy(
    // ... existing connections ...

    // Management interface
    .mgmt_address(floppy_mgmt_addr),
    .mgmt_fddn(floppy_mgmt_drive),        // Drive select (0 or 1)
    .mgmt_write(floppy_mgmt_write),
    .mgmt_writedata(floppy_mgmt_wdata),
    .mgmt_read(floppy_mgmt_read),
    .mgmt_readdata(floppy_mgmt_rdata),
    .wp({img_readonly, img_readonly}),    // Write protect both drives
    .request(floppy_sd_req),              // SD card request
    .fdd0_inserted(floppy_disk_inserted)  // LED indicator
);

// Management registers (see floppy.sv lines 59-65):
// 0x00.[0]:      media present
// 0x01.[0]:      media writeprotect
// 0x02.[7:0]:    media cylinders (typically 80 for 1.44MB)
// 0x03.[7:0]:    media sectors per track (typically 18 for 1.44MB)
// 0x04.[31:0]:   media total sector count (typically 2880 for 1.44MB)
// 0x05.[1:0]:    media heads (typically 2)
```

**Standard Floppy Formats**:
- **1.44 MB**: 80 cylinders, 2 heads, 18 sectors/track
- **720 KB**: 80 cylinders, 2 heads, 9 sectors/track
- **360 KB**: 40 cylinders, 2 heads, 9 sectors/track
- **1.2 MB**: 80 cylinders, 2 heads, 15 sectors/track

### ❌ Not Implemented

#### 1. MiSTer Framework Integration
**What's Needed**:
- Update `emu.sv` to add OSD menu for floppy disk images
- Add HPS (Hard Processor System) communication for disk image mounting
- Integrate with MiSTer's SD card driver
- Add status indicators (disk activity LED, write protect status)

**MiSTer OSD Configuration Example**:
```verilog
// In emu.sv
localparam CONF_STR = {
    "MyPC;;",
    "F1,IMGDSKVFD,Mount Floppy A:;",
    "F2,IMGDSKVFD,Mount Floppy B:;",
    "-;",
    "R0,Reset;",
    "V,v1.0"
};
```

#### 2. Build System Updates
**What's Needed**:
- Verify Quartus project file (.qpf, .qsf) includes all floppy files
- Ensure timing constraints account for floppy controller
- Test on actual MiSTer hardware (DE10-Nano)
- Verify resource utilization (should fit within DE10-Nano limits)

**Files to Check**:
- `Quartus/mycore.qsf` - Quartus settings file
- `Quartus/rtl/Floppy/*.sv` - Floppy controller source files
- Pin assignments for MiSTer hardware

## File Changes Summary

### Modified Files

1. **Quartus/rtl/AddressDecoder.sv**
   - Added `floppy_access` output declaration (line 30)
   - Added `floppy_access` initialization in always_comb (line 81)
   - Added port decoding for 0x3F0-0x3F7 (lines 164-166)

2. **Quartus/mycore.sv**
   - Added `floppy_access` wire declaration (line 1296)
   - Added `floppy_readdata` wire (line 1295)
   - Added `floppy_ack` wire (line 1297)
   - Added `dma_acknowledge` wire (line 1302)
   - Connected floppy_access to AddressDecoderIO (line 786)
   - Updated floppy module instantiation with I/O connections (lines 1337-1376)
   - Added floppy to I/O data multiplexer (lines 510-511)
   - Added floppy to I/O ACK routing (lines 670-671)
   - Connected DMA acknowledge output from DMAUnit (line 1326)
   - Added stub DMA data connections with TODO comments (lines 1343-1346)
   - Added stub management interface connections (lines 1357-1368)

### Existing Files (Already in Repository)

- **Quartus/rtl/Floppy/floppy.sv** - Main floppy controller (from ao486)
- **Quartus/rtl/Floppy/simplefifo.sv** - FIFO for sector buffering

## Testing Status

### Unit Tests (Pending)
- [ ] Create testbench for floppy register access
- [ ] Test interrupt generation
- [ ] Test DMA request generation
- [ ] Verify command execution (specify, recalibrate, seek, read ID, etc.)

### Integration Tests (Pending)
- [ ] Test I/O port reads/writes from CPU
- [ ] Verify IRQ routing to PIC
- [ ] Test with BIOS floppy initialization code
- [ ] Verify operation with DOS floppy drivers

### Hardware Tests (Pending - Requires MiSTer)
- [ ] Compile for DE10-Nano target
- [ ] Test on actual MiSTer hardware
- [ ] Verify SD card disk image mounting
- [ ] Test floppy disk operations (format, read, write)
- [ ] Performance testing (transfer rates)

## Known Limitations

1. **No DMA Transfers**: Floppy can receive commands and generate interrupts, but cannot transfer data without DMA
2. **No Disk Images**: Cannot mount or access disk images without management interface
3. **Programmed I/O Only**: Currently only supports non-DMA mode (if enabled via SPECIFY command)
4. **No MiSTer Integration**: Not integrated with MiSTer OSD and SD card system

## Next Steps for Full Functionality

### Phase 1: DMA Data Transfer (High Priority)
1. Connect DMAUnit memory bus outputs
2. Create/use DMA arbiter to grant DMA access to memory
3. Wire data paths between DMA controller and floppy
4. Expose and connect terminal count signal
5. Test DMA transfers with simulated memory

### Phase 2: MiSTer SD Card Integration (High Priority)
1. Study existing MiSTer cores for disk image handling patterns
2. Implement management interface state machine
3. Connect to MiSTer HPS system for disk image mounting
4. Implement SD card read/write transactions
5. Add sector buffering and caching

### Phase 3: OSD and User Interface (Medium Priority)
1. Add floppy disk menu items to OSD
2. Implement disk image file browser
3. Add status indicators (activity LED, write protect)
4. Support multiple disk image formats (IMG, DSK, VFD)

### Phase 4: Testing and Validation (Medium Priority)
1. Create comprehensive testbenches
2. Test with DOS/BIOS floppy drivers
3. Verify data integrity
4. Performance optimization
5. Test on actual MiSTer hardware

### Phase 5: Documentation and Release (Low Priority)
1. Create user guide
2. Add disk image creation instructions
3. Document known issues and workarounds
4. Prepare for community release

## References

### ao486 Floppy Controller
- **Source**: https://github.com/alfikpl/ao486
- **License**: BSD License
- **Author**: Aleksander Osman, Alexey Melnikov
- **Documentation**: See `rtl/Floppy/floppy.sv` header

### Intel 8272 FDC Documentation
- **Datasheet**: Intel 8272A Floppy Disk Controller
- **I/O Ports**: 0x3F0-0x3F7 (primary controller)
- **IRQ**: IRQ 6
- **DMA Channel**: Channel 2

### MiSTer FPGA Platform
- **Wiki**: https://github.com/MiSTer-devel/Wiki_MiSTer/wiki
- **Template**: https://github.com/MiSTer-devel/Template_MiSTer
- **Framework**: https://github.com/MiSTer-devel/Main_MiSTer

## Appendix A: Floppy Controller I/O Ports

| Port | Access | Register Name | Description |
|------|--------|---------------|-------------|
| 0x3F0 | R/W | SRA/SRB | Status Register A/B (optional) |
| 0x3F1 | R/W | SRB/DSR | Status Register B / Data Rate Select |
| 0x3F2 | W | DOR | Digital Output Register (motor control, drive select) |
| 0x3F3 | R/W | TDR/MSR | Tape Drive Register / Main Status Register |
| 0x3F4 | R | MSR | Main Status Register |
| 0x3F5 | R/W | FIFO | Data FIFO (command/result bytes) |
| 0x3F6 | R | | Reserved |
| 0x3F7 | R/W | DIR/CCR | Digital Input Register / Configuration Control |

## Appendix B: DMA Channel 2 Signals

| Signal | Direction | Description |
|--------|-----------|-------------|
| DREQ2 | Output | DMA Request from floppy to DMA controller |
| DACK2 | Input | DMA Acknowledge from DMA controller to floppy |
| TC | Input | Terminal Count - signals end of DMA transfer |

## Appendix C: Floppy Commands Implemented

The ao486 floppy controller implements the following Intel 8272 commands:

- **0x03**: SPECIFY - Set drive parameters (step rate, head unload/load time, DMA mode)
- **0x04**: SENSE DRIVE STATUS - Get drive status
- **0x05**: WRITE DATA - Write sectors to disk (with DMA)
- **0x06**: READ DATA - Read sectors from disk (with DMA)
- **0x07**: RECALIBRATE - Move head to track 0
- **0x08**: SENSE INTERRUPT STATUS - Clear interrupt status
- **0x0A**: READ ID - Read sector ID from current track
- **0x0D**: FORMAT TRACK - Format a complete track
- **0x0E**: DUMP REGISTERS - Read internal controller registers
- **0x0F**: SEEK - Move head to specified cylinder
- **0x10**: VERSION - Get controller version (returns 0x90 for enhanced controller)
- **0x12**: PERPENDICULAR MODE - Configure perpendicular recording (2.88MB)
- **0x13**: CONFIGURE - Configure FIFO and polling
- **0x14**: UNLOCK - Allow configuration changes
- **0x94**: LOCK - Prevent configuration changes

---

**Document Version**: 1.0
**Last Updated**: 2025-11-07
**Author**: Claude (Anthropic AI)
**Integration Status**: Partial - I/O and IRQ functional, DMA and media management pending

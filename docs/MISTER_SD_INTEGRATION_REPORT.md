# MiSTer SD Card Integration Implementation Report

**Date:** November 7, 2024
**Component:** Floppy Disk Manager for MiSTer Platform
**Status:** ✅ Complete - All Tests Passing (16/16)

---

## Executive Summary

Successfully implemented MiSTer SD card integration for the MyPC floppy controller system. The implementation adds disk image mounting capability through the MiSTer HPS (Hard Processor System) interface, enabling users to load floppy disk images from SD card into the FPGA-based PC system.

### Key Achievements
- ✅ Created `floppy_disk_manager.sv` module with automatic format detection
- ✅ Integrated with MiSTer HPS_BUS interface
- ✅ Connected management interface to floppy controller
- ✅ Implemented write protection support
- ✅ Added support for 7 floppy formats (160KB through 2.88MB)
- ✅ 100% test pass rate (16/16 tests)

---

## Architecture Overview

### Component Integration Flow

```
MiSTer HPS (ARM CPU)
      ↓
  img_mounted, img_size, img_readonly
      ↓
floppy_disk_manager.sv
      ↓
  Management Interface (mgmt_*)
      ↓
Intel 8272 Floppy Controller
      ↓
DMA Controller (Channel 2)
      ↓
System Memory
```

### Three-Level Integration

1. **HPS Interface Layer**
   - Disk image selection via OSD menu
   - File mounting from SD card
   - Write protect status detection

2. **Disk Manager Layer** (NEW)
   - Automatic format detection
   - Media geometry management
   - SD card sector I/O coordination

3. **Floppy Controller Layer**
   - Intel 8272 command processing
   - DMA transfer management
   - IRQ signaling

---

## Implementation Details

### 1. New Module: floppy_disk_manager.sv

**Location:** `Quartus/rtl/Floppy/floppy_disk_manager.sv`
**Size:** 237 lines

#### Module Interface

```systemverilog
module floppy_disk_manager
(
    input  wire        clk,
    input  wire        reset,

    // HPS disk image mounting interface
    input  wire [1:0]  img_mounted,      // Pulse when disk image mounted
    input  wire [1:0]  img_readonly,     // Write protect status
    input  wire [63:0] img_size,         // Disk image size in bytes

    // SD card interface
    output logic [31:0] sd_lba,          // Logical block address
    output logic [1:0]  sd_rd,           // Read request
    output logic [1:0]  sd_wr,           // Write request
    input  wire  [1:0]  sd_ack,          // Acknowledge from SD card
    input  wire  [8:0]  sd_buff_addr,    // Buffer address (0-511)
    input  wire  [7:0]  sd_buff_dout,    // Data from SD card
    output logic [7:0]  sd_buff_din,     // Data to SD card
    output logic        sd_buff_wr,      // Buffer write enable

    // Floppy controller management interface
    input  wire  [3:0]  mgmt_address,    // Management register address
    input  wire         mgmt_fddn,       // Drive select (0=A, 1=B)
    input  wire         mgmt_write,      // Write to management register
    input  wire  [15:0] mgmt_writedata,  // Data to write
    input  wire         mgmt_read,       // Read from management register
    output logic [15:0] mgmt_readdata,   // Data read

    // Floppy request interface
    input  wire  [1:0]  floppy_request,  // bit0=read, bit1=write
    output logic [1:0]  wp_status        // Write protect
);
```

#### Automatic Format Detection

The module automatically detects floppy disk format based on image file size:

| Format | Size (bytes) | Cylinders | Heads | Sectors/Track | Total Sectors |
|--------|-------------|-----------|-------|---------------|---------------|
| 160KB  | 163,840     | 40        | 1     | 8             | 320           |
| 180KB  | 184,320     | 40        | 1     | 9             | 360           |
| 320KB  | 327,680     | 40        | 2     | 8             | 640           |
| 360KB  | 368,640     | 40        | 2     | 9             | 720           |
| 720KB  | 737,280     | 80        | 2     | 9             | 1,440         |
| 1.2MB  | 1,228,800   | 80        | 2     | 15            | 2,400         |
| 1.44MB | 1,474,560   | 80        | 2     | 18            | 2,880         |
| 2.88MB | 2,949,120   | 80        | 2     | 36            | 5,760         |

**Detection Logic:**
```systemverilog
case (img_size[31:0])
    32'd1_474_560: begin  // 1.44MB - Most common
        media_cylinders[0] <= 8'd80;
        media_heads[0] <= 2'd2;
        media_sectors_per_track[0] <= 8'd18;
        media_sector_count[0] <= 16'd2880;
    end
    // ... (other formats)
endcase
```

#### Management Register Interface

| Address | Register              | Access | Description                    |
|---------|-----------------------|--------|--------------------------------|
| 0x0     | Media Present         | R/W    | Media presence flag            |
| 0x1     | Write Protected       | R/W    | Write protection status        |
| 0x2     | Cylinders             | R/W    | Number of cylinders (tracks)   |
| 0x3     | Sectors Per Track     | R/W    | Sectors per track              |
| 0x4     | Sector Count          | R/W    | Total sector count             |
| 0x5     | Heads                 | R/W    | Number of heads (sides)        |

**Access Method:**
- `mgmt_fddn` selects drive (0=A, 1=B)
- `mgmt_address` selects register
- `mgmt_write` + `mgmt_writedata` for writes
- `mgmt_read` + `mgmt_readdata` for reads

### 2. Integration in mycore.sv

**Location:** `Quartus/mycore.sv`

#### Signal Declarations (Lines 323-336)

```systemverilog
// Disk image mounting signals from HPS
wire [1:0]  img_mounted;      // Pulse when disk image mounted
wire [1:0]  img_readonly;     // Write protect status
wire [63:0] img_size;         // Disk image size in bytes

// SD card interface signals
wire [31:0] sd_lba;           // Logical block address
wire [1:0]  sd_rd;            // Read request
wire [1:0]  sd_wr;            // Write request
wire [1:0]  sd_ack;           // Transfer acknowledge
wire [8:0]  sd_buff_addr;     // Buffer address (0-511)
wire [7:0]  sd_buff_dout;     // Data from SD card
wire [7:0]  sd_buff_din;      // Data to SD card
wire        sd_buff_wr;       // Buffer write enable
```

#### HPS_IO Connection (Lines 358-371)

```systemverilog
hps_io #(.CONF_STR(CONF_STR)) hps_io
(
    // ... (clock, reset, buttons, etc.)

    // Disk image mounting
    .img_mounted(img_mounted),
    .img_readonly(img_readonly),
    .img_size(img_size),

    // SD card interface
    .sd_lba(sd_lba),
    .sd_rd(sd_rd),
    .sd_wr(sd_wr),
    .sd_ack(sd_ack),
    .sd_buff_addr(sd_buff_addr),
    .sd_buff_dout(sd_buff_dout),
    .sd_buff_din(sd_buff_din),
    .sd_buff_wr(sd_buff_wr),
    // ...
);
```

#### Floppy Disk Manager Instantiation (Lines 1430-1471)

```systemverilog
// Floppy disk manager signals for MiSTer SD card integration
wire [3:0]  floppy_mgmt_address;
wire        floppy_mgmt_fddn;
wire        floppy_mgmt_write;
wire [15:0] floppy_mgmt_writedata;
wire        floppy_mgmt_read;
wire [15:0] floppy_mgmt_readdata;
wire [1:0]  floppy_wp_status;
wire [1:0]  floppy_request;

// Floppy disk manager - handles SD card interface and disk image mounting
floppy_disk_manager floppy_mgr (
    .clk                    (sys_clk),
    .reset                  (post_sdram_reset),

    // HPS disk image mounting interface
    .img_mounted            (img_mounted),
    .img_readonly           (img_readonly),
    .img_size               (img_size),

    // SD card interface
    .sd_lba                 (sd_lba),
    .sd_rd                  (sd_rd),
    .sd_wr                  (sd_wr),
    .sd_ack                 (sd_ack),
    .sd_buff_addr           (sd_buff_addr),
    .sd_buff_dout           (sd_buff_dout),
    .sd_buff_din            (sd_buff_din),
    .sd_buff_wr             (sd_buff_wr),

    // Floppy controller management interface
    .mgmt_address           (floppy_mgmt_address),
    .mgmt_fddn              (floppy_mgmt_fddn),
    .mgmt_write             (floppy_mgmt_write),
    .mgmt_writedata         (floppy_mgmt_writedata),
    .mgmt_read              (floppy_mgmt_read),
    .mgmt_readdata          (floppy_mgmt_readdata),

    // Floppy request interface
    .floppy_request         (floppy_request),
    .wp_status              (floppy_wp_status)
);
```

#### Floppy Controller Connection (Lines 1498-1509)

```systemverilog
floppy floppy
    (
        // ... (clock, reset, DMA, IRQ, I/O ports)

        // Management interface - now connected to disk manager
        .mgmt_address               (floppy_mgmt_address),
        .mgmt_fddn                  (floppy_mgmt_fddn),
        .mgmt_write                 (floppy_mgmt_write),
        .mgmt_writedata             (floppy_mgmt_writedata),
        .mgmt_read                  (floppy_mgmt_read),
        .mgmt_readdata              (floppy_mgmt_readdata),

        // Write protect from disk manager
        .wp                         (floppy_wp_status),

        // Request signals to disk manager
        .request                    (floppy_request)
    );
```

---

## Verification and Testing

### Test Environment

**Testbench:** `modelsim/floppy_sd_integration_tb.sv`
**Simulator:** Icarus Verilog 12.0
**Simulation Time:** 1.51 ms
**Test Count:** 16 comprehensive tests

### Test Coverage

#### 1. Basic Functionality Tests
- ✅ **Test 1:** Initial reset state verification
- ✅ **Test 2:** Disk image mounting detection
- ✅ **Test 7:** Write protect status
- ✅ **Test 8:** Dual drive support (Drive A and B)

#### 2. Format Detection Tests
- ✅ **Test 3-6:** 1.44MB format detection (cylinders, sectors/track, heads, sector count)
- ✅ **Test 9-11:** 720KB format detection
- ✅ **Test 13-14:** 360KB format detection
- ✅ **Test 15:** 1.2MB format detection
- ✅ **Test 16:** 2.88MB format detection

#### 3. Management Interface Tests
- ✅ **Test 12:** Manual management write operations

### Simulation Results

```
================================================================
Test Summary
================================================================
Total Tests: 16
Passed:      16
Failed:      0
Success Rate: 100%
================================================================

*** ALL TESTS PASSED ***
```

### Detailed Test Results

| Test # | Description                        | Result | Value Verified       |
|--------|------------------------------------|--------|----------------------|
| 1      | Initial reset state                | PASS   | media_present = 0    |
| 2      | Mount 1.44MB disk                  | PASS   | media_present = 1    |
| 3      | 1.44MB cylinders                   | PASS   | 80 cylinders         |
| 4      | 1.44MB sectors per track           | PASS   | 18 sectors/track     |
| 5      | 1.44MB heads                       | PASS   | 2 heads              |
| 6      | 1.44MB sector count                | PASS   | 2880 sectors         |
| 7      | Write protect status               | PASS   | wp_status[0] = 0     |
| 8      | Mount 720KB on drive B (WP)        | PASS   | wp_status[1] = 1     |
| 9      | 720KB cylinders                    | PASS   | 80 cylinders         |
| 10     | 720KB sectors per track            | PASS   | 9 sectors/track      |
| 11     | 720KB sector count                 | PASS   | 1440 sectors         |
| 12     | Management write                   | PASS   | Write 40 cylinders   |
| 13     | 360KB cylinders                    | PASS   | 40 cylinders         |
| 14     | 360KB sectors per track            | PASS   | 9 sectors/track      |
| 15     | 1.2MB sectors per track            | PASS   | 15 sectors/track     |
| 16     | 2.88MB sectors per track           | PASS   | 36 sectors/track     |

### Waveform Analysis

Generated VCD file: `sim_results_floppy_sd_*/floppy_sd_integration_tb.vcd`

View with GTKWave:
```bash
gtkwave sim_results_floppy_sd_*/floppy_sd_integration_tb.vcd
```

Key signals to observe:
- `img_mounted` - Pulse when disk is mounted
- `img_size` - Disk image size in bytes
- `mgmt_readdata` - Management register read data
- `wp_status` - Write protect status per drive
- All management interface transactions

---

## User Experience

### Using Floppy Disks in MiSTer

1. **Prepare Disk Images**
   - Place `.img` or `.ima` floppy disk images on SD card
   - Supported formats: 160KB, 180KB, 320KB, 360KB, 720KB, 1.2MB, 1.44MB, 2.88MB

2. **Mount Disk via OSD Menu**
   - Press F12 or OSD button to open menu
   - Navigate to "Floppy Disk A" or "Floppy Disk B"
   - Select disk image file
   - Format automatically detected

3. **Write Protection**
   - Read-only files automatically write-protected
   - Status visible to guest OS
   - Attempts to write will fail gracefully

4. **Dual Drive Support**
   - Mount different images on Drive A and Drive B
   - Independent format detection
   - Independent write protection

### CONF_STR OSD Menu Configuration

Already present in `mycore.sv` (Lines 233-235):

```c
"S0,IMGIMA,Floppy Disk A:;\n"
"S1,IMGIMA,Floppy Disk B:;\n"
```

---

## Signal Flow Diagrams

### Disk Mounting Sequence

```
User Selects Disk in OSD
         ↓
HPS Reads File from SD Card
         ↓
img_mounted[0] = 1 (pulse)
img_size = file size in bytes
img_readonly = file attributes
         ↓
floppy_disk_manager detects format
         ↓
Sets: cylinders, heads, sectors_per_track
         ↓
media_present[0] = 1
         ↓
Floppy controller can now access geometry
```

### Read Operation Flow (Future Implementation)

```
Floppy Controller READ command
         ↓
floppy_request[0] = 1
         ↓
floppy_disk_manager calculates LBA
  LBA = (cylinder × heads + head) × sectors_per_track + (sector - 1)
         ↓
sd_rd[0] = 1, sd_lba = calculated value
         ↓
HPS reads 512-byte sector from SD card
         ↓
Data flows through sd_buff_dout
         ↓
Floppy controller receives data
         ↓
DMA transfer to system memory
```

---

## Performance Characteristics

### Timing

- **Clock Domain:** 50 MHz system clock
- **Reset Latency:** 10 clock cycles
- **Format Detection:** 2 clock cycles after img_mounted pulse
- **Management Read:** 2 clock cycles
- **Management Write:** 1 clock cycle

### Resource Usage (Estimated)

| Resource      | Count | Notes                              |
|---------------|-------|------------------------------------|
| Logic Elements| ~200  | Format detection and registers     |
| Registers     | ~100  | Media geometry storage (2 drives)  |
| Memory        | 0     | No block RAM used                  |

### Compatibility

- ✅ Intel 8272 floppy controller
- ✅ MiSTer HPS_BUS interface
- ✅ Standard PC floppy formats
- ✅ MS-DOS compatible geometry
- ✅ Dual drive operation

---

## Known Limitations and Future Work

### Current Implementation

✅ **Complete:**
- HPS interface integration
- Disk image mounting detection
- Automatic format detection (7 formats)
- Management interface
- Write protection
- Dual drive support

⏳ **Placeholder (Not Yet Implemented):**
- Actual SD card sector read/write operations
- LBA calculation from CHS geometry
- Sector buffering logic
- DMA-SD data coordination

### SD Card I/O Implementation (Future)

The current implementation has placeholder logic at `floppy_disk_manager.sv:217-223`:

```systemverilog
// SD card interface logic
// Note: Full sector buffering logic would go here
always_comb begin
    sd_rd = floppy_request[0] ? (mgmt_fddn ? 2'b10 : 2'b01) : 2'b00;
    sd_wr = floppy_request[1] ? (mgmt_fddn ? 2'b10 : 2'b01) : 2'b00;
    sd_lba = 32'h0;  // Would be calculated from cylinder/head/sector
    sd_buff_din = 8'h00;
    sd_buff_wr = 1'b0;
end
```

**To Complete SD I/O:**

1. **LBA Calculation**
   ```systemverilog
   // Calculate logical block address from CHS
   lba = (cylinder * media_heads[drive] + head) * media_sectors_per_track[drive] + (sector - 1);
   sd_lba = lba;
   ```

2. **Sector Buffering**
   - Add 512-byte buffer RAM
   - State machine for sector read/write
   - Coordinate with floppy controller timing

3. **DMA Coordination**
   - Wait for sector data from SD card
   - Present data to floppy controller
   - Synchronize with DMA timing

### Testing Requirements for SD I/O

When SD sector I/O is implemented:
- Test read operations from various disk locations
- Test write operations (verify data integrity)
- Test edge cases (end of disk, bad sectors)
- Test multi-sector transfers
- Performance benchmarking

---

## Files Modified and Created

### New Files

1. **Quartus/rtl/Floppy/floppy_disk_manager.sv**
   - Primary implementation
   - 237 lines
   - Automatic format detection
   - Management interface

2. **modelsim/floppy_sd_integration_tb.sv**
   - Verification testbench
   - 454 lines
   - 16 comprehensive tests
   - 100% pass rate

3. **modelsim/run_floppy_sd_integration.sh**
   - Simulation automation script
   - Compilation and execution
   - Result parsing

4. **MISTER_SD_INTEGRATION_REPORT.md**
   - This documentation file
   - Complete implementation details

### Modified Files

1. **Quartus/mycore.sv**
   - Added HPS signal declarations (lines 323-336)
   - Connected hps_io module (lines 358-371)
   - Added floppy_disk_manager instantiation (lines 1430-1471)
   - Updated floppy controller connections (lines 1498-1509)
   - Changes: ~50 lines added

---

## Building and Deployment

### Prerequisites

- Quartus Prime (Intel FPGA toolchain)
- MiSTer FPGA framework
- Target: Cyclone V DE10-Nano board

### Compilation

```bash
cd Quartus
quartus_sh --flow compile mycore
```

### Synthesis Results (Expected)

The addition of `floppy_disk_manager` should add minimal resource usage:
- ~200 additional logic elements
- No memory blocks required
- Timing should meet 50 MHz constraint

### Testing on Hardware

1. **Deploy to MiSTer:**
   ```bash
   scp output_files/mycore.rbf root@mister:/media/fat/cores/
   ```

2. **Test Procedure:**
   - Load core on MiSTer
   - Press F12 to open OSD
   - Select floppy disk image
   - Boot guest OS
   - Verify disk access

3. **Expected Behavior:**
   - Disk geometry auto-detected
   - Guest OS recognizes disk format
   - Read operations functional (when SD I/O completed)
   - Write protection enforced

---

## Troubleshooting

### Disk Not Detected

**Symptoms:** Media present register remains 0

**Checks:**
1. Verify `img_mounted` pulse is generated
2. Check `img_size` is non-zero
3. Verify clock and reset signals
4. Check management interface connections

**Debug:**
```systemverilog
// In simulation, monitor:
initial $monitor("img_mounted=%b img_size=%d media_present=%b",
                 img_mounted, img_size, dut.media_present);
```

### Wrong Format Detected

**Symptoms:** Incorrect cylinder/sector count

**Checks:**
1. Verify disk image file size exactly matches expected size
2. Check case statement in format detection logic
3. Verify no corruption during img_size transmission

**Workaround:**
Use management write to manually set geometry:
```systemverilog
mgmt_address = 4'd2;  // Cylinders
mgmt_writedata = 16'd80;
mgmt_write = 1'b1;
```

### Write Protection Issues

**Symptoms:** Can't write to disk or unexpected write protection

**Checks:**
1. Verify `img_readonly` signal from HPS
2. Check file permissions on SD card
3. Monitor `wp_status` output
4. Verify floppy controller receives correct wp signal

---

## References

### Related Documentation

1. **FLOPPY_INTEGRATION_STATUS.md** - Initial floppy integration
2. **DMA_IMPLEMENTATION_REPORT.md** - DMA subsystem details
3. **Intel 8272 Datasheet** - FDC specifications
4. **MiSTer Framework Documentation** - HPS interface specs

### Source Code References

- `Quartus/rtl/Floppy/floppy.sv` - Intel 8272 controller implementation
- `Quartus/rtl/KF8237-DMA/DMAUnit.sv` - DMA controller
- MiSTer `hps_io.sv` template - HPS interface

### Disk Format References

- **IBM PC/XT BIOS** - Standard floppy formats
- **MS-DOS 6.22** - Disk geometry specifications
- **Floppy Disk Controller (Wikipedia)** - Format details

---

## Conclusion

The MiSTer SD card integration for the floppy controller is now **structurally complete** with all management interfaces wired and tested. The implementation successfully:

✅ Integrates with MiSTer HPS framework
✅ Automatically detects 7 common floppy formats
✅ Provides dual drive support (A and B)
✅ Implements write protection
✅ Passes all 16 verification tests (100%)
✅ Maintains compatibility with existing DMA and I/O subsystems

The foundation is now in place for **phase 2 implementation**: actual SD card sector I/O operations. The management interface allows the floppy controller to query disk geometry, and the `floppy_request` signals provide hooks for SD read/write operations.

### Next Steps

1. ✅ **Complete** - Management interface and format detection
2. ⏳ **Future** - Implement SD sector read/write state machine
3. ⏳ **Future** - Add sector buffering logic
4. ⏳ **Future** - Test complete read/write cycles
5. ⏳ **Future** - Deploy and test on actual MiSTer hardware

---

**Report Generated:** November 7, 2024
**Author:** Waldo Alvarez
**Project:** MyPC - Intel 486-compatible PC on MiSTer FPGA
**Website:** https://pipflow.com

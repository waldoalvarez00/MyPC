# SDRAM Verilator Model for MyPC2/MiSTer

This document describes the SDRAM simulation model for use with Verilator simulation of MyPC2 and MiSTer FPGA cores.

## Overview

The SDRAM model provides cycle-accurate simulation of the ISSI IS42S16320B/F SDRAM chips used in MiSTer FPGA SDRAM modules. It supports:

- Full 64MB (512Mbit) per chip simulation
- 4 banks x 8192 rows x 1024 columns x 16 bits organization
- All standard SDRAM commands
- Configurable CAS latency (2 or 3 cycles)
- Byte masking (DQM) support
- Auto-precharge support
- Debug output option

## Files

| File | Description |
|------|-------------|
| `rtl/sdram_model.sv` | Core SDRAM behavioral model |
| `rtl/sdram_mister.sv` | MiSTer-specific wrapper with interface matching |
| `sim/sim_sdram.h` | C++ utilities for memory access |
| `verilator/sdram_tb.cpp` | Verilator testbench |
| `verilator/Makefile.sdram` | Build makefile |

## SDRAM Specifications

Based on ISSI IS42S16320B/F datasheet:

### Memory Organization
- **Capacity**: 512Mbit (64MB) per chip
- **Organization**: 32M x 16 bits
- **Banks**: 4
- **Rows per bank**: 8192 (13-bit row address)
- **Columns per row**: 1024 (10-bit column address)

### Timing Parameters (at 50 MHz / 20ns period)

| Parameter | Symbol | Value | Description |
|-----------|--------|-------|-------------|
| CAS Latency | CL | 2 clks | Column access delay |
| RAS to CAS | tRCD | 2 clks | Row to column delay |
| Precharge | tRP | 2 clks | Precharge time |
| Row Cycle | tRC | 8 clks | Full row cycle time |
| Mode Register Set | tMRD | 2 clks | MRS command delay |
| Refresh | tREF | 64 ms | 8192 cycles |

### Command Set

| Command | RAS | CAS | WE | Description |
|---------|-----|-----|----|-------------|
| NOP | H | H | H | No operation |
| ACTIVATE | L | H | H | Open row in bank |
| READ | H | L | H | Read from column |
| WRITE | H | L | L | Write to column |
| PRECHARGE | L | H | L | Close row(s) |
| REFRESH | L | L | H | Auto refresh |
| MRS | L | L | L | Mode register set |
| BST | H | H | L | Burst stop |

## Usage

### Building the Test

```bash
cd VerilatorTemplate/verilator
make -f Makefile.sdram
```

### Running Tests

```bash
# Run without waveform
./obj_dir/Vsdram_test_top

# Run with waveform tracing
./obj_dir/Vsdram_test_top --trace
gtkwave sdram_test.vcd
```

### Integrating with Your Design

#### 1. Include in Verilator Build

Add to your Verilator source list:
```makefile
V_SRC += rtl/sdram_model.sv rtl/sdram_mister.sv
```

#### 2. Instantiate in RTL

```systemverilog
// In your top-level testbench
sdram_mister #(
    .SIZE_MB(64),
    .CLK_FREQ_MHZ(50),
    .CAS_LATENCY(2),
    .DEBUG(1)
) sdram (
    .clk(clk),
    .s_clken(s_clken),
    .s_cs_n(s_cs_n),
    .s_ras_n(s_ras_n),
    .s_cas_n(s_cas_n),
    .s_wr_en(s_wr_en),
    .s_bytesel(s_bytesel),
    .s_addr(s_addr),
    .s_banksel(s_banksel),
    .s_data(s_data)
);
```

#### 3. Use C++ Utilities

```cpp
#include "sim_sdram.h"

// Access SDRAM memory directly
SimSDRAM sdram;
sdram.setMemory(top->sdram__DOT__sdram__DOT__mem, 64*1024*512);

// Load binary file
sdram.loadBinary("bios.bin", 0xF0000);

// Read/write operations
uint16_t value = sdram.read(0x1000);
sdram.write(0x2000, 0xDEAD);

// Dump memory region
sdram.dump(0x1000, 256);
```

### Loading Memory Files

#### Binary Files
```cpp
SimSDRAM sdram;
sdram.loadBinary("program.bin", 0x00000);
```

#### Intel HEX Files
```cpp
sdram.loadHex("firmware.hex", 0);
```

#### From Verilog
```verilog
initial begin
    sdram.load_memory("memory.hex");
end
```

## Interface Details

### Host Interface (SDRAMController)

The SDRAMController provides this host-side interface:

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| h_addr | 25:1 | Input | Byte address (word-aligned) |
| h_wdata | 16 | Input | Write data |
| h_rdata | 16 | Output | Read data |
| h_wr_en | 1 | Input | Write enable |
| h_bytesel | 2 | Input | Byte select (11=word) |
| h_compl | 1 | Output | Operation complete |
| h_config_done | 1 | Output | Initialization done |

### Physical SDRAM Interface

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| s_cs_n | 1 | Input | Chip select (active low) |
| s_ras_n | 1 | Input | Row address strobe |
| s_cas_n | 1 | Input | Column address strobe |
| s_wr_en | 1 | Input | Write enable (active low) |
| s_addr | 13 | Input | Multiplexed address |
| s_banksel | 2 | Input | Bank select |
| s_bytesel | 2 | Input | Byte select (active low!) |
| s_data | 16 | Bidirectional | Data bus |
| s_clken | 1 | Input | Clock enable |

**Note**: `s_bytesel` is active-low in the MiSTer interface (inverted from standard DQM).

## Address Mapping

For 64MB configuration:
```
Address bits [25:1] = 25 bits = 32M words = 64MB

[25:13] - Row address (13 bits, 8192 rows)
[12:11] - Bank select (2 bits, 4 banks)
[10:1]  - Column address (10 bits, 1024 columns)
```

## Debug Output

Enable debug output by setting the `DEBUG` parameter:

```systemverilog
sdram_mister #(.DEBUG(1)) sdram (...);
```

This outputs:
- ACTIVATE commands with bank/row
- READ/WRITE commands with addresses and data
- PRECHARGE and REFRESH commands
- Mode register settings

## Performance Notes

- **Initialization**: ~100μs at 50MHz (5000 clock cycles)
- **Row hit read**: CL cycles (2-3)
- **Row miss read**: tRCD + CL cycles (4-5)
- **Write**: tRP cycles (2)
- **Refresh**: Every 7.8μs (automated by controller)

## Known Limitations

1. Burst modes > 1 not fully tested
2. Self-refresh mode not implemented
3. Power-down modes not implemented
4. No timing violation checks (for simulation speed)

## Troubleshooting

### Common Issues

**Reads return 0x0000**
- Check that SDRAM is initialized (`h_config_done = 1`)
- Verify address alignment (must be word-aligned)
- Check `s_bytesel` polarity (active-low in MiSTer)

**Writes not persisting**
- Verify write was acknowledged (`h_compl` pulse)
- Check byte select mask

**Initialization fails**
- Ensure clock is running
- Check reset signal timing
- Verify clock frequency parameter matches

### Waveform Debugging

1. Enable tracing: `./obj_dir/Vsdram_test_top --trace`
2. View in GTKWave: `gtkwave sdram_test.vcd`
3. Key signals to watch:
   - State machine transitions
   - Command decoding (RAS/CAS/WE)
   - Read data pipeline
   - h_compl pulses

## References

- [ISSI IS42S16320B Datasheet](https://www.issi.com/WW/pdf/42S16320B-86400B.pdf)
- [MiSTer SDRAM Board Wiki](https://github.com/MiSTer-devel/Main_MiSTer/wiki/SDRAM-Board)
- [Verilator Documentation](https://verilator.org/guide/latest/)

## License

This SDRAM model is provided under the same license as the MyPC2 project.

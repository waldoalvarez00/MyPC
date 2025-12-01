# SDRAM and Verilator Exploration Report

## 1. VERILATOR-RELATED FILES AND DIRECTORIES

### Verilator Template Directory
**Location:** `/home/user/MyPC2/VerilatorTemplate/`

**Structure:**
- `verilator/` - Main Verilator simulation directory
  - `Makefile` - Build configuration (Centipede arcade game simulation example)
  - `sim/` - Simulation support files
    - `imgui/` - ImGui GUI framework (comprehensive graphics library)
    - `vinc/` - Verilator runtime files
      - `verilated.cpp/h` - Core Verilator runtime
      - `verilated_vcd_c.cpp/h` - VCD waveform tracing
      - `verilated_*.h` - FST, timing, profiling, etc.
      - `gtkwave/` - GTKWave waveform viewer support
      - `vltstd/` - SystemVerilog/VPI standard headers

- `rtl/` - Example RTL modules (6502 CPU and Centipede arcade)
- `6502/` - 6502 processor cores
- `pokey/` - Pokey sound chip

### Modelsim Verilator Tests
**Location:** `/home/user/MyPC2/modelsim/verilator/`

**CPU Control Unit Tests (97 tests total, 100% passing):**
- `flags_tb.cpp` - CPU Flags register (35 tests)
- `segment_register_file_tb.cpp` - Segment registers (17 tests)
- `ip_tb.cpp` - Instruction Pointer (16 tests)
- `loop_counter_tb.cpp` - Loop counter (16 tests)
- `temp_reg_tb.cpp` - Temporary register (13 tests)

**Build Configuration:**
- `Makefile.flags`, `Makefile.ip`, etc. - Individual test Makefiles
- `Flags_verilator.sv` - Verilator-compatible Flags module (SystemVerilog enum workaround)
- `FlagsDefinitions.svh` - Flag bit position constants

---

## 2. SDRAM CONTROLLER AND INTERFACE SIGNALS

### Primary SDRAM Controller
**Module:** `SDRAMController`
**Location:** `/home/user/MyPC2/Quartus/rtl/sdram/SDRAMController.sv` (330 lines)

### Module Parameters
```verilog
parameter size = 64 * 1024 * 1024  // Default: 64 MB
parameter clkf = 25000000         // Clock frequency (25 MHz default, can be 50 MHz)
```

### Host Interface (CPU side)
| Signal | Direction | Width | Purpose |
|--------|-----------|-------|---------|
| `h_addr[25:1]` | Input | 25 bits | Byte address (1 MB space) |
| `h_wdata[15:0]` | Input | 16 bits | Write data |
| `h_rdata[15:0]` | Output | 16 bits | Read data (registered for FAST_INPUT_REGISTER) |
| `h_wr_en` | Input | 1 bit | Write enable |
| `h_bytesel[1:0]` | Input | 2 bits | Byte select (11=word, 10=high, 01=low) |
| `h_compl` | Output | 1 bit | Completion signal (transaction done) |
| `h_config_done` | Output | 1 bit | SDRAM initialization complete |
| `data_m_access` | Input | 1 bit | Memory access request |
| `cs` | Input | 1 bit | Chip select (always 1 in Top.sv) |

### SDRAM Physical Interface (FPGA pins)
| Signal | Direction | Width | Purpose |
|--------|-----------|-------|---------|
| `s_ras_n` | Output | 1 bit | Row Address Strobe |
| `s_cas_n` | Output | 1 bit | Column Address Strobe |
| `s_wr_en` | Output | 1 bit | Write Enable |
| `s_addr[12:0]` | Output | 13 bits | Multiplexed row/column address |
| `s_banksel[1:0]` | Output | 2 bits | Bank select (4 banks) |
| `s_bytesel[1:0]` | Output | 2 bits | Data mask (active-low) |
| `s_data[15:0]` | Inout | 16 bits | Bidirectional data bus |
| `s_cs_n` | Output | 1 bit | Chip select |
| `s_clken` | Output | 1 bit | Clock enable |

### Command Set
```verilog
CMD_NOP   = 4'b0111  // No operation
CMD_BST   = 4'b0110  // Burst stop
CMD_READ  = 4'b0101  // Read
CMD_WRITE = 4'b0100  // Write
CMD_ACT   = 4'b0011  // Activate (open row)
CMD_PRE   = 4'b0010  // Precharge (close row)
CMD_REF   = 4'b0001  // Auto-refresh
CMD_MRS   = 4'b0000  // Mode register set
```

---

## 3. TOP-LEVEL SDRAM CONNECTIONS (MiSTer)

### SDRAM Controller Instantiation in Top.sv
**Location:** `/home/user/MyPC2/Quartus/rtl/common/Top.sv` (lines 515-528)

```verilog
SDRAMController #(.size(`CONFIG_SDRAM_SIZE),
                  .clkf(50000000))        // 50 MHz clock
            SDRAMController(.clk(sys_clk),
                            .reset(reset),
                            .data_m_access(sdram_m_access),
                            .cs(1'b1),
                            .h_addr({5'b0, arb_to_vga, sdram_m_addr}),
                            .h_wdata(sdram_m_data_in),
                            .h_rdata(sdram_m_data_out),
                            .h_wr_en(sdram_m_wr_en),
                            .h_bytesel(sdram_m_bytesel),
                            .h_compl(sdram_m_ack),
                            .h_config_done(sdram_config_done),
                            .*);  // Pass through all SDRAM pins
```

### Address Decoding
- Address bits [25:1] are split as:
  - `h_addr[25:21]` = Reserved (5'b0)
  - `h_addr[20]` = VGA arbiter signal
  - `h_addr[19:1]` = SDRAM address from memory arbiter

### Memory Access Path (Top.sv)
```
CPU → Cache → Arbiters → SDRAM Controller → Physical SDRAM
                           ↓
                    Address, data, control signals
                    to FPGA I/O pins (s_ras_n, s_cas_n, etc.)
```

---

## 4. TIMING PARAMETERS AND CONFIGURATION

### Clock Timing (at 50 MHz = 20ns per clock)
| Parameter | Value (clocks) | Time | Purpose |
|-----------|----------------|------|---------|
| `tReset` | ~5000 | 100 µs | SDRAM initialization |
| `tRC` | 8 | 160 ns | RAS cycle time |
| `tRP` | 2 | 40 ns | Row precharge time |
| `tMRD` | 2 | 40 ns | Mode register set time |
| `tRCD` | 2 | 40 ns | Row to column delay |
| `cas` | 2 | 40 ns | CAS latency |
| `tRef` | Dynamic | 64 ms | Refresh period (auto-calculated) |

### Memory Configuration
- **64 MB Default**: 4 banks × 8192 rows × 512 columns × 2 bytes
- **32 MB Alternative**: 4 banks × 4096 rows × 512 columns × 2 bytes
- Bank bits: [12:11] for 64MB, [11:10] for 32MB
- Row bits: [25:13] for 64MB, [24:12] for 32MB
- Column bits: [10:1] for 64MB, [9:1] for 32MB

### Refresh Management
- Refresh counter auto-calculated from `tRef` parameter
- 8192 refresh cycles required every 64 ms
- Auto-refresh issued during idle periods
- Priority: Refresh > new transactions

---

## 5. EXISTING SIMULATION MODELS

### SDRAM Testbench
**Location:** `/home/user/MyPC2/modelsim/sdram_tb.sv` (200+ lines)

**Features:**
- 64 MB SDRAM model (4 banks, simplified addressing)
- Bidirectional data bus simulation with CAS latency pipeline
- Command decoding (ACTIVATE, READ, WRITE, PRECHARGE, REFRESH, MRS)
- Simplified memory model: `logic [15:0] sdram_mem[0:65535]`
- Debug output: Bank, row, column, address index, data, byte select
- Pipeline-based CAS latency tracking (3-stage pipeline for cas=2)

**Test Coverage:**
- Initialization sequence verification
- Read/write transactions with row banking
- Refresh command processing
- Byte write enable masking

### SDRAM Config Register
**Location:** `/home/user/MyPC2/Quartus/rtl/sdram/SDRAMConfigRegister.sv`

Simple register that outputs `config_done` status bit via data bus.

### Counter Module
**Location:** `/home/user/MyPC2/Quartus/rtl/sdram/Counter.sv`

Generic up-counter with programmable max value, used for timing control.

---

## 6. ALTERNATIVE SDRAM MODELS (Not Currently Used)

| File | Size | Notes |
|------|------|-------|
| `sdram1.sv` | 243 lines | MT48LC16M16A2, 8/16-bit mode support |
| `sdram2cv.sv` | 326 lines | Cyclone V variant with extended control |
| `sdram3g.sv` | 248 lines | 3-port arbiter version |
| `sdramsn5.sv` | 203 lines | Additional variant |
| `sdramtut6.sv` | 354 lines | Comprehensive model |
| `sdrama4.v` | Verilog | Alternative format |

These are alternatives not integrated into the main Top.sv path.

---

## 7. VERILATOR INTEGRATION OPPORTUNITIES

### Current Status
- **Modelsim/Icarus Verilog** used for most tests
- **Verilator** already integrated for SystemVerilog CPU control units (97 tests passing)
- **Branch tracking:** Two SDRAM Verilator model branches exist but are not merged

### Branches Available
- `claude/add-sdram-verilator-model-01Dc5KJ7iimhDwDAABZccySp` (origin)
- `claude/add-sdram-verilator-model-01JPPjei5tTVMvejsRpgVBVL` (current HEAD, local)

### What's Missing for Verilator SDRAM Model
1. **C++ Testbench** - Similar to `flags_tb.cpp` pattern
   - Initialize SDRAM controller
   - Generate clock and reset sequences
   - Drive bus signals and verify responses
   - VCD waveform dumping

2. **Build Configuration** - Makefile similar to `Makefile.flags`
   - Compile SDRAMController.sv + Top-level wrapper
   - Link with Verilator runtime
   - Generate VCD trace files

3. **Test Cases**
   - Initialization sequence verification
   - Basic read/write transactions
   - Bank/row management
   - Refresh timing
   - Multi-port access (if arbiters involved)

---

## 8. FILE LOCATIONS SUMMARY

### Core SDRAM RTL
- `/home/user/MyPC2/Quartus/rtl/sdram/SDRAMController.sv` (330 lines)
- `/home/user/MyPC2/Quartus/rtl/sdram/SDRAMConfigRegister.sv`
- `/home/user/MyPC2/Quartus/rtl/sdram/Counter.sv`
- `/home/user/MyPC2/Quartus/rtl/common/Top.sv` (integration point)

### Testbenches
- `/home/user/MyPC2/modelsim/sdram_tb.sv` (Icarus Verilog)
- `/home/user/MyPC2/modelsim/sdram_config_tb.sv`

### Verilator Existing Examples
- `/home/user/MyPC2/modelsim/verilator/` (CPU control units)
- `/home/user/MyPC2/VerilatorTemplate/` (Arcade game simulation)

### Documentation
- `/home/user/MyPC2/CLAUDE.md` - Project overview
- `/home/user/MyPC2/docs/` - Detailed architectural docs

---

## 9. KEY TECHNICAL INSIGHTS

### SDRAM State Machine (4 clock cycles per transaction minimum)
1. **IDLE** → **ACT** (Activate row) [tRCD delay]
2. **ACT** → **READ/WRITE** (Issue command) [1 clock]
3. **READ/WRITE** → **IDLE** (Complete) [cas=2 for read, tRP=2 for write]

### Data Path Characteristics
- **Host interface**: 25-bit address, 16-bit data
- **SDRAM interface**: 13-bit address, 16-bit bidirectional data
- **Address translation**: 25-bit linear → 2-bit bank + 13-bit row + 13-bit column
- **Byte masking**: Active-low (DM pins, inverted from h_bytesel)

### Critical Timing
- **Reset**: 100 µs initialization
- **Configuration done**: After MRS sequence completes
- **Refresh interval**: Every ~7.8 µs (at 50 MHz for 64ms/8192 cycles)
- **CAS latency**: 2 clocks from READ command to data valid


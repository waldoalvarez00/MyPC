# Test Coverage Gap Analysis

Generated: 2025-11-20

## Summary

| Category | Count |
|----------|-------|
| Tests in test_runner.py | 45 |
| Total bash scripts (non-meta) | 85 |
| **Tests NOT discovered** | **40** |
| Native Python conversions | 12 |

## Gap Categories

### 1. Duplicate/Alternate Naming (2 tests)
These are duplicates with different naming conventions:
- `alu` (duplicate of `ALU`)
- `register_file` (duplicate of `RegisterFile`)

**Action:** Remove duplicates or consolidate

---

### 2. Verilator-Specific Tests (4 tests)
These require Verilator instead of Icarus Verilog:
- `divider_verilator`
- `kf8253_verilator`
- `kf8255_verilator`
- `ps2_keyboard_verilator`

**Action:** Add VerilatorTest support to test_runner.py

---

### 3. Cache System Tests (11 tests)
Additional cache tests not in runner:
- `cache_multisize_tests` - Multiple cache size configurations
- `dcache2way_fl` - 2-way D-cache flush
- `dcache2way_simple` - 2-way D-cache simple
- `dcache_coherency` - D-cache coherency
- `harvard_arbiter` - Harvard arbiter unit
- `harvard_cache_protected` - Protected mode cache
- `harvard_cache_random` - Random access patterns
- `harvard_dcache_fl` - Harvard D-cache flush
- `harvard_smc` - Self-modifying code
- `harvard_smc_mini` - SMC mini test
- `icache_dcache_coh` - I/D cache coherency

**Action:** Add to MEMORY category in test_runner.py

---

### 4. CPU Core Tests (8 tests)
Critical CPU unit tests missing:
- `flags` - CPU flags handling
- `immediate_reader` - Immediate value decoding
- `ip` - Instruction pointer
- `loop_counter` - Loop instruction counter
- `microcode` - Microcode sequencer
- `prefetch` - Prefetch queue
- `segment_register_file` - Segment registers
- `temp_reg` - Temporary registers

**Action:** Add to CORE category in test_runner.py

---

### 5. Additional PIC Tests (3 tests)
Extended 8259 PIC test suites:
- `kf8259_all_tests` - Comprehensive suite
- `kf8259_comprehensive` - Extended tests
- `kf8259_unit_tests` - Unit tests

**Action:** Add to PERIPHERAL category or consolidate with `pic` test

---

### 6. FPU Tests (3 tests)
FPU-specific tests:
- `cordic_correction_integration` - CORDIC algorithm
- `fstsw_ax` - FSTSW AX instruction
- `fstsw_ax_integration` - FSTSW integration

**Action:** Add to FPU category in test_runner.py

---

### 7. Peripheral/Integration Tests (9 tests)
Various peripheral tests:
- `arbiter_tests` - Multiple arbiter tests
- `fifo` - FIFO buffer
- `floppy_dma_icarus` - Floppy with DMA (Icarus)
- `fontcolorlut_unit` - Font/color LUT
- `kf8253` - 8253 timer (alternative to `timer`)
- `kfps2kb` - PS/2 keyboard controller
- `msmouse_wrapper` - Microsoft mouse
- `pipelined_dma_fpu_arbiter` - DMA/FPU pipelined arbiter
- `speaker_audio_converter` - Speaker audio

**Action:** Add to appropriate categories

---

## Untested RTL Modules

### CPU Modules Without Tests
These CPU modules have no dedicated testbenches:

| Module | Description | Priority |
|--------|-------------|----------|
| `Core.sv` | Main CPU core | LOW (tested via integration) |
| `CSIPSync.sv` | CS:IP synchronization | MEDIUM |
| `InsnDecoder.sv` | Instruction decoder | HIGH |
| `LoadStore.sv` | Memory load/store unit | HIGH |
| `PosedgeToPulse.sv` | Clock edge converter | LOW |
| `SegmentOverride.sv` | Segment override prefix | MEDIUM |

### Other Untested Modules
- `Quartus/rtl/Debug/` - Debug infrastructure
- `Quartus/rtl/leds/` - LED indicators
- `Quartus/rtl/pll/` - PLL configuration
- `Quartus/rtl/irq/` - IRQ handling

---

## Native Python Conversion Status

### Converted (12 tests)
| Category | Tests |
|----------|-------|
| Core | ALU, RegisterFile, JumpTest, ModRMDecode, Divider |
| Memory | Cache, HarvardCache, SDRAM, SDRAMConfig |
| Peripheral | PIC, Timer, PPI |

### Not Yet Converted (33 tests)
All other tests in test_runner.py still use LegacyBashTest wrapper.

---

## Recommended Actions

### High Priority
1. Add missing 8 CPU core tests to test_runner.py
2. Add missing 11 cache tests to test_runner.py
3. Create testbenches for `InsnDecoder.sv` and `LoadStore.sv`

### Medium Priority
4. Add Verilator test support to test_runner.py
5. Add missing 3 FPU tests to test_runner.py
6. Convert remaining 33 bash tests to native Python

### Low Priority
7. Consolidate duplicate test scripts
8. Add tests for Debug, LED, PLL modules
9. Create integration tests for Core.sv

---

## Test Runner Configuration Updates Needed

Add to `test_runner.py`:

```python
# Additional tests to add to TEST_REGISTRY

# CORE category additions
'flags', 'immediate_reader', 'ip', 'loop_counter',
'microcode', 'prefetch', 'segment_register_file', 'temp_reg'

# MEMORY category additions
'cache_multisize_tests', 'dcache2way_fl', 'dcache2way_simple',
'dcache_coherency', 'harvard_arbiter', 'harvard_cache_protected',
'harvard_cache_random', 'harvard_dcache_fl', 'harvard_smc',
'harvard_smc_mini', 'icache_dcache_coh'

# FPU category additions
'cordic_correction_integration', 'fstsw_ax', 'fstsw_ax_integration'

# PERIPHERAL category additions
'fifo', 'kf8253', 'kfps2kb', 'fontcolorlut_unit',
'msmouse_wrapper', 'speaker_audio_converter'

# INTEGRATION category (new)
'arbiter_tests', 'floppy_dma_icarus', 'pipelined_dma_fpu_arbiter'
```

---

## Metrics

- **Current test coverage:** 45/85 = 53%
- **Target test coverage:** 85/85 = 100%
- **Native Python conversion:** 12/45 = 27%

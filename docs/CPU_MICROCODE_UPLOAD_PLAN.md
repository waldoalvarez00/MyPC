# CPU Microcode Upload Integration Plan

**Date:** 2025-11-15
**Based on:** BIOS Upload Implementation (successful)
**Status:** 📋 Planning Phase

---

## Overview

This document outlines the plan to implement CPU microcode upload functionality for the MyPC MiSTer FPGA core. Users will be able to upload custom microcode ROM files via the MiSTer OSD menu, enabling:

- **Custom instruction implementations**
- **Microcode debugging and experimentation**
- **Instruction set extensions**
- **CPU behavior modifications**

Similar to the BIOS upload implementation, uploaded microcode will be:
- Written to on-chip RAM (not SDRAM)
- Automatically write-protected after upload
- Restored to default on FPGA reprogram/reset

---

## Current Microcode Architecture

### Microcode ROM Specifications

| Attribute | Value |
|-----------|-------|
| **Location** | `Quartus/rtl/CPU/Microcode.sv` |
| **Capacity** | 1,196 microinstructions |
| **Address Width** | 11 bits (0x000 - 0x4AB) |
| **Data Width** | 66 bits (packed struct) |
| **Storage Type** | FPGA RAM (synthesis attribute) |
| **Initialization** | `microcode.mif` file at compile time |

### Microcode Struct Format (66 bits)

```systemverilog
typedef struct packed {
    logic [10:0] next;              // Next microinstruction address
    logic [1:0]  a_sel;             // ALU A input selector
    logic [5:0]  alu_op;            // ALU operation
    logic [2:0]  b_sel;             // ALU B input selector
    logic        ext_int_inhibit;   // Disable external interrupts
    logic        ext_int_yield;     // Allow interrupt handling
    logic [3:0]  immediate;         // Immediate value index (LUT)
    logic        io;                // I/O operation flag
    logic [3:0]  jump_type;         // Conditional jump type
    logic        load_ip;           // Load instruction pointer
    logic        mar_wr_sel;        // Memory address register write select
    logic        mar_write;         // MAR write enable
    logic        mdr_write;         // Memory data register write enable
    logic        mem_read;          // Memory read request
    logic        mem_write;         // Memory write request
    logic        next_instruction;  // Fetch next x86 instruction
    logic        ra_modrm_rm_reg;   // Use ModR/M for register select
    logic [2:0]  ra_sel;            // Register A selector
    logic        rb_cl;             // Register B = CL (for shifts)
    logic [2:0]  rd_sel;            // Destination register selector
    logic [1:0]  rd_sel_source;     // Destination source
    logic [1:0]  reg_wr_source;     // Register write data source
    logic [1:0]  segment;           // Segment register selector
    logic        segment_force;     // Override segment
    logic        segment_wr_en;     // Segment write enable
    logic        tmp_wr_en;         // Temporary register write enable
    logic        tmp_wr_sel;        // Temporary write select
    logic        fpu_ctrl_wr;       // FPU control word write
    logic [3:0]  update_flags;      // CPU flags update pattern index
    logic [1:0]  width;             // Operand width (byte/word)
} microcode_instruction;  // Total: 66 bits
```

### Current ROM Access Pattern

```systemverilog
// Line 146: ROM declaration
(* ram_init_file = "microcode.mif" *) microcode_instruction mem[num_instructions];

// Line 383: ROM read (sequential)
always @(posedge clk)
    current <= mem[next_addr];
```

**Read-Only:** No write logic exists in current implementation.

---

## Proposed Architecture

### Design Pattern (Same as BIOS Upload)

```
MiSTer OSD Menu (User selects .UCode file)
    ↓
hps_io module (ARM ↔ FPGA communication)
    ↓ (ioctl_download, ioctl_wr, ioctl_addr, ioctl_dout)
MicrocodeUploadController (State machine)
    ↓ (microcode_wr_req, microcode_addr, microcode_data)
Microcode.sv Module (Modified to accept uploads)
    ↓
CPU executes custom microcode (transparent)
```

### Key Features

1. **✅ Upload via OSD**: New menu entry "P1 → Upload Microcode:"
2. **✅ Write Protection**: Automatic after upload completion
3. **✅ Re-upload Support**: Can upload new microcode without reset
4. **✅ Size Validation**: Must be exactly 1,196 microinstructions (99,336 bytes)
5. **✅ Default Microcode**: Power-on loads default from `microcode.mif`
6. **✅ No SDRAM Usage**: Uses on-chip M10K RAM blocks

---

## Implementation Steps

### **Phase 1: Microcode Module Modification** ⏱️ ~1 hour

**File:** `Quartus/rtl/CPU/Microcode.sv`

**Changes Required:**

1. **Add Upload Interface:**
```systemverilog
module Microcode(
    input logic clk,
    input logic reset,
    // ... existing signals ...

    // Upload interface (NEW)
    input logic                      upload_wr_req,
    input logic [addr_bits-1:0]      upload_addr,      // 11-bit address
    input logic [65:0]               upload_data,      // 66-bit microinstruction
    input microcode_instruction      upload_data_struct // Alternative: struct input
);
```

2. **Enable Write to ROM:**
```systemverilog
// Current (line 383):
always @(posedge clk)
    current <= mem[next_addr];

// Modified:
always @(posedge clk) begin
    if (upload_wr_req)
        mem[upload_addr] <= upload_data_struct;  // Write during upload
    else
        current <= mem[next_addr];                // Normal read
end
```

3. **Critical Consideration:**
   - Uploading microcode while CPU is running is dangerous!
   - **Solution:** Assert CPU reset during upload, release after completion
   - Or: Add upload_mode signal that halts microcode sequencer

---

### **Phase 2: MicrocodeUploadController Module** ⏱️ ~4 hours

**New File:** `Quartus/rtl/CPU/MicrocodeUploadController.sv`

**Functionality:**
- Monitors `ioctl_download` with index `0xC3` (microcode upload)
- Receives 66-bit data from `ioctl_dout` (requires special handling for wide data)
- Streams microinstructions to Microcode ROM
- Validates upload size (must be 1,196 instructions)
- Asserts CPU reset during upload, releases after completion

**Data Width Challenge:**
- `ioctl_dout` is 16 bits wide (WIDE=1 mode)
- Microcode is 66 bits wide
- **Solution:** Accumulate 5 words (16×5 = 80 bits, use lower 66 bits)

**State Machine:**
```
IDLE → RESET_CPU → UPLOADING → VALIDATING → RELEASE_CPU → PROTECTED
  ↑                                                            ↓
  └──────────────(new upload requested)──────────────────────┘
```

**Pseudo-code:**
```systemverilog
module MicrocodeUploadController(
    input  logic        clk,
    input  logic        reset,

    // IOCTL interface
    input  logic        ioctl_download,
    input  logic [15:0] ioctl_index,
    input  logic        ioctl_wr,
    input  logic [26:0] ioctl_addr,
    input  logic [15:0] ioctl_dout,

    // Microcode ROM write interface
    output logic                    microcode_wr_req,
    output logic [10:0]             microcode_addr,
    output microcode_instruction    microcode_data,

    // CPU control
    output logic        cpu_reset_req,  // Hold CPU in reset during upload

    // Status
    output logic        upload_active,
    output logic        upload_complete,
    output logic [10:0] upload_instruction_count
);

localparam MICROCODE_UPLOAD_INDEX = 16'hC3;
localparam NUM_MICROINSTRUCTIONS = 11'd1196;
localparam WORDS_PER_INSTRUCTION = 3'd5;  // 66 bits / 16 bits = 5 words (rounded)

typedef enum logic [2:0] {
    IDLE,
    RESET_CPU,
    UPLOADING,
    VALIDATING,
    RELEASE_CPU,
    PROTECTED
} state_t;

state_t state;
logic [2:0] word_count;          // Count words within current instruction (0-4)
logic [79:0] instruction_buffer; // Accumulate 5×16-bit words
logic [10:0] instruction_count;  // Count completed instructions

always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        state <= IDLE;
        cpu_reset_req <= 1'b0;
    end else begin
        case (state)
            IDLE: begin
                if (ioctl_download && ioctl_index == MICROCODE_UPLOAD_INDEX) begin
                    state <= RESET_CPU;
                    cpu_reset_req <= 1'b1;  // Hold CPU in reset
                end
            end

            RESET_CPU: begin
                // Wait a few cycles for CPU reset to propagate
                state <= UPLOADING;
                word_count <= 3'd0;
                instruction_count <= 11'd0;
            end

            UPLOADING: begin
                if (ioctl_wr) begin
                    // Accumulate 16-bit words
                    instruction_buffer <= {instruction_buffer[63:0], ioctl_dout};
                    word_count <= word_count + 3'd1;

                    // After 5 words, write complete instruction
                    if (word_count == WORDS_PER_INSTRUCTION - 1) begin
                        microcode_wr_req <= 1'b1;
                        microcode_addr <= instruction_count;
                        microcode_data <= instruction_buffer[65:0];  // Lower 66 bits
                        instruction_count <= instruction_count + 11'd1;
                        word_count <= 3'd0;
                    end
                end

                if (!ioctl_download) begin
                    state <= VALIDATING;
                    microcode_wr_req <= 1'b0;
                end
            end

            VALIDATING: begin
                if (instruction_count == NUM_MICROINSTRUCTIONS) begin
                    upload_complete <= 1'b1;
                    state <= RELEASE_CPU;
                end else begin
                    // Invalid size - reject upload
                    upload_complete <= 1'b0;
                    state <= RELEASE_CPU;  // Release CPU anyway
                end
            end

            RELEASE_CPU: begin
                cpu_reset_req <= 1'b0;  // Release CPU reset
                state <= PROTECTED;
            end

            PROTECTED: begin
                // No writes allowed, wait for new upload
                if (ioctl_download && ioctl_index == MICROCODE_UPLOAD_INDEX) begin
                    state <= IDLE;
                end
            end
        endcase
    end
end
endmodule
```

---

### **Phase 3: OSD Menu Update** ⏱️ ~15 minutes

**File:** `Quartus/mycore.sv` (CONF_STR)

**Add Menu Entry:**
```verilog
"P1,System & BIOS;",
"P1O3,Model,IBM PCXT,Tandy 1000;",
"P1FC0,ROM,PCXT BIOS:;",
"P1FC1,ROM,Tandy BIOS:;",
"P1FC2,ROM,EC00 BIOS:;",
"P1-;",
"P1FC3,UCODE,Upload Microcode (Advanced):;",  // NEW - index 0xC3
"P1-;",
```

**Warning Label (Optional):**
```verilog
"P1FC3,UCODE,⚠ Microcode (requires reset):;",  // With warning symbol
```

---

### **Phase 4: System Integration** ⏱️ ~2 hours

**File:** `Quartus/mycore.sv`

**Signal Declarations:**
```systemverilog
// Microcode upload signals
wire        microcode_upload_wr_req;
wire [10:0] microcode_upload_addr;
microcode_instruction microcode_upload_data;
wire        microcode_upload_cpu_reset;
wire        microcode_upload_active;
wire        microcode_upload_complete;
```

**Instantiate Controller:**
```systemverilog
MicrocodeUploadController microcode_uploader(
    .clk(sys_clk),
    .reset(xreset),

    // IOCTL interface from hps_io
    .ioctl_download(ioctl_download),
    .ioctl_index(ioctl_index),
    .ioctl_wr(ioctl_wr),
    .ioctl_addr(ioctl_addr),
    .ioctl_dout(ioctl_dout),

    // Microcode ROM write interface
    .microcode_wr_req(microcode_upload_wr_req),
    .microcode_addr(microcode_upload_addr),
    .microcode_data(microcode_upload_data),

    // CPU control
    .cpu_reset_req(microcode_upload_cpu_reset),

    // Status
    .upload_active(microcode_upload_active),
    .upload_complete(microcode_upload_complete),
    .upload_instruction_count()
);
```

**Modify CPU Reset Logic:**
```systemverilog
// Current:
wire cpu_reset = xreset | debug_reset | ...;

// Modified:
wire cpu_reset = xreset | debug_reset | microcode_upload_cpu_reset | ...;
```

**Pass Upload Signals to Core/Microcode:**
```systemverilog
Core u80186(
    .clk(sys_clk),
    .reset(cpu_reset),  // Now includes microcode upload reset

    // ... existing signals ...

    // Microcode upload interface (pass-through to Microcode module)
    .microcode_upload_wr_req(microcode_upload_wr_req),
    .microcode_upload_addr(microcode_upload_addr),
    .microcode_upload_data(microcode_upload_data)
);
```

**Modify Core.sv** (pass-through to Microcode):
```systemverilog
// In Core.sv instantiation of Microcode module:
Microcode Microcode(
    // ... existing signals ...

    .upload_wr_req(microcode_upload_wr_req),
    .upload_addr(microcode_upload_addr),
    .upload_data_struct(microcode_upload_data)
);
```

---

### **Phase 5: Testing - Unit Tests** ⏱️ ~4 hours

**File:** `modelsim/microcode_upload_controller_tb.sv`

**Test Scenarios:**

1. **Test 1: Valid Full Microcode Upload (1,196 instructions)**
   - Upload 1,196 × 66-bit instructions (5,980 × 16-bit words)
   - Verify `upload_complete = 1`
   - Verify `instruction_count = 1196`

2. **Test 2: Partial Upload (500 instructions)**
   - Upload only 500 instructions
   - Verify rejection (size mismatch)
   - Verify `upload_complete = 0`

3. **Test 3: Re-upload Capability**
   - Upload full microcode
   - Upload different microcode
   - Verify second upload succeeds

4. **Test 4: CPU Reset Assertion**
   - Monitor `cpu_reset_req` during upload
   - Verify asserted during UPLOADING state
   - Verify released after completion

5. **Test 5: Word Accumulation Logic**
   - Send 5 × 16-bit words
   - Verify 66-bit instruction assembled correctly
   - Check endianness and bit alignment

6. **Test 6: Write Request Generation**
   - Verify `microcode_wr_req` asserted every 5 words
   - Verify correct address incrementing

**Test Structure:**
```systemverilog
module microcode_upload_controller_tb;
    // DUT signals
    logic        clk, reset;
    logic        ioctl_download;
    logic [15:0] ioctl_index;
    logic        ioctl_wr;
    logic [26:0] ioctl_addr;
    logic [15:0] ioctl_dout;
    logic        microcode_wr_req;
    logic [10:0] microcode_addr;
    microcode_instruction microcode_data;
    logic        cpu_reset_req;

    // DUT instantiation
    MicrocodeUploadController dut(...);

    // Test tasks
    task upload_microcode_file(input int num_instructions);
        ioctl_index = 16'hC3;
        ioctl_download = 1;

        for (int i = 0; i < num_instructions; i++) begin
            for (int word = 0; word < 5; word++) begin
                ioctl_addr = (i * 10) + (word * 2);  // Byte address
                ioctl_dout = generate_test_word(i, word);
                ioctl_wr = 1;
                @(posedge clk);
                ioctl_wr = 0;
                @(posedge clk);
            end
        end

        ioctl_download = 0;
        repeat(10) @(posedge clk);
    endtask

    function logic [15:0] generate_test_word(int instr, int word);
        // Generate test pattern for word N of instruction M
        return 16'hA000 + {instr[7:0], word[2:0], 5'b0};
    endfunction

    // ... test procedures ...
endmodule
```

---

### **Phase 6: Testing - Integration Tests** ⏱️ ~5 hours

**File:** `modelsim/microcode_upload_integration_tb.sv`

**Integration Test Structure:**
```
hps_io (simulated) → MicrocodeUploadController → Microcode.sv → CPU reads microcode
```

**Test Scenarios:**

1. **Test 1: Upload and Execute Simple Microcode**
   - Upload microcode with known pattern (e.g., NOP sequence)
   - Reset CPU
   - Verify CPU fetches from uploaded microcode
   - Monitor microcode address sequencing

2. **Test 2: Upload Complete Microcode Set**
   - Upload all 1,196 instructions
   - Read back via CPU microcode fetches
   - Verify each instruction matches uploaded data

3. **Test 3: CPU Reset During Upload**
   - Start upload
   - Verify CPU halted (`cpu_reset_req = 1`)
   - Complete upload
   - Verify CPU released and executing

4. **Test 4: Instruction Sequencing After Upload**
   - Upload microcode with specific jump pattern
   - Execute CPU for several instructions
   - Verify correct microcode address progression

**Challenges:**
- Need to instantiate full `Microcode.sv` module
- Need to provide all microcode input signals (rm_is_reg, modrm_reg, flags, etc.)
- May need stub CPU to generate realistic control signals

**Simplified Integration Test:**
```systemverilog
module microcode_upload_integration_tb;
    // System signals
    logic clk, reset;

    // IOCTL signals
    logic        ioctl_download;
    logic [15:0] ioctl_index;
    logic        ioctl_wr;
    logic [26:0] ioctl_addr;
    logic [15:0] ioctl_dout;

    // Upload controller outputs
    logic                    microcode_wr_req;
    logic [10:0]             microcode_addr;
    microcode_instruction    microcode_data;
    logic                    cpu_reset_req;

    // Microcode module signals (stubs)
    logic        stall = 0;
    logic        nmi_pulse = 0;
    logic        intr = 0;
    // ... other signals stubbed ...

    // Upload controller
    MicrocodeUploadController uploader(...);

    // Microcode module
    Microcode microcode_module(
        .clk(clk),
        .reset(reset | cpu_reset_req),
        .stall(stall),
        // ... stub inputs ...
        .upload_wr_req(microcode_wr_req),
        .upload_addr(microcode_addr),
        .upload_data_struct(microcode_data)
    );

    // Test: Upload and verify read-back
    initial begin
        // Upload test microcode
        upload_test_microcode(100);  // 100 instructions

        // Release CPU reset
        wait(cpu_reset_req == 0);

        // Monitor microcode execution for several cycles
        repeat(20) @(posedge clk);

        // Verify microcode addresses accessed
        // (requires internal signal probing or debug outputs)
    end
endmodule
```

---

### **Phase 7: Microcode File Format** ⏱️ ~2 hours

**Create Microcode Binary Format Specification**

**Option A: Binary Format (66 bits per instruction)**
```
File: custom_microcode.ucode
Size: 99,336 bytes (1,196 instructions × 66 bits = 98,736 bits = 12,342 bytes)
      Actually: 1,196 × 10 bytes = 11,960 bytes (66 bits + padding to 80 bits)

Format:
[Instruction 0]: 80 bits (66 bits microcode + 14 bits padding)
[Instruction 1]: 80 bits
...
[Instruction 1195]: 80 bits
```

**Option B: Hex Format (Compatible with MIF)**
```
File: custom_microcode.hex
Format: ASCII hex, one instruction per line

Example:
04A_3_05_2_0_0_1_3_0_0_0_1_0_0_0_0_1_5_0_3_0_0_0_0_0_0_0_0_2_0
^   ^ ^  ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^ ^
|   | |  | | | | | | | | | | | | | | | | | | | | | | | | | | └─ width[1:0]
|   | |  | ...
|   | |  └─ alu_op[5:0]
|   | └─ a_sel[1:0]
|   └─ next[10:0]
```

**Conversion Tool:**
Create `utils/microassembler/ucode2bin.py`:
```python
#!/usr/bin/env python3
# Convert .us microcode source to uploadable binary format

import sys
from microassembler import assemble_microcode

def convert_microcode_to_binary(source_files, output_file):
    """Assemble microcode and output binary format for upload"""

    # Assemble microcode (reuse existing assembler)
    microcode = assemble_microcode(source_files)

    # Write binary format (80 bits per instruction, little-endian)
    with open(output_file, 'wb') as f:
        for instruction in microcode:
            # Pack 66-bit instruction into 80 bits (10 bytes)
            data = instruction.to_bytes(10, byteorder='little')
            f.write(data)

    print(f"Wrote {len(microcode)} instructions to {output_file}")

if __name__ == '__main__':
    sources = sys.argv[1:-1]
    output = sys.argv[-1]
    convert_microcode_to_binary(sources, output)
```

**Usage:**
```bash
cd utils/microassembler/
python ucode2bin.py microcode/*.us custom_microcode.ucode
```

---

### **Phase 8: Documentation** ⏱️ ~2 hours

**Create:** `docs/MICROCODE_UPLOAD_IMPLEMENTATION.md`

**Contents:**
- Architecture overview
- Upload procedure
- File format specification
- Safety warnings (uploading bad microcode can brick CPU until reset)
- Examples of custom microcode (e.g., new instruction implementation)
- Debugging techniques

---

## Resource Impact Estimate

### FPGA Utilization

| Resource | Before | Addition | New Total | % Change |
|----------|--------|----------|-----------|----------|
| ALMs | ~78% | ~400 | ~78.5% | +0.5% |
| M10K Blocks | 89 | 0 | 89 | 0% (reuses microcode RAM) |
| Registers | ~40,150 | ~250 | ~40,400 | +0.6% |
| Logic | | ~300 LUTs | | |

**Impact:** Minimal - slightly larger than BIOS upload due to wider data path.

---

## Timeline Estimate

| Phase | Duration | Complexity |
|-------|----------|------------|
| Phase 1: Microcode.sv Modification | 1 hour | Low |
| Phase 2: Upload Controller | 4 hours | Medium-High |
| Phase 3: OSD Menu | 15 min | Low |
| Phase 4: System Integration | 2 hours | Medium |
| Phase 5: Unit Testing | 4 hours | Medium |
| Phase 6: Integration Testing | 5 hours | High |
| Phase 7: File Format Tools | 2 hours | Medium |
| Phase 8: Documentation | 2 hours | Low |
| **Total** | **~21 hours** | **Medium-High** |

---

## Risks and Mitigations

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| **Bad microcode hangs CPU** | High | High | Require reset after upload; watchdog timer |
| **66-bit data path complexity** | Medium | Medium | Use 80-bit alignment (5×16 bits) |
| **Instruction count mismatch** | Medium | Medium | Strict validation (must be 1,196) |
| **Upload during CPU execution** | Medium | High | Force CPU reset during upload |
| **ROM timing issues** | Low | High | Ensure write/read don't conflict |

---

## Testing Strategy

### Unit Test Checklist
- [ ] Valid full upload (1,196 instructions)
- [ ] Invalid size rejection
- [ ] Re-upload capability
- [ ] CPU reset control
- [ ] Word accumulation (5×16→66 bits)
- [ ] Write request generation
- [ ] Address sequencing
- [ ] State machine transitions

### Integration Test Checklist
- [ ] Upload → read-back verification
- [ ] CPU execution after upload
- [ ] Reset timing verification
- [ ] Microcode address sequencing
- [ ] Control signal propagation

### Hardware Validation Checklist
- [ ] Upload default microcode (should work identically)
- [ ] Upload modified microcode (e.g., NOP all instructions)
- [ ] Verify CPU behavior changes
- [ ] Test reset to restore default
- [ ] Performance measurement

---

## Safety Considerations

### **⚠️ CRITICAL WARNINGS FOR USERS**

1. **Uploading bad microcode can hang or crash the CPU**
   - System will become unresponsive
   - Requires FPGA reprogram or power cycle to recover

2. **No validation of microcode correctness**
   - System cannot detect invalid microinstruction sequences
   - Testing in simulation strongly recommended

3. **Always keep backup of default microcode.mif**
   - Default microcode restored only on FPGA reprogram
   - No "undo" after upload

4. **CPU reset required after upload**
   - Automatic reset during upload
   - May cause data loss if CPU was mid-operation

### **Recommended Workflow**

1. **Develop microcode in simulator first**
   - Test with Verilator or Icarus Verilog
   - Verify instruction sequences
   - Check for infinite loops

2. **Test incremental changes**
   - Modify only a few instructions at a time
   - Compare behavior to default microcode

3. **Keep default microcode accessible**
   - Store copy of `microcode.mif` on SD card
   - Can re-upload if custom microcode fails

---

## Future Enhancements

1. **Microcode Disassembler** (Difficulty: Medium)
   - Read current microcode from ROM
   - Display in human-readable format
   - Compare uploaded vs default

2. **Partial Microcode Update** (Difficulty: High)
   - Upload only specific instruction ranges
   - Preserve default microcode for unmodified instructions
   - Requires read-modify-write capability

3. **Microcode Checksum Verification** (Difficulty: Low)
   - Calculate CRC32 of uploaded microcode
   - Verify against known-good checksum

4. **Microcode Debugging Interface** (Difficulty: Very High)
   - Single-step through microcode execution
   - Breakpoints at specific microcode addresses
   - Inspect microcode fields in real-time

5. **Multiple Microcode Storage** (Difficulty: Medium)
   - Store multiple microcode sets in SDRAM
   - OSD selection to choose active set
   - Requires 150 KB SDRAM (1,196 × 66 bits × 16 sets)

---

## Alternative Approach: Hybrid System

**Idea:** Combine default ROM with writable RAM overlay

```systemverilog
// Default ROM (read-only, synthesis initialized)
microcode_instruction rom[num_instructions];

// Writable RAM overlay (initially empty)
microcode_instruction ram[num_instructions];

// Overlay enable bits (1 bit per instruction)
logic overlay_enable[num_instructions];

// Fetch logic:
always @(posedge clk) begin
    if (upload_wr_req) begin
        ram[upload_addr] <= upload_data_struct;
        overlay_enable[upload_addr] <= 1'b1;
    end else begin
        current <= overlay_enable[next_addr] ? ram[next_addr]
                                              : rom[next_addr];
    end
end
```

**Benefits:**
- Preserves default microcode always
- Can selectively override specific instructions
- Easy to "undo" (clear overlay_enable bits)

**Drawbacks:**
- Doubles RAM usage (2× 1,196 × 66 bits)
- More complex logic

---

## Questions to Resolve

1. **File Format:** Binary or hex-text?
   - **Recommendation:** Binary (smaller, faster upload)

2. **Endianness:** Little-endian or big-endian?
   - **Recommendation:** Little-endian (matches x86)

3. **OSD Warning:** Show warning about danger?
   - **Recommendation:** Yes - "⚠ Advanced: Can hang CPU"

4. **CPU Reset:** Automatic or manual?
   - **Recommendation:** Automatic (safer)

5. **Validation:** Strict (1,196 only) or flexible?
   - **Recommendation:** Strict (microcode address space is fixed)

---

## Summary

This plan provides a **comprehensive roadmap** for implementing CPU microcode upload functionality, based on the successful BIOS upload implementation. Key differences:

- **Wider data path:** 66 bits vs 16 bits
- **More complex validation:** Exact instruction count required
- **CPU reset required:** Safety measure to prevent corruption
- **Higher risk:** Bad microcode can hang CPU

**Estimated effort:** ~21 hours (vs 4 hours for BIOS upload)

**Complexity:** Medium-High (data width accumulation, CPU reset control)

**Priority:** Medium (advanced feature, not critical for basic operation)

---

**End of Plan**

# FPU8087 Module Interfaces - Testbench Reference Guide

## Executive Summary
This document provides detailed interface specifications for four critical FPU8087 modules needed for testbench development:
1. **FPU_CORDIC_Wrapper.v** - CORDIC algorithm for trigonometric functions (sin/cos/tan/atan)
2. **FPU_Transcendental.v** - Unified interface for transcendental operations
3. **FPU_Core.v** - Main FPU execution engine (137K lines)
4. **MicroSequencer_Extended_BCD.v** - Microcode engine for complex operations (47K lines)

---

## 1. FPU_CORDIC_Wrapper.v

### Module Declaration
```verilog
module FPU_CORDIC_Wrapper(
    input wire clk,
    input wire reset,
    input wire enable,
    input wire [1:0] mode,           // 00=rotation (sin/cos), 01=vectoring (atan), 10=tan
    
    // FP80 Input/Output
    input wire [79:0] angle_in,      // For rotation and tan modes
    input wire [79:0] x_in,          // For vectoring mode
    input wire [79:0] y_in,          // For vectoring mode
    
    output reg [79:0] sin_out,       // Rotation mode: sin result
    output reg [79:0] cos_out,       // Rotation mode: cos result
    output reg [79:0] atan_out,      // Vectoring mode: atan result
    output reg [79:0] magnitude_out, // Vectoring mode: magnitude result
    output reg [79:0] tan_out,       // Tan mode: tan result
    
    output reg done,
    output reg error,
    
    // External Arithmetic Unit Interface
    output reg        ext_addsub_req,      // AddSub request
    output reg [79:0] ext_addsub_a,        // Operand A
    output reg [79:0] ext_addsub_b,        // Operand B
    output reg        ext_addsub_sub,      // 0=add, 1=subtract
    input wire [79:0] ext_addsub_result,   // AddSub result
    input wire        ext_addsub_done,     // AddSub complete
    input wire        ext_addsub_invalid,  // AddSub exception
    
    output reg        ext_muldiv_req,      // MulDiv request
    output reg        ext_muldiv_op,       // 0=multiply, 1=divide
    output reg [79:0] ext_muldiv_a,        // Operand A
    output reg [79:0] ext_muldiv_b,        // Operand B
    input wire [79:0] ext_muldiv_result,   // MulDiv result
    input wire        ext_muldiv_done,     // MulDiv complete
    input wire        ext_muldiv_invalid   // MulDiv exception
);
```

### Key State Machine States
```verilog
STATE_IDLE           = 5'd0   // Waiting for enable
STATE_RANGE_REDUCE   = 5'd1   // Range reduction phase
STATE_CONVERT_INPUT  = 5'd2   // FP80 → Q2.62 fixed-point
STATE_CORDIC_INIT    = 5'd3   // Initialize iteration counter
STATE_CORDIC_ITER    = 5'd4   // Execute CORDIC iterations
STATE_CONVERT_OUTPUT = 5'd5   // Q2.62 fixed-point → FP80
STATE_QUAD_CORRECT   = 5'd6   // Apply quadrant corrections
STATE_DONE           = 5'd7   // Operation complete
STATE_CORR_*         = 5'd8-19 // Correction states for TAN/ATAN
```

### Key Parameters & Constants
| Parameter | Value | Purpose |
|-----------|-------|---------|
| `NUM_ITERATIONS_SINCOS` | 50 | Iterations for sin/cos (64-bit accuracy) |
| `NUM_ITERATIONS_TANATAN` | 16 | Iterations for tan/atan + polynomial correction |
| `FP80_CORDIC_SCALE` | 0x3FFE_9B74EDA81F6EB000 | 1/K for 50-iteration pre-scaling |
| `FP80_CORDIC_SCALE_16` | 0x3FFE_D413CCCFE779921B | 1/K16 for 16-iteration pre-scaling |
| `FP80_ZERO` | 0x0000_0000000000000000 | Zero constant |
| `FP80_ONE` | 0x3FFF_8000000000000000 | One constant |

### Control Signals Summary
- **enable**: Start operation
- **mode**: 00=rotation (sin/cos), 01=vectoring (atan), 10=tan
- **done**: Operation complete (1 cycle pulse)
- **error**: Exception occurred
- **ext_addsub_req/ext_muldiv_req**: Request signals (must be held until _done asserts)

### Internal Data Format
- **Working registers (64-bit signed)**:
  - `x_cordic`, `y_cordic`, `z_cordic` - Q2.62 fixed-point format
  - Range: [-2, +2) with resolution 2^-62

### Dependencies
- **FPU_Range_Reduction** - Reduces input angle to [-π/4, π/4]
- **FPU_Atan_Table** - Arctangent values for each iteration (combinational ROM)
- **External AddSub/MulDiv units** - Shared arithmetic (cannot be instantiated locally)

### Testbench Considerations
- **Input range**: ±∞ (FP80 format)
- **Known values to test**: 0, π/6, π/4, π/3, π/2, and their negatives
- **Accuracy**: Should satisfy sin²(θ) + cos²(θ) = 1
- **Latency**: ~55 cycles (50 iterations + overhead)
- **Requires**: External AddSub and MulDiv units running at same clock

---

## 2. FPU_Transcendental.v

### Module Declaration
```verilog
module FPU_Transcendental(
    input wire clk,
    input wire reset,
    input wire [3:0] operation,      // Operation selector (see codes below)
    input wire enable,               // Start operation
    
    // Operands (80-bit FP)
    input wire [79:0] operand_a,     // Primary operand
    input wire [79:0] operand_b,     // Secondary operand
    
    // Results (80-bit FP)
    output reg [79:0] result_primary,
    output reg [79:0] result_secondary,
    output reg        has_secondary, // 1 if secondary result valid (FSINCOS/FPTAN)
    
    output reg done,
    output reg error,
    
    // External Arithmetic Unit Interface (pass-through to shared units)
    output reg        ext_addsub_req,      // AddSub request
    output reg [79:0] ext_addsub_a,
    output reg [79:0] ext_addsub_b,
    output reg        ext_addsub_sub,
    input wire [79:0] ext_addsub_result,
    input wire        ext_addsub_done,
    input wire        ext_addsub_invalid,
    input wire        ext_addsub_overflow,
    input wire        ext_addsub_underflow,
    input wire        ext_addsub_inexact,
    
    output reg        ext_muldiv_req,
    output reg        ext_muldiv_op,       // 0=mul, 1=div
    output reg [79:0] ext_muldiv_a,
    output reg [79:0] ext_muldiv_b,
    input wire [79:0] ext_muldiv_result,
    input wire        ext_muldiv_done,
    input wire        ext_muldiv_invalid,
    input wire        ext_muldiv_div_by_zero,
    input wire        ext_muldiv_overflow,
    input wire        ext_muldiv_underflow,
    input wire        ext_muldiv_inexact,
    
    // Polynomial evaluator interface (for FYL2X, F2XM1, FYL2XP1)
    output wire        ext_poly_addsub_req,
    output wire [79:0] ext_poly_addsub_a,
    output wire [79:0] ext_poly_addsub_b,
    input wire [79:0]  ext_poly_addsub_result,
    input wire         ext_poly_addsub_done,
    // ... (overflow/underflow/inexact flags)
    
    output wire        ext_poly_muldiv_req,
    output wire [79:0] ext_poly_muldiv_a,
    output wire [79:0] ext_poly_muldiv_b,
    input wire [79:0]  ext_poly_muldiv_result,
    input wire         ext_poly_muldiv_done
    // ... (exception flags)
);
```

### Operation Codes (4-bit selector)
```verilog
OP_SQRT    = 4'd0   // Square root (MICROCODE ONLY - returns NaN)
OP_SIN     = 4'd1   // Sine via CORDIC rotation (50 iterations)
OP_COS     = 4'd2   // Cosine via CORDIC rotation (50 iterations)
OP_SINCOS  = 4'd3   // Both sin/cos (CORDIC, returns secondary)
OP_TAN     = 4'd4   // Tangent via CORDIC (16 iterations + correction)
OP_ATAN    = 4'd5   // Arctangent via CORDIC vectoring (16 iterations + correction)
OP_F2XM1   = 4'd6   // 2^x - 1 via polynomial (130-150 cycles)
OP_FYL2X   = 4'd7   // y × log₂(x) polynomial + multiply (155-175 cycles)
OP_FYL2XP1 = 4'd8   // y × log₂(x+1) add + polynomial + multiply (165-185 cycles)
```

### Key State Machine States
```verilog
STATE_IDLE           = 4'd0  // Waiting for enable
STATE_ROUTE_OP       = 4'd1  // Decode operation and route to subunit
STATE_WAIT_CORDIC    = 4'd2  // Wait for CORDIC completion
STATE_WAIT_POLY      = 4'd3  // Wait for polynomial evaluator
STATE_WAIT_SQRT      = 4'd4  // Square root (immediate error)
STATE_POST_PROCESS   = 4'd5  // Reserved
STATE_WAIT_DIV       = 4'd6  // FPTAN division (unused after Plan 2)
STATE_WAIT_MUL       = 4'd7  // FYL2X, FYL2XP1 multiply
STATE_WAIT_ADD       = 4'd8  // FYL2XP1 pre-add (x+1)
STATE_DONE           = 4'd9  // Operation complete
```

### Internal Modules Instantiated
- **FPU_CORDIC_Wrapper** - For sin/cos/tan/atan operations
- **FPU_Polynomial_Evaluator** - For F2XM1, FYL2X, FYL2XP1
- **Arithmetic Arbiter** - Routes requests to shared AddSub/MulDiv units

### Arbiter Priority (combinational)
1. **Priority 1**: Local state machine requests (FPTAN division, FYL2X multiply, FYL2XP1 operations)
2. **Priority 2**: CORDIC requests (TAN/ATAN polynomial correction)
3. **Priority 3**: Polynomial evaluator requests

### Performance Estimates
| Operation | Cycles | Real 8087 |
|-----------|--------|-----------|
| FSIN      | 300-350 | 200-300 |
| FCOS      | 300-350 | 200-300 |
| FSINCOS   | 300-350 | 250-350 |
| FPTAN     | 360-410 | 200-250 |
| FPATAN    | 300-350 | 200-300 |
| F2XM1     | 130-150 | 200-300 |
| FYL2X     | 155-175 | 250-350 |
| FYL2XP1   | 165-185 | 250-350 |

### Important Notes
- **SQRT Hardware Removed**: Returns NaN to signal microcode-only implementation (address 0x0140)
- **TAN Implementation**: Direct CORDIC with 16 iterations + polynomial correction
- **ATAN Implementation**: CORDIC vectoring mode with 16 iterations + polynomial correction
- **Shared Units Required**: Cannot run independently; requires FPU_ArithmeticUnit providing AddSub/MulDiv

---

## 3. FPU_Core.v (Top-Level FPU, 137K lines)

### Module Declaration
```verilog
module FPU_Core(
    input wire clk,
    input wire reset,
    
    // Instruction interface
    input wire [7:0]  instruction,      // FPU instruction opcode
    input wire [2:0]  stack_index,      // Stack index for ST(i) operands
    input wire        execute,          // Start execution
    output reg        ready,            // FPU ready
    output reg        error,            // Exception occurred
    
    // Data interface
    input wire [79:0] data_in,          // Data input (for loads)
    output reg [79:0] data_out,         // Data output (for stores)
    input wire [31:0] int_data_in,      // Integer input
    output reg [31:0] int_data_out,     // Integer output
    
    // Memory operand format information
    input wire        has_memory_op,    // Instruction uses memory operand
    input wire [1:0]  operand_size,     // 0=word, 1=dword, 2=qword, 3=tbyte
    input wire        is_integer,       // Integer format flag
    input wire        is_bcd,           // BCD format flag
    
    // Control/Status interface
    input wire [15:0] control_in,       // Control word input
    input wire        control_write,    // Control word write enable
    output wire [15:0] status_out,      // Status word output
    output wire [15:0] control_out,     // Control word output
    output wire [15:0] tag_word_out,    // Tag word output
    
    // Exception interface
    output wire       int_request       // INT signal (active HIGH)
);
```

### Instruction Opcodes (8-bit)
```verilog
// Arithmetic
INST_FADD    = 8'h10    // ST(0) = ST(0) + ST(i)
INST_FADDP   = 8'h11    // ST(1) = ST(0) + ST(1), pop
INST_FSUB    = 8'h12    // ST(0) = ST(0) - ST(i)
INST_FSUBP   = 8'h13    // ST(1) = ST(0) - ST(1), pop
INST_FMUL    = 8'h14    // ST(0) = ST(0) * ST(i)
INST_FMULP   = 8'h15    // ST(1) = ST(0) * ST(1), pop
INST_FDIV    = 8'h16    // ST(0) = ST(0) / ST(i)
INST_FDIVP   = 8'h17    // ST(1) = ST(0) / ST(1), pop

// Stack operations
INST_FLD     = 8'h20    // Push ST(i) or memory value
INST_FST     = 8'h21    // Store ST(0) to ST(i) or memory
INST_FSTP    = 8'h22    // Store ST(0) and pop
INST_FXCH    = 8'h23    // Exchange ST(0) with ST(i)

// Integer conversions
INST_FILD16  = 8'h30    // Load 16-bit integer
INST_FILD32  = 8'h31    // Load 32-bit integer
INST_FIST16  = 8'h32    // Store 16-bit integer
INST_FIST32  = 8'h33    // Store 32-bit integer

// BCD operations
INST_FBLD    = 8'h36    // Load BCD (18 digits)
INST_FBSTP   = 8'h37    // Store BCD and pop

// FP format conversions
INST_FLD32   = 8'h40    // Load FP32 (convert to FP80)
INST_FLD64   = 8'h41    // Load FP64 (convert to FP80)
INST_FST32   = 8'h42    // Store as FP32
INST_FST64   = 8'h43    // Store as FP64

// Transcendental
INST_FSQRT   = 8'h50    // Square root
INST_FSIN    = 8'h51    // Sine
INST_FCOS    = 8'h52    // Cosine
INST_FSINCOS = 8'h53    // Sin & Cos
INST_FPTAN   = 8'h54    // Partial tangent
INST_FPATAN  = 8'h55    // Partial arctangent
INST_F2XM1   = 8'h56    // 2^x - 1
INST_FYL2X   = 8'h57    // y × log₂(x)
INST_FYL2XP1 = 8'h58    // y × log₂(x+1)

// Comparison
INST_FCOM    = 8'h60    // Compare ST(0) with ST(i)
INST_FCOMP   = 8'h61    // Compare and pop
INST_FTST    = 8'h63    // Test against 0.0
INST_FXAM    = 8'h64    // Examine ST(0)

// Control
INST_FINIT   = 8'hF0    // Initialize FPU
INST_FLDCW   = 8'hF1    // Load control word
INST_FSTCW   = 8'hF2    // Store control word
INST_FSTSW   = 8'hF3    // Store status word
INST_FCLEX   = 8'hF4    // Clear exceptions
INST_FWAIT   = 8'hF5    // Wait for ready
```

### Key Internal Components
| Component | Purpose |
|-----------|---------|
| `FPU_RegisterStack` | 8-register stack (ST(0)-ST(7)) |
| `FPU_ControlWord` | Rounding/precision/exception mask control |
| `FPU_StatusWord` | Status flags and exception indication |
| `FPU_ArithmeticUnit` | Arithmetic operations (5 operations) |
| `FPU_Exception_Handler` | Exception generation and INT request logic |
| `FPU_BCD_to_Binary` | BCD → 64-bit binary conversion |
| `FPU_Binary_to_BCD` | 64-bit binary → BCD conversion |
| `FPU_Payne_Hanek_ROM` | Extended precision range reduction ROM |
| `MicroSequencer_Extended_BCD` | Microcode engine for complex operations |

### Key Control Signals
```verilog
// Status word bits
status_out[15:14] = stack_pointer   // Stack top
status_out[13:11] = reserved
status_out[10:8]  = condition codes (C0-C3)
status_out[7]     = error_summary
status_out[6]     = stack_fault
status_out[5]     = precision_exception
status_out[4]     = underflow_exception
status_out[3]     = overflow_exception
status_out[2]     = zero_divide_exception
status_out[1]     = denormal_exception
status_out[0]     = invalid_exception

// Control word bits (16-bit)
control_out[15:13] = rounding_mode (00=nearest, 01=down, 10=up, 11=trunc)
control_out[12:11] = precision_control
control_out[10:6]  = exception masks (P,U,O,Z,D,I)
control_out[5:0]   = reserved/unused
```

### Microsequencer Integration
- **32 microcode programs** (indices 0-31) for complex operations
- Programs include: FADD, FSUB, FMUL, FDIV, FSQRT, FSIN, FCOS, FSINCOS, FPTAN, FPATAN, etc.
- **Execution flow**: CPU decodes ESC instruction → FPU_Core routes to microsequencer → returns result

### Exception Handling
- **Stack exceptions**: Stack overflow, stack underflow, stack fault
- **Operation exceptions**: Invalid, denormal, zero divide, overflow, underflow, precision
- **Masking**: All exceptions individually maskable via control word
- **INT generation**: Unmasked exception → INT_REQUEST signal pulses

### Status Word Management
- **Sticky bits**: Exceptions remain set until FCLEX/FNCLEX
- **Condition codes**: Set by compare/test instructions
- **Busy bit**: Indicates FPU executing

### Important Design Notes
1. **Stack-based**: No explicit register addresses; always work with ST(0)-ST(7)
2. **Tag word**: Tracks register status (valid, zero, special, empty)
3. **Rounding modes**: Affects all arithmetic and format conversions
4. **Exception masks**: If unmasked, INT asserts on exception
5. **Control word persistence**: Survives FINIT in no-wait modes

---

## 4. MicroSequencer_Extended_BCD.v (Microcode Engine, 47K lines)

### Module Declaration
```verilog
module MicroSequencer_Extended_BCD (
    input wire clk,
    input wire reset,
    
    // Control
    input wire        start,                // Start microprogram
    input wire [4:0]  micro_program_index,  // Program to run (0-31)
    output reg        instruction_complete, // Execution done
    
    // Data bus (for memory operations)
    input wire [79:0] data_in,
    output reg [79:0] data_out,
    
    // Debug registers (expose internals)
    output wire [79:0] debug_temp_result,
    output wire [79:0] debug_temp_fp_a,
    output wire [79:0] debug_temp_fp_b,
    output wire [79:0] debug_temp_fp_c,
    output wire [63:0] debug_temp_uint64,
    output wire        debug_temp_sign,
    
    // ===== Interfaces to FPU_Core Hardware Units =====
    
    // FPU_ArithmeticUnit interface
    output reg [4:0]  arith_operation,      // Operation code
    output reg        arith_enable,         // Start operation
    input wire [1:0]  arith_rounding_mode,  // From control word
    output reg [79:0] arith_operand_a,      // 80-bit FP
    output reg [79:0] arith_operand_b,      // 80-bit FP
    output reg signed [15:0] arith_int16_in,
    output reg signed [31:0] arith_int32_in,
    output reg [63:0] arith_uint64_in,      // For BCD conversion
    output reg        arith_uint64_sign_in, // Sign bit
    output reg [31:0] arith_fp32_in,
    output reg [63:0] arith_fp64_in,
    
    // Arithmetic results
    input wire [79:0] arith_result,
    input wire [79:0] arith_result_secondary, // For sincos/tan
    input wire signed [15:0] arith_int16_out,
    input wire signed [31:0] arith_int32_out,
    input wire [63:0] arith_uint64_out,     // From BCD conversion
    input wire        arith_uint64_sign_out,
    input wire [31:0] arith_fp32_out,
    input wire [63:0] arith_fp64_out,
    input wire        arith_done,           // Operation complete
    input wire        arith_invalid,        // Exception flags
    input wire        arith_overflow,
    input wire        arith_cc_less,        // Compare condition codes
    input wire        arith_cc_equal,
    input wire        arith_cc_greater,
    input wire        arith_cc_unordered,
    
    // BCD_to_Binary converter interface
    output reg        bcd2bin_enable,
    output reg [79:0] bcd2bin_bcd_in,
    input wire [63:0] bcd2bin_binary_out,
    input wire        bcd2bin_sign_out,
    input wire        bcd2bin_done,
    input wire        bcd2bin_error,
    
    // Binary_to_BCD converter interface
    output reg        bin2bcd_enable,
    output reg [63:0] bin2bcd_binary_in,
    output reg        bin2bcd_sign_in,
    input wire [79:0] bin2bcd_bcd_out,
    input wire        bin2bcd_done,
    input wire        bin2bcd_error,
    
    // Payne-Hanek ROM interface
    output reg [2:0]  ph_rom_addr,      // ROM address (0-4)
    input wire [79:0] ph_rom_data       // ROM data
);
```

### FSM States
```verilog
STATE_IDLE   = 3'd0  // Waiting for start
STATE_FETCH  = 3'd1  // Fetch instruction from ROM
STATE_DECODE = 3'd2  // Decode instruction fields
STATE_EXEC   = 3'd3  // Execute instruction
STATE_WAIT   = 3'd4  // Wait for hardware completion
```

### Microinstruction Format (32-bit)
```verilog
[31:28] = opcode        // 4 bits (0=NOP, 1=EXEC, 2=JUMP, 3=CALL, 4=RET, F=HALT)
[27:23] = micro_op      // 5 bits (operation code)
[22:15] = immediate     // 8 bits
[14:0]  = next_addr     // 15 bits (for jumps/calls)
```

### Opcode Types (4-bit)
```verilog
OPCODE_NOP   = 4'h0   // No operation
OPCODE_EXEC  = 4'h1   // Execute micro-operation
OPCODE_JUMP  = 4'h2   // Unconditional jump
OPCODE_CALL  = 4'h3   // Call subroutine
OPCODE_RET   = 4'h4   // Return from subroutine
OPCODE_HALT  = 4'hF   // Halt execution
```

### Micro-Operations (5-bit MOP codes)
```verilog
// Data movement operations (0x01-0x0F)
MOP_LOAD           = 5'h01  // Load from data_in
MOP_STORE          = 5'h02  // Store to data_out
MOP_MOVE_TEMP      = 5'h03  // Move between temp registers
MOP_LOAD_IMM       = 5'h04  // Load immediate
MOP_LOAD_A         = 5'h05  // data_in → temp_fp_a
MOP_LOAD_B         = 5'h06  // data_in → temp_fp_b
MOP_MOVE_RES_TO_A  = 5'h07  // temp_result → temp_fp_a
MOP_MOVE_RES_TO_B  = 5'h08  // temp_result → temp_fp_b
MOP_MOVE_RES_TO_C  = 5'd19   // temp_result → temp_fp_c
MOP_MOVE_A_TO_C    = 5'h09   // temp_fp_a → temp_fp_c
MOP_MOVE_A_TO_B    = 5'h0A   // temp_fp_a → temp_fp_b
MOP_MOVE_C_TO_A    = 5'h0B   // temp_fp_c → temp_fp_a
MOP_MOVE_C_TO_B    = 5'h0C   // temp_fp_c → temp_fp_b
MOP_LOAD_HALF_B    = 5'h0D   // 0.5 → temp_fp_b

// Hardware unit operations (0x10-0x1F)
MOP_CALL_ARITH     = 5'h10   // Start arithmetic operation
MOP_WAIT_ARITH     = 5'h11   // Wait for arithmetic completion
MOP_LOAD_ARITH_RES = 5'h12   // Load result from arithmetic unit
MOP_LOAD_ARITH_RES_SEC = 5'd26 // Load secondary result (for SINCOS)

// BCD conversion operations (0x1A-0x1F)
MOP_CALL_BCD2BIN   = 5'h1A   // Start BCD → Binary
MOP_WAIT_BCD2BIN   = 5'h1B   // Wait for completion
MOP_LOAD_BCD2BIN   = 5'h1C   // Load result from BCD → Binary
MOP_CALL_BIN2BCD   = 5'h1D   // Start Binary → BCD
MOP_WAIT_BIN2BCD   = 5'h1E   // Wait for completion
MOP_LOAD_BIN2BCD   = 5'h1F   // Load result from Binary → BCD

// Extended precision operations (using remaining slots)
MOP_CLEAR_ACCUM    = 5'd20   // Clear 128-bit accumulator
MOP_LOAD_ROM       = 5'd21   // Load from Payne-Hanek ROM
MOP_EXTRACT_MANT   = 5'd22   // Extract 64-bit mantissa from FP80
MOP_EXTRACT_EXP    = 5'd23   // Extract 15-bit exponent
MOP_MUL64          = 5'd24   // 64×64 multiply → 128-bit result
MOP_ADD128         = 5'd25   // 128-bit addition with carry
MOP_PACK_FP80      = 5'd14   // Pack sign/exp/mant → FP80
MOP_LOAD_ROM_DATA  = 5'd15   // Load ROM data to temp_fp_b
```

### Arithmetic Operation Codes (used in immediate field)
```verilog
op=0   // FADD
op=1   // FSUB
op=2   // FMUL
op=3   // FDIV
op=4   // FSCALE
op=5   // FXTRACT
op=13  // FSIN
op=14  // FCOS
op=15  // FSINCOS
op=16  // FBLD
op=17  // FBSTP
// ... (see FPU_ArithmeticUnit documentation for full list)
```

### Internal Temporary Registers
```verilog
reg [79:0] temp_fp_a;       // Operand A (80-bit FP)
reg [79:0] temp_fp_b;       // Operand B (80-bit FP)
reg [79:0] temp_fp_c;       // Operand C / scratch (80-bit FP)
reg [79:0] temp_result;     // Operation result
reg [63:0] temp_uint64;     // For BCD intermediate (64-bit binary)
reg        temp_sign;       // Sign bit for BCD
reg [63:0] accum_hi;        // Upper 64-bit of 128-bit accumulator (Payne-Hanek)
reg [63:0] accum_lo;        // Lower 64-bit of 128-bit accumulator (Payne-Hanek)
reg [63:0] temp_64bit;      // Temporary 64-bit register
reg [2:0]  rom_addr_reg;    // Payne-Hanek ROM address
reg        carry_bit;       // Carry flag
```

### Program Table (32 Programs)
```verilog
Program 0   (0x0100) → FADD  Addition subroutine
Program 1   (0x0110) → FSUB  Subtraction subroutine
Program 2   (0x0120) → FMUL  Multiplication subroutine
Program 3   (0x0130) → FDIV  Division subroutine
Program 4   (0x0140) → FSQRT Square root (Newton-Raphson, 2 iterations)
Program 5   (0x01C0) → FSIN  Sine via CORDIC
Program 6   (0x01D0) → FCOS  Cosine via CORDIC
Program 7   (0x0200) → FLD   Load with format conversion
Program 8   (0x0210) → FST   Store with format conversion
Program 9   (0x0300) → FPREM Partial remainder
Program 10  (0x0400) → FXTRACT Extract exponent/significand
Program 11  (0x0500) → FSCALE Scale by power of 2
Program 12  (0x0600) → FBLD  Load BCD (BCD → Binary → FP80)
Program 13  (0x0610) → FBSTP Store BCD (FP80 → Binary → BCD)
Program 14  (0x0700) → FPTAN Partial tangent
Program 15  (0x0710) → FPATAN Partial arctangent
Program 16  (0x0720) → F2XM1 2^x - 1
Program 17  (0x0730) → FYL2X y × log₂(x)
Program 18  (0x0740) → FYL2XP1 y × log₂(x+1)
Program 19  (0x0750) → FSINCOS Sin and Cos (dual result)
Program 20  (0x0760) → FPREM1 IEEE partial remainder
Program 21  (0x0770) → FRNDINT Round to integer
Program 22-31       → Available for extensions
```

### ROM Capacity
- **Microcode ROM**: 4K × 32-bit (16K bytes total)
- **Addresses**: 0x0000 to 0x0FFF
- **Program counter**: 16-bit (allows for expansion)

### Call Stack
- **Depth**: 16 levels
- **Purpose**: Support nested subroutines
- **Auto-increment**: On CALL, auto-decrement on RET

### Key Characteristics
1. **Wait-state based**: Explicitly waits for hardware unit completion
2. **Modular design**: Each instruction/operation has its own microcode sequence
3. **Temporary registers**: Can hold intermediate results between operations
4. **Extended precision**: 128-bit accumulator for Payne-Hanek range reduction
5. **BCD support**: Dedicated BCD conversion interfaces
6. **Condition codes**: Can branch based on compare results

### Typical Sequence for Complex Operation
```
1. LOAD operands into temp_fp_a, temp_fp_b
2. CALL_ARITH with operation code
3. WAIT_ARITH until done
4. LOAD_ARITH_RES into temp_result
5. Process result (move, convert, etc.)
6. STORE to data_out
7. RET
```

---

## Integration Guide for Testbenches

### Dependencies Between Modules
```
FPU_Core (top)
├─→ FPU_RegisterStack
├─→ FPU_ControlWord
├─→ FPU_StatusWord
├─→ FPU_ArithmeticUnit (primary arithmetic)
├─→ FPU_Exception_Handler
├─→ FPU_BCD_to_Binary
├─→ FPU_Binary_to_BCD
├─→ FPU_Payne_Hanek_ROM
└─→ MicroSequencer_Extended_BCD
    ├─→ Uses same FPU_ArithmeticUnit (multiplexed)
    ├─→ Uses same FPU_BCD_to_Binary (multiplexed)
    ├─→ Uses same FPU_Binary_to_BCD (multiplexed)
    └─→ Uses FPU_Payne_Hanek_ROM

FPU_Transcendental
├─→ FPU_CORDIC_Wrapper
├─→ FPU_Polynomial_Evaluator
└─→ Arithmetic Arbiter (arbitrates shared units)

FPU_CORDIC_Wrapper
├─→ FPU_Range_Reduction
├─→ FPU_Atan_Table (ROM)
└─→ External shared AddSub/MulDiv units
```

### Clock Synchronization
- **All modules on same clock**: `clk` (typically 50 MHz)
- **Synchronous resets**: `reset` (active HIGH)
- **No clock gating**: Simple synchronous design

### Interface Latencies
| Operation | Latency | Notes |
|-----------|---------|-------|
| FADD/FSUB | ~25 cycles | IEEE 754 compliant |
| FMUL | ~30 cycles | 64-bit mantissa |
| FDIV | ~35 cycles | Iterative division |
| FSIN/FCOS | ~300-350 cycles | 50 CORDIC iterations |
| FPTAN | ~360-410 cycles | 16 iterations + polynomial |
| FSQRT (microcode) | ~950-1425 cycles | 2 Newton-Raphson iterations |
| Format conversions | ~20-40 cycles | FP32/FP64 ↔ FP80 |
| BCD operations | ~100-200 cycles | Digit-by-digit processing |

### Exception Signaling
- **status_out**: Returns exception flags (sticky)
- **int_request**: Pulses HIGH for unmasked exceptions
- **error output**: Indicates operation failed

### Memory Interface
- **data_in/data_out**: 80-bit bidirectional operands
- **int_data_in/int_data_out**: 32-bit integer conversion
- **has_memory_op**: From decoder to indicate memory operand
- **operand_size**: 0=word, 1=dword, 2=qword, 3=tbyte (80-bit)

---

## Testbench Creation Checklist

For each module, create testbenches covering:

### FPU_CORDIC_Wrapper
- [ ] Basic functionality: sin/cos/tan/atan with known values
- [ ] Quadrant handling: all 4 quadrants
- [ ] Edge cases: 0, ±π/2, ±π
- [ ] Pythagorean identity: sin²+cos² ≈ 1
- [ ] Range reduction bypass for small angles
- [ ] Polynomial correction for tan/atan
- [ ] External unit interface arbitration
- [ ] Timeout/error handling

### FPU_Transcendental
- [ ] Operation routing: all 9 operations
- [ ] Result registers: primary and secondary
- [ ] Arithmetic arbitration: priority handling
- [ ] Polynomial evaluator flow: F2XM1, FYL2X, FYL2XP1
- [ ] Exception propagation from sub-units
- [ ] Pipeline efficiency: concurrent operations
- [ ] Microcode integration with FPU_Core

### FPU_Core
- [ ] Stack push/pop: all 8 registers
- [ ] Arithmetic operations: FADD/FSUB/FMUL/FDIV
- [ ] Control word: rounding modes, exception masks
- [ ] Status word: condition codes, exceptions
- [ ] Memory operations: load/store various formats
- [ ] BCD operations: FBLD/FBSTP
- [ ] Exception generation and INT request
- [ ] Instruction decoding: all 50+ opcodes
- [ ] Microsequencer integration
- [ ] Reset and initialization (FINIT)

### MicroSequencer_Extended_BCD
- [ ] Program loading and execution
- [ ] State machine transitions
- [ ] Register transfers (MOVE operations)
- [ ] Arithmetic unit arbitration
- [ ] BCD converter interface
- [ ] ROM access (Payne-Hanek)
- [ ] Call stack (nesting, return)
- [ ] Wait states and completion signals
- [ ] Program counter and branching
- [ ] Error handling and timeout

---

## Key Test Values

### Trigonometric Functions
```
sin(0) = 0
sin(π/6) = 0.5
sin(π/4) = √2/2 ≈ 0.707107
sin(π/3) = √3/2 ≈ 0.866025
sin(π/2) = 1
sin(π) = 0
sin(3π/2) = -1
sin(2π) = 0

cos(0) = 1
cos(π/6) = √3/2 ≈ 0.866025
cos(π/4) = √2/2 ≈ 0.707107
cos(π/3) = 0.5
cos(π/2) = 0
cos(π) = -1
cos(3π/2) = 0
cos(2π) = 1

tan(0) = 0
tan(π/6) ≈ 0.577350
tan(π/4) = 1
tan(π/3) ≈ 1.732051
tan(π/2) = ∞ (error expected)
```

### Special Values
```
atan(0) = 0
atan(1) = π/4 ≈ 0.785398
atan(∞) = π/2 ≈ 1.570796
atan(-1) = -π/4 ≈ -0.785398
atan(-∞) = -π/2 ≈ -1.570796
```


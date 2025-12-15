# Verilog Component Verification Guide

## Complete Methodology for Hardware Verification

This comprehensive guide covers how to verify hardware components using Verilog simulation and verification techniques, with practical examples from the MyPC project.

---

## Table of Contents

1. [Introduction to Hardware Verification](#1-introduction-to-hardware-verification)
2. [Verification Tools Setup](#2-verification-tools-setup)
3. [Testbench Fundamentals](#3-testbench-fundamentals)
4. [Writing Self-Checking Testbenches](#4-writing-self-checking-testbenches)
5. [Simulation Techniques](#5-simulation-techniques)
6. [Static Analysis with Verilator](#6-static-analysis-with-verilator)
7. [Debugging and Waveform Analysis](#7-debugging-and-waveform-analysis)
8. [Practical Examples](#8-practical-examples)
9. [Best Practices](#9-best-practices)
10. [Common Pitfalls](#10-common-pitfalls)

---

## 1. Introduction to Hardware Verification

### Why Verify Hardware?

Hardware bugs are **expensive** and **difficult to fix** after fabrication or deployment:
- FPGA resynthesis takes hours
- Silicon bugs require new tape-out (millions of dollars)
- Field updates may be impossible

**Verification catches bugs before deployment.**

### Verification vs. Validation

- **Verification:** Does the design match the specification? (Are we building it right?)
- **Validation:** Does the specification match user needs? (Are we building the right thing?)

### Verification Methods

1. **Static Analysis** - Lint checking without simulation (Verilator)
2. **Functional Simulation** - Execute testbenches (Icarus, ModelSim, VCS)
3. **Formal Verification** - Mathematical proof of correctness (SymbiYosys)
4. **Emulation** - Run on actual FPGA hardware
5. **Co-simulation** - Combine software and hardware simulation

This guide focuses on **Static Analysis** and **Functional Simulation**.

---

## 2. Verification Tools Setup

### 2.1 Icarus Verilog (Open Source)

**Best for:** Quick functional simulation, educational use, CI/CD

#### Installation (Ubuntu/Debian):
```bash
sudo apt-get update
sudo apt-get install iverilog
```

#### Installation (macOS):
```bash
brew install icarus-verilog
```

#### Verify Installation:
```bash
iverilog -v
# Expected: Icarus Verilog version 12.0 or later
```

#### Basic Usage:
```bash
# Compile
iverilog -g2012 -o sim_output module.sv testbench.sv

# Run simulation
vvp sim_output

# With VCD waveform dump
vvp sim_output -vcd
```

**Pros:**
- Free and open source
- Fast compilation
- Good SystemVerilog support
- Easy to integrate into scripts

**Cons:**
- Limited SystemVerilog features (unpacked arrays, classes)
- No built-in coverage tools
- Slower simulation than commercial tools

---

### 2.2 Verilator (Open Source)

**Best for:** Static analysis, lint checking, high-performance C++ co-simulation

#### Installation (Ubuntu/Debian):
```bash
# Option 1: Package manager (may be old version)
sudo apt-get install verilator

# Option 2: From source (recommended for latest)
git clone https://github.com/verilator/verilator
cd verilator
autoconf
./configure
make -j$(nproc)
sudo make install
```

#### Verify Installation:
```bash
verilator --version
# Expected: Verilator 4.x or 5.x
```

#### Basic Usage for Lint:
```bash
verilator --lint-only -Wall -Wno-fatal module.sv
```

#### Advanced Usage (C++ Simulation):
```bash
verilator -Wall --cc --exe --build testbench.cpp module.sv
./obj_dir/Vmodule
```

**Pros:**
- Excellent static analysis
- Very fast simulation (compiles to C++)
- Best for finding logic bugs
- Free and open source

**Cons:**
- Not a complete simulator (no 4-state logic)
- Requires C++ knowledge for testbenches
- Learning curve for advanced features

---

### 2.3 ModelSim/Questa (Commercial)

**Best for:** Professional development, advanced debugging, coverage

#### Installation:
- Download from Intel (ModelSim) or Siemens (Questa)
- Requires license (free starter edition available with limitations)

#### Basic Usage:
```tcl
# Compile
vlog -sv module.sv testbench.sv

# Simulate
vsim -c testbench -do "run -all; quit"

# GUI mode
vsim testbench
```

**Pros:**
- Full SystemVerilog support
- Advanced debugging features
- Code coverage analysis
- Professional waveform viewer

**Cons:**
- Expensive commercial license
- Heavy resource usage
- Steep learning curve

---

### 2.4 Tool Selection Guide

| Use Case | Recommended Tool | Alternative |
|----------|------------------|-------------|
| Learning Verilog | Icarus Verilog | Verilator lint |
| CI/CD Pipeline | Icarus Verilog | Verilator |
| Static Analysis | Verilator | Linting tools |
| Finding Logic Bugs | Verilator lint | Icarus |
| Performance Sim | Verilator C++ | Questa |
| Coverage Analysis | Questa/VCS | Open-source tools |
| Small Projects | Icarus Verilog | Verilator |
| Large Projects | Verilator | Questa |

---

## 3. Testbench Fundamentals

### 3.1 Testbench Structure

A complete testbench includes:

```systemverilog
`timescale 1ns/1ps

module MyModule_tb;

// 1. SIGNALS - Declare all DUT (Design Under Test) signals
logic clk;
logic reset;
logic [15:0] data_in;
logic [15:0] data_out;

// 2. TEST TRACKING
integer test_count = 0;
integer pass_count = 0;
integer fail_count = 0;

// 3. DUT INSTANTIATION
MyModule uut (
    .clk(clk),
    .reset(reset),
    .data_in(data_in),
    .data_out(data_out)
);

// 4. CLOCK GENERATION
parameter CLK_PERIOD = 10; // 100MHz
always #(CLK_PERIOD/2) clk = ~clk;

// 5. STIMULUS AND CHECKING
initial begin
    // Initialize
    clk = 0;
    reset = 1;
    data_in = 0;

    // Reset pulse
    #(CLK_PERIOD * 2);
    reset = 0;
    #(CLK_PERIOD * 2);

    // Test cases
    run_test_1();
    run_test_2();

    // Summary
    display_summary();
    $finish;
end

// 6. TEST TASKS
task run_test_1;
    // Test implementation
endtask

// 7. CHECKING TASKS
task automatic check_result(
    input string test_name,
    input [15:0] expected,
    input [15:0] actual
);
    test_count++;
    if (expected === actual) begin
        $display("[PASS] %s", test_name);
        pass_count++;
    end else begin
        $display("[FAIL] %s: Expected 0x%04h, Got 0x%04h",
                 test_name, expected, actual);
        fail_count++;
    end
endtask

// 8. SUMMARY
task display_summary;
    $display("\n========================================");
    $display("Simulation Complete");
    $display("Total Tests: %0d", test_count);
    $display("Passed: %0d", pass_count);
    $display("Failed: %0d", fail_count);
    if (fail_count == 0)
        $display("STATUS: ALL TESTS PASSED!");
    else
        $display("STATUS: SOME TESTS FAILED!");
    $display("========================================");
endtask

// 9. TIMEOUT WATCHDOG
initial begin
    #100000; // Timeout after 100us
    $display("ERROR: Testbench timeout!");
    $finish;
end

endmodule
```

---

### 3.2 Key Components Explained

#### Timescale Directive
```systemverilog
`timescale <time_unit>/<time_precision>
`timescale 1ns/1ps  // 1ns time unit, 1ps precision
```
- **Time unit:** Smallest delay you can specify (#1 means 1ns)
- **Precision:** Simulation accuracy (affects rounding)

#### Signal Declaration
```systemverilog
logic signal;        // 2-state (0, 1) - for synthesis
reg signal;          // 4-state (0, 1, X, Z) - simulation
wire signal;         // Driven by continuous assignment

// Preferred in testbenches:
logic signal;        // Modern SystemVerilog
```

#### Clock Generation
```systemverilog
// Method 1: Always block (most common)
always #5 clk = ~clk;  // 10ns period = 100MHz

// Method 2: Initial with forever
initial begin
    clk = 0;
    forever #5 clk = ~clk;
end

// Method 3: Precise control
parameter CLK_PERIOD = 10;
always #(CLK_PERIOD/2) clk = ~clk;
```

#### Reset Generation
```systemverilog
initial begin
    reset = 1;        // Assert reset
    #100;             // Hold for 100ns
    reset = 0;        // Deassert
end
```

---

## 4. Writing Self-Checking Testbenches

### 4.1 Comparison Methods

#### Method 1: Inline Checks
```systemverilog
initial begin
    data_in = 16'h1234;
    #CLK_PERIOD;
    #CLK_PERIOD;

    if (data_out === 16'h1234) begin
        $display("PASS: Data matches");
    end else begin
        $display("FAIL: Expected 0x1234, got 0x%04h", data_out);
        $finish;
    end
end
```

#### Method 2: Check Tasks (Recommended)
```systemverilog
task automatic check_equal(
    input string name,
    input [15:0] expected,
    input [15:0] actual
);
    test_count++;
    if (expected === actual) begin
        $display("[PASS] %s: 0x%04h", name, actual);
        pass_count++;
    end else begin
        $display("[FAIL] %s: Expected 0x%04h, Got 0x%04h",
                 name, expected, actual);
        fail_count++;
    end
endtask

// Usage:
check_equal("ALU Add Test", 16'h0300, alu_out);
```

#### Method 3: Assertions (Advanced)
```systemverilog
// Immediate assertion
assert (data_out == 16'h1234) else
    $error("Data mismatch: expected 0x1234, got 0x%04h", data_out);

// Concurrent assertion (property)
property data_valid;
    @(posedge clk) enable |-> (data_out != 16'hXXXX);
endproperty

assert property (data_valid) else
    $error("Invalid data on output");
```

---

### 4.2 Expected Value Generation

#### Method 1: Literal Values
```systemverilog
// Simple, but tedious for many tests
expected = 16'h1234;
check_equal("Test 1", expected, actual);
```

#### Method 2: Reference Model
```systemverilog
// Behavioral model in testbench
function automatic [15:0] reference_add(
    input [15:0] a,
    input [15:0] b
);
    return a + b;
endfunction

// Compare DUT to model
expected = reference_add(16'h0100, 16'h0200);
check_equal("ALU Add", expected, alu_out);
```

#### Method 3: Golden Vectors (File-based)
```systemverilog
integer file;
logic [15:0] test_input, test_output;

initial begin
    file = $fopen("test_vectors.txt", "r");
    while (!$feof(file)) begin
        $fscanf(file, "%h %h\n", test_input, test_output);
        data_in = test_input;
        #CLK_PERIOD;
        #CLK_PERIOD;
        check_equal($sformatf("Vector %0d", test_count),
                    test_output, data_out);
    end
    $fclose(file);
end
```

---

### 4.3 Timing Verification

#### Check Setup/Hold Times
```systemverilog
// Setup time check
always @(posedge clk) begin
    if ($past(data_in) !== data_in) begin
        // Data changed near clock edge - potential violation
        $warning("Data changed close to clock edge");
    end
end
```

#### Monitor Timing Violations
```systemverilog
// Use $setuphold for precise timing
specify
    $setuphold(posedge clk, data_in, 2ns, 1ns);
endspecify
```

---

## 5. Simulation Techniques

### 5.1 Directed Testing

Test specific scenarios with known inputs/outputs:

```systemverilog
// Test Case: Basic addition
test_count++;
a = 16'h0100;
b = 16'h0200;
op = ALU_ADD;
#1; // Wait for combinational logic
if (out == 16'h0300 && flags[ZF] == 0 && flags[CF] == 0) begin
    $display("[PASS] Basic addition");
    pass_count++;
end else begin
    $display("[FAIL] Basic addition");
    fail_count++;
end
```

**Pros:** Targeted, easy to debug
**Cons:** May miss corner cases

---

### 5.2 Constrained Random Testing

Generate random but valid test cases:

```systemverilog
integer i;
logic [15:0] random_a, random_b;
logic [31:0] expected;

initial begin
    for (i = 0; i < 1000; i++) begin
        // Generate random inputs
        random_a = $random;
        random_b = $random;

        // Apply to DUT
        a = random_a;
        b = random_b;
        #1;

        // Check with reference model
        expected = random_a + random_b;
        check_equal($sformatf("Random test %0d", i),
                    expected[15:0], out);
    end
end
```

**Pros:** Better coverage
**Cons:** Harder to reproduce failures (use seeds)

---

### 5.3 Corner Case Testing

Always test boundary conditions:

```systemverilog
// Test minimum value
a = 16'h0000;
b = 16'h0000;
test_operation("Min + Min");

// Test maximum value
a = 16'hFFFF;
b = 16'hFFFF;
test_operation("Max + Max");

// Test overflow
a = 16'h7FFF;
b = 16'h0001;
test_operation("Overflow");

// Test zero flag
a = 16'h1234;
b = 16'hEDCC; // Two's complement of 0x1234
test_operation("Zero result");

// Test all bits set
a = 16'hFFFF;
b = 16'hFFFF;
test_operation("All bits");

// Test alternating bits
a = 16'hAAAA;
b = 16'h5555;
test_operation("Alternating bits");
```

---

### 5.4 State Machine Testing

For FSMs, test all states and transitions:

```systemverilog
// Test all states
test_state_idle();
test_state_read();
test_state_write();
test_state_error();

// Test all transitions
test_idle_to_read();
test_idle_to_write();
test_read_to_idle();
test_write_to_error();

// Test illegal transitions
test_illegal_state_transition();
```

---

## 6. Static Analysis with Verilator

### 6.1 Basic Lint Checking

```bash
#!/bin/bash
# run_verilator_lint.sh

verilator --lint-only \
    -Wall \
    -Wno-fatal \
    -sv \
    --top-module MyModule \
    -I./include \
    MyModule.sv
```

**Common Warnings:**
- `UNUSED`: Signal declared but never used
- `UNDRIVEN`: Signal never assigned
- `WIDTH`: Bit width mismatch
- `LATCH`: Unintended latch (incomplete assignments)
- `COMBDLY`: Combinational delay (feedback loop)

---

### 6.2 Comprehensive Analysis

Example from MyPC project:

```bash
verilator --lint-only \
    -Wall \
    -Wno-TIMESCALEMOD \
    -Wno-fatal \
    -sv \
    --top-module emu \
    -I. \
    -Irtl \
    -Irtl/CPU \
    -Irtl/VGA \
    --error-limit 200 \
    mycore.sv \
    rtl/CPU/Core.sv \
    rtl/VGA/*.sv \
    2>&1 | tee verilator.log
```

---

### 6.3 Interpreting Results

#### Example Warning:
```
%Warning-WIDTH: module.sv:45:12: Operator ADD expects 16 bits on the LHS, but LHS's VARREF 'count' generates 8 bits.
```

**Fix:**
```systemverilog
// Before (Warning):
logic [7:0] count;
assign result = count + 16'h0100;  // Width mismatch!

// After (Fixed):
logic [15:0] count;  // Match width
assign result = count + 16'h0100;

// OR use explicit casting:
assign result = {8'b0, count} + 16'h0100;
```

---

## 7. Debugging and Waveform Analysis

### 7.1 Generating VCD Waveforms

```systemverilog
initial begin
    // Dump all signals
    $dumpfile("waves.vcd");
    $dumpvars(0, MyModule_tb);

    // Or specific module:
    $dumpvars(1, MyModule_tb.uut);
end
```

### 7.2 Viewing Waveforms

**GTKWave (Free):**
```bash
gtkwave waves.vcd
```

**Features:**
- Zoom in/out
- Add signals to viewer
- Set radix (hex, binary, decimal)
- Measure timing
- Add markers

---

### 7.3 Debug Prints

#### Basic Printing:
```systemverilog
$display("Time=%0t: data=%h", $time, data);
$write("Value: %d\n", value);  // Like $display but no auto-newline
```

#### Formatted Output:
```systemverilog
$display("Data: %h (hex) %d (dec) %b (bin)", data, data, data);
$display("Time: %0t ns", $time);
$display("String: %s", "Hello");
```

#### Conditional Printing:
```systemverilog
always @(posedge clk) begin
    if (debug_enable)
        $display("Cycle %0d: state=%b", cycle_count, state);
end
```

#### Severity Levels:
```systemverilog
$info("Informational message");
$warning("Warning message");
$error("Error message (continues simulation)");
$fatal("Fatal error (stops simulation)");
```

---

## 8. Practical Examples

### 8.1 Example 1: ALU Testbench

From MyPC CPU verification:

```systemverilog
`timescale 1ns/1ps

`include "FlagsEnum.sv"
`include "MicrocodeTypes.sv"

module ALU_tb;

logic [15:0] a, b;
logic [31:0] out;
logic is_8_bit;
logic [5:0] op;
logic [15:0] flags_in, flags_out;
logic multibit_shift;
logic [4:0] shift_count;
logic busy;

integer test_count = 0;
integer pass_count = 0;
integer fail_count = 0;

ALU uut (
    .a(a),
    .b(b),
    .out(out),
    .is_8_bit(is_8_bit),
    .op(op),
    .flags_in(flags_in),
    .flags_out(flags_out),
    .multibit_shift(multibit_shift),
    .shift_count(shift_count),
    .busy(busy)
);

task automatic check_result(
    input string test_name,
    input [31:0] expected_out,
    input [15:0] expected_flags
);
    #1;
    test_count++;
    if (out === expected_out &&
        (expected_flags === 16'hxxxx || flags_out === expected_flags)) begin
        $display("[PASS] %s", test_name);
        pass_count++;
    end else begin
        $display("[FAIL] %s", test_name);
        $display("       Expected: out=0x%08h, flags=0x%04h",
                 expected_out, expected_flags);
        $display("       Got:      out=0x%08h, flags=0x%04h",
                 out, flags_out);
        fail_count++;
    end
endtask

initial begin
    $display("========================================");
    $display("ALU Testbench Started");
    $display("========================================");

    // Initialize
    a = 0; b = 0; is_8_bit = 0; op = 0;
    flags_in = 0; multibit_shift = 0; shift_count = 0;
    #10;

    // Test 16-bit addition
    $display("\n--- Test: 16-bit ADD ---");
    is_8_bit = 0;
    a = 16'h0100;
    b = 16'h0200;
    op = 6'd2; // ALU_ADD
    #1;
    if (out[15:0] == 16'h0300 && flags_out[CF_IDX] == 0 &&
        flags_out[ZF_IDX] == 0) begin
        $display("[PASS] ADD 0x0100 + 0x0200 = 0x0300");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ADD test");
        fail_count++;
        test_count++;
    end

    // Test with overflow
    a = 16'hFFFF;
    b = 16'h0001;
    #1;
    if (out[15:0] == 16'h0000 && flags_out[CF_IDX] == 1 &&
        flags_out[ZF_IDX] == 1) begin
        $display("[PASS] ADD overflow: CF=1, ZF=1");
        pass_count++;
        test_count++;
    end else begin
        $display("[FAIL] ADD overflow test");
        fail_count++;
        test_count++;
    end

    // Summary
    #10;
    $display("\n========================================");
    $display("Total Tests: %0d", test_count);
    $display("Passed:      %0d", pass_count);
    $display("Failed:      %0d", fail_count);
    if (fail_count == 0)
        $display("STATUS: ALL TESTS PASSED!");
    else
        $display("STATUS: SOME TESTS FAILED!");
    $display("========================================");

    $finish;
end

initial begin
    #10000;
    $display("ERROR: Testbench timeout!");
    $finish;
end

endmodule
```

**Key Features:**
- Self-checking with pass/fail tracking
- Clear test organization
- Timeout watchdog
- Detailed error messages

---

### 8.2 Example 2: Conditional Branch Logic

From MyPC JumpTest verification:

```systemverilog
`timescale 1ns/1ps

module JumpTest_tb;

parameter CF_IDX = 0;
parameter ZF_IDX = 6;
parameter SF_IDX = 7;
parameter OF_IDX = 11;

logic [7:0] opcode;
logic [15:0] flags;
logic taken;

integer test_count = 0;
integer pass_count = 0;

JumpTest uut (
    .opcode(opcode),
    .flags(flags),
    .taken(taken)
);

task automatic check_jump(
    input string name,
    input [7:0] op,
    input [15:0] flg,
    input logic expected
);
    opcode = op;
    flags = flg;
    #1;
    test_count++;
    if (taken === expected) begin
        $display("[PASS] %s", name);
        pass_count++;
    end else begin
        $display("[FAIL] %s: expected=%b, got=%b", name, expected, taken);
    end
endtask

function [15:0] set_flag(input [15:0] base, input integer idx, input logic val);
    if (val)
        return base | (1 << idx);
    else
        return base & ~(1 << idx);
endfunction

initial begin
    $display("JumpTest Testbench");

    // Test JE (Jump if Equal/Zero)
    check_jump("JE with ZF=1", 8'h74, set_flag(16'h0000, ZF_IDX, 1), 1'b1);
    check_jump("JE with ZF=0", 8'h74, set_flag(16'h0000, ZF_IDX, 0), 1'b0);

    // Test JNE (Jump if Not Equal)
    check_jump("JNE with ZF=0", 8'h75, set_flag(16'h0000, ZF_IDX, 0), 1'b1);
    check_jump("JNE with ZF=1", 8'h75, set_flag(16'h0000, ZF_IDX, 1), 1'b0);

    // Summary
    $display("\nTotal: %0d, Passed: %0d", test_count, pass_count);
    $finish;
end

endmodule
```

---

### 8.3 Example 3: Register File with Timing

```systemverilog
module RegisterFile_tb;

parameter CLK_PERIOD = 10;

logic clk, reset;
logic is_8_bit;
logic [2:0] rd_sel[2];
logic [15:0] rd_val[2];
logic [2:0] wr_sel;
logic [15:0] wr_val;
logic wr_en;

RegisterFile uut (
    .clk(clk),
    .reset(reset),
    .is_8_bit(is_8_bit),
    .rd_sel(rd_sel),
    .rd_val(rd_val),
    .wr_sel(wr_sel),
    .wr_val(wr_val),
    .wr_en(wr_en)
);

always #(CLK_PERIOD/2) clk = ~clk;

initial begin
    // Initialize
    clk = 0;
    reset = 1;
    is_8_bit = 0;
    wr_en = 0;
    #(CLK_PERIOD * 2);
    reset = 0;
    #(CLK_PERIOD * 2);

    // Write to register
    wr_sel = 3'b000; // AX
    wr_val = 16'h1234;
    wr_en = 1;
    #CLK_PERIOD;
    wr_en = 0;

    // Read back (account for registered output - 1 cycle delay)
    rd_sel[0] = 3'b000;
    #CLK_PERIOD; // Wait for read register
    #CLK_PERIOD; // Output appears

    if (rd_val[0] === 16'h1234)
        $display("[PASS] Register write/read");
    else
        $display("[FAIL] Expected 0x1234, got 0x%04h", rd_val[0]);

    $finish;
end

endmodule
```

**Key Point:** Account for registered outputs - add extra clock cycles!

---

## 9. Best Practices

### 9.1 Testbench Organization

```
project/
├── rtl/
│   ├── module1.sv
│   └── module2.sv
├── sim/ or tb/
│   ├── module1_tb.sv
│   ├── module2_tb.sv
│   └── common/
│       ├── test_utils.sv
│       └── assertions.sv
├── scripts/
│   ├── run_all_tests.sh
│   ├── run_verilator.sh
│   └── check_coverage.sh
└── results/
    └── sim_YYYYMMDD_HHMMSS/
```

---

### 9.2 Naming Conventions

```systemverilog
// Module Under Test
MyModule uut (...)          // "uut" = Unit Under Test
MyModule dut (...)          // "dut" = Design Under Test

// Testbench signals - use descriptive names
logic expected_output;      // Not "exp" or "e"
logic [15:0] test_data;     // Not "td" or "data"

// Test cases - descriptive names
test_basic_addition();
test_overflow_condition();
test_edge_case_all_ones();
```

---

### 9.3 Modular Testbenches

```systemverilog
// Separate file: test_utils.svh
package test_utils;

    typedef struct {
        integer total;
        integer passed;
        integer failed;
    } test_stats_t;

    function automatic void print_stats(test_stats_t stats);
        $display("Tests: %0d, Passed: %0d, Failed: %0d",
                 stats.total, stats.passed, stats.failed);
    endfunction

endpackage

// In testbench:
import test_utils::*;

test_stats_t stats = '{0, 0, 0};
```

---

### 9.4 Parameterized Testbenches

```systemverilog
module MyModule_tb #(
    parameter DATA_WIDTH = 16,
    parameter ADDR_WIDTH = 8
);

logic [DATA_WIDTH-1:0] data;
logic [ADDR_WIDTH-1:0] addr;

MyModule #(
    .DATA_WIDTH(DATA_WIDTH),
    .ADDR_WIDTH(ADDR_WIDTH)
) uut (
    .data(data),
    .addr(addr)
);

// Test with different parameters
initial begin
    if (DATA_WIDTH == 16)
        test_16bit();
    else if (DATA_WIDTH == 32)
        test_32bit();
end

endmodule
```

---

### 9.5 Automated Test Scripts

```bash
#!/bin/bash
# run_all_tests.sh

LOGDIR="sim_results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$LOGDIR"

TESTS=(
    "ALU_tb"
    "RegisterFile_tb"
    "JumpTest_tb"
)

total_pass=0
total_fail=0

for test in "${TESTS[@]}"; do
    echo "Running $test..."

    iverilog -g2012 -o "$LOGDIR/${test}.vvp" \
        -I rtl \
        rtl/*.sv \
        sim/${test}.sv

    vvp "$LOGDIR/${test}.vvp" > "$LOGDIR/${test}.log"

    # Parse results
    pass=$(grep "Passed:" "$LOGDIR/${test}.log" | awk '{print $2}')
    fail=$(grep "Failed:" "$LOGDIR/${test}.log" | awk '{print $2}')

    total_pass=$((total_pass + pass))
    total_fail=$((total_fail + fail))

    if [ "$fail" -eq 0 ]; then
        echo "✓ $test PASSED"
    else
        echo "✗ $test FAILED"
    fi
done

echo ""
echo "========================================"
echo "Overall Results"
echo "========================================"
echo "Total Passed: $total_pass"
echo "Total Failed: $total_fail"
if [ "$total_fail" -eq 0 ]; then
    echo "STATUS: ALL TESTS PASSED"
    exit 0
else
    echo "STATUS: SOME TESTS FAILED"
    exit 1
fi
```

---

## 10. Common Pitfalls

### 10.1 Race Conditions

**Problem:**
```systemverilog
initial begin
    clk = 0;
    data = 16'h1234;

    #10 clk = 1;  // Clock edge
    #0  data = 16'h5678;  // Zero delay - RACE!
end
```

**Solution:**
```systemverilog
initial begin
    clk = 0;
    data = 16'h1234;

    #10 clk = 1;
    #1  data = 16'h5678;  // Small delay after edge
end

// OR use non-blocking assignments:
always @(posedge clk) begin
    data <= 16'h5678;  // Non-blocking (<=) is safer
end
```

---

### 10.2 X/Z Propagation

**Problem:**
```systemverilog
logic [15:0] data;  // Uninitialized = X
logic [15:0] result;

result = data + 16'h0001;  // X + 1 = X
```

**Solution:**
```systemverilog
logic [15:0] data = 16'h0000;  // Initialize

// OR in initial block:
initial begin
    data = 16'h0000;
    // ...
end
```

---

### 10.3 Blocking vs Non-Blocking

**Problem:**
```systemverilog
always @(posedge clk) begin
    a = b;  // Blocking (=) in sequential logic - WRONG!
    c = a;  // Uses new value of a immediately
end
```

**Solution:**
```systemverilog
always @(posedge clk) begin
    a <= b;  // Non-blocking (<=) for sequential
    c <= a;  // Uses old value of a (correct)
end

always_comb begin
    y = a & b;  // Blocking (=) for combinational - CORRECT
end
```

**Rule:** Use `<=` in `always_ff`, use `=` in `always_comb`

---

### 10.4 Incomplete Sensitivity Lists

**Problem:**
```systemverilog
always @(a) begin  // Missing b in sensitivity list
    y = a & b;     // Won't update when b changes!
end
```

**Solution:**
```systemverilog
always @(a, b) begin  // Complete list
    y = a & b;
end

// OR better: use always_comb (automatic sensitivity)
always_comb begin
    y = a & b;
end
```

---

### 10.5 Timing Issues with Registered Outputs

**Problem:**
```systemverilog
// Module has registered output
always_ff @(posedge clk)
    data_out <= data_in;

// Testbench expects immediate result
data_in = 16'h1234;
#1;  // Short delay
if (data_out == 16'h1234)  // FAILS! Need clock cycle
```

**Solution:**
```systemverilog
data_in = 16'h1234;
@(posedge clk);  // Wait for clock edge
#1;              // Small delay after edge
if (data_out == 16'h1234)  // Now passes
```

---

## Summary Checklist

### Before Simulation:
- [ ] Understand module specification
- [ ] Identify all inputs/outputs
- [ ] List corner cases to test
- [ ] Choose simulation tool

### Writing Testbench:
- [ ] Set correct timescale
- [ ] Declare all signals
- [ ] Instantiate DUT correctly
- [ ] Generate clock (if needed)
- [ ] Generate reset
- [ ] Write test cases
- [ ] Add self-checking
- [ ] Add timeout watchdog
- [ ] Add summary display

### Running Tests:
- [ ] Compile without errors
- [ ] Run simulation
- [ ] Check all tests pass
- [ ] Review waveforms (if failures)
- [ ] Run static analysis
- [ ] Document results

### Best Practices:
- [ ] Test corner cases
- [ ] Use meaningful names
- [ ] Add comments
- [ ] Keep testbenches modular
- [ ] Automate with scripts
- [ ] Track coverage (if possible)
- [ ] Version control testbenches

---

## Additional Resources

### Documentation:
- SystemVerilog LRM (IEEE 1800-2017)
- Icarus Verilog documentation
- Verilator manual
- GTKWave user guide

### Books:
- "Writing Testbenches" by Janick Bergeron
- "SystemVerilog for Verification" by Chris Spear
- "Digital Design and Computer Architecture" by Harris & Harris

### Online:
- [ASIC World - Verilog Tutorial](http://www.asic-world.com/verilog/)
- [ChipVerify - SystemVerilog Tutorials](https://www.chipverify.com/)
- [Verilator Documentation](https://verilator.org/guide/latest/)

---

**Document Version:** 1.0
**Date:** November 6, 2025
**Project:** MyPC - PCXT on MiSTer FPGA
**Author:** Claude (AI Assistant)

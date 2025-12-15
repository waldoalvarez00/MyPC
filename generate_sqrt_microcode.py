#!/usr/bin/env python3
"""Generate corrected SQRT microcode with proper operand order"""

# Starting address for iterations
addr = 0x0142

print("        // Iteration template: x_{n+1} = 0.5 × (x_n + S/x_n)")
print("        // Corrected to compute S/x_n (not x_n/S)")

for iteration in range(1, 9):
    print(f"\n        // Iteration {iteration}: x{iteration} = 0.5 × (x{iteration-1} + S/x{iteration-1})")

    instructions = [
        (f"MOVE_A_TO_B", f"8'd0", f"Save x{iteration-1} to temp_fp_b"),
        (f"MOVE_C_TO_A", f"8'd0", f"Load S into temp_fp_a"),
        (f"CALL_ARITH", f"8'd3", f"S / x{iteration-1} (DIV)"),
        (f"WAIT_ARITH", f"8'd0", f"Wait"),
        (f"LOAD_ARITH_RES", f"8'd0", f"Load quotient"),
        (f"MOVE_RES_TO_A", f"8'd0", f"quotient → temp_fp_a"),
        (f"CALL_ARITH", f"8'd0", f"quotient + x{iteration-1} (ADD, x{iteration-1} still in B)"),
        (f"WAIT_ARITH", f"8'd0", f"Wait"),
        (f"LOAD_ARITH_RES", f"8'd0", f"Load sum"),
        (f"MOVE_RES_TO_A", f"8'd0", f"sum → temp_fp_a"),
        (f"LOAD_HALF_B", f"8'd0", f"0.5 → temp_fp_b"),
        (f"CALL_ARITH", f"8'd2", f"0.5 × sum (MUL)"),
        (f"WAIT_ARITH", f"8'd0", f"Wait"),
        (f"LOAD_ARITH_RES", f"8'd0", f"Load x{iteration}"),
        (f"MOVE_RES_TO_A", f"8'd0", f"x{iteration} → temp_fp_a"),
    ]

    for i, (mop, imm, comment) in enumerate(instructions):
        next_addr = addr + i + 1
        print(f"        microcode_rom[16'h{addr+i:04X}] = {{OPCODE_EXEC, MOP_{mop}, {imm}, 15'h{next_addr:04X}}};  // {comment}")

    addr += len(instructions)

print(f"\n        // Store final result and return")
print(f"        microcode_rom[16'h{addr:04X}] = {{OPCODE_RET, 5'd0, 8'd0, 15'd0}};  // Return with result in temp_result")
print(f"\n        // SQRT microcode ends at 0x{addr:04X} ({addr - 0x0140} instructions total)")

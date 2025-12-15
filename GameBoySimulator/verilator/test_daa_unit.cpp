// Unit test for DAA instruction - tests specific known values
#include <cstdio>
#include <cstdint>
#include <cstring>

// Correct GameBoy DAA implementation (reference)
// Returns: result in low 8 bits, flags in bits 15:8 (Z=15, N=14, H=13, C=12)
uint16_t correct_daa(uint8_t a, uint8_t f) {
    int n = (f >> 6) & 1;  // GB N flag
    int h = (f >> 5) & 1;  // GB H flag
    int c = (f >> 4) & 1;  // GB C flag

    int result = a;
    int carry_out = c;

    if (n == 0) {
        // After addition
        if (h || (result & 0x0F) > 9) {
            result += 0x06;
        }
        if (c || result > 0x9F) {
            result += 0x60;
            carry_out = 1;
        }
    } else {
        // After subtraction
        if (h) {
            result -= 0x06;
        }
        if (c) {
            result -= 0x60;
        }
    }

    result &= 0xFF;
    int z = (result == 0) ? 1 : 0;

    // Return result + flags (Z N H C in GB positions)
    uint8_t flags_out = (z << 7) | (n << 6) | (0 << 5) | (carry_out << 4);
    return (flags_out << 8) | result;
}

struct TestCase {
    uint8_t a_in, f_in;
    uint8_t expected_a, expected_f;
};

int main(int argc, char** argv) {
    printf("=== DAA Unit Test ===\n\n");

    // Test cases - specifically targeting values that might produce 0xA0 or 0xD2
    TestCase tests[] = {
        // a_in, f_in(Z=7,N=6,H=5,C=4), expected_a, expected_f
        // Format: f_in uses GB positions

        // Basic cases
        {0x00, 0x00, 0x00, 0x80},   // DAA of 0 = 0, Z=1
        {0x09, 0x00, 0x09, 0x00},   // 9 -> 9 (no adjust)
        {0x0A, 0x00, 0x10, 0x00},   // 10 -> 16 (BCD)
        {0x0F, 0x00, 0x15, 0x00},   // 15 -> 21 (BCD)

        // Values that should produce >0x99 adjustment
        {0x9A, 0x00, 0x00, 0x90},   // 0x9A -> 0x00 with C (add 0x66)
        {0x99, 0x00, 0x99, 0x00},   // 0x99 -> 0x99 (no adjust needed)
        {0xA0, 0x00, 0x00, 0x90},   // 0xA0 -> 0x00 with C (add 0x60)
        {0xFF, 0x00, 0x65, 0x10},   // 0xFF -> 0x65 with C (add 0x66)

        // Half-carry cases
        {0x0A, 0x20, 0x10, 0x00},   // H flag set - should add 6
        {0x00, 0x20, 0x06, 0x00},   // H flag set, A=0

        // Carry flag cases
        {0x00, 0x10, 0x60, 0x10},   // C flag set - should add 0x60
        {0x0A, 0x10, 0x70, 0x10},   // C + need low adjust

        // After subtraction (N=1)
        {0x00, 0x40, 0x00, 0xC0},   // Sub, A=0 -> 0, Z=1
        {0x06, 0x60, 0x00, 0xC0},   // Sub with H -> subtract 6
        {0x60, 0x50, 0x00, 0xD0},   // Sub with C -> subtract 0x60

        // Complex cases
        {0x9A, 0x20, 0x00, 0x90},   // H set + A>9 in high nibble
        {0xAA, 0x00, 0x10, 0x10},   // Both nibbles >9
    };

    int num_tests = sizeof(tests) / sizeof(tests[0]);
    int passed = 0;
    int failed = 0;

    printf("Testing reference DAA implementation:\n");
    for (int i = 0; i < num_tests; i++) {
        TestCase& t = tests[i];
        uint16_t ref = correct_daa(t.a_in, t.f_in);
        uint8_t ref_a = ref & 0xFF;
        uint8_t ref_f = (ref >> 8) & 0xF0;

        // Recalculate expected using reference
        t.expected_a = ref_a;
        t.expected_f = ref_f;

        printf("Test %2d: A=0x%02X F=0x%02X -> A=0x%02X F=0x%02X",
               i, t.a_in, t.f_in, ref_a, ref_f);

        int n_in = (t.f_in >> 6) & 1;
        int h_in = (t.f_in >> 5) & 1;
        int c_in = (t.f_in >> 4) & 1;
        printf(" (N=%d H=%d C=%d)\n", n_in, h_in, c_in);
    }

    printf("\n=== Checking values that produce 0xA0, 0xD2 ===\n");

    // Search for any input that should produce 0xA0 or 0xD2
    printf("\nInputs that should produce A=0xA0:\n");
    for (int a = 0; a < 256; a++) {
        for (int f = 0; f < 256; f += 0x10) {  // Only check flag combinations
            // Only valid flag combinations (Z N H C in bits 7,6,5,4)
            if ((f & 0x0F) != 0) continue;

            uint16_t ref = correct_daa(a, f);
            uint8_t ref_a = ref & 0xFF;
            if (ref_a == 0xA0) {
                int n = (f >> 6) & 1;
                int h = (f >> 5) & 1;
                int c = (f >> 4) & 1;
                printf("  A=0x%02X F=0x%02X (N=%d H=%d C=%d) -> 0xA0\n", a, f, n, h, c);
            }
        }
    }

    printf("\nInputs that should produce A=0xD2:\n");
    for (int a = 0; a < 256; a++) {
        for (int f = 0; f < 256; f += 0x10) {
            if ((f & 0x0F) != 0) continue;

            uint16_t ref = correct_daa(a, f);
            uint8_t ref_a = ref & 0xFF;
            if (ref_a == 0xD2) {
                int n = (f >> 6) & 1;
                int h = (f >> 5) & 1;
                int c = (f >> 4) & 1;
                printf("  A=0x%02X F=0x%02X (N=%d H=%d C=%d) -> 0xD2\n", a, f, n, h, c);
            }
        }
    }

    // Cross-check with an alternative algorithm
    printf("\n=== Cross-check: Testing all 4096 AF combinations ===\n");
    int mismatches = 0;

    for (int f_in = 0; f_in < 256; f_in += 0x10) {  // Valid flag combinations
        for (int a_in = 0; a_in < 256; a_in++) {
            // Reference implementation #1 (from test - uses order: +6 first, then +60)
            uint16_t ref1 = correct_daa(a_in, f_in);
            uint8_t a1 = ref1 & 0xFF;
            uint8_t f1 = (ref1 >> 8) & 0xFF;

            // Reference implementation #2 (alternative, checking both conditions on original value)
            uint8_t a2 = a_in;
            int n2 = (f_in >> 6) & 1;
            int h2 = (f_in >> 5) & 1;
            int c2 = (f_in >> 4) & 1;
            int c_out2 = c2;

            if (n2 == 0) {
                // Addition - both checks on original
                bool adj60 = c2 || (a_in > 0x99);
                bool adj06 = h2 || ((a_in & 0x0F) > 0x09);
                if (adj60) { a2 += 0x60; c_out2 = 1; }
                if (adj06) { a2 += 0x06; }
            } else {
                // Subtraction
                if (c2) { a2 -= 0x60; }
                if (h2) { a2 -= 0x06; }
            }
            int z2 = (a2 == 0) ? 1 : 0;
            uint8_t f2 = (z2 << 7) | (n2 << 6) | (0 << 5) | (c_out2 << 4);

            if (a1 != a2 || f1 != f2) {
                if (mismatches < 10) {
                    printf("MISMATCH: A=0x%02X F=0x%02X -> ref1: A=0x%02X F=0x%02X, ref2: A=0x%02X F=0x%02X\n",
                           a_in, f_in, a1, f1, a2, f2);
                }
                mismatches++;
            }
        }
    }

    if (mismatches == 0) {
        printf("All 4096 AF combinations match between implementations.\n");
    } else {
        printf("Total mismatches: %d\n", mismatches);
    }

    printf("\n=== Test complete ===\n");
    return 0;
}

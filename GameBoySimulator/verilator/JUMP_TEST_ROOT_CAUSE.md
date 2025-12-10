# Jump Test Failure - Root Cause Found

## Critical Finding

**The boot ROM is NOT loaded!** All bytes read by CPU are $00.

## Evidence

Memory read test shows CPU reading all zeros:
```
  $0001: $00 (should be $FE)
  $0002: $00 (should be $FF)
  $0003: $00 (should be $C3 - JP opcode)
  $0004: $00 (should be $10 - target low)
  $0005: $00 (should be $00 - target high, correct by coincidence)
```

## Why CPU Jumps to $00C3

With all bytes being $00:
- CPU reads opcode $00 (NOP) at each address
- Executes NOPs and increments PC
- Eventually hits uninitialized memory containing garbage
- Random byte $C3 found somewhere causes jump

JR works because it uses relative offset (+10) from current PC, not absolute address from memory.

## Root Cause

The `load_test_program()` function is NOT actually writing to boot ROM memory. Possible reasons:

1. **Wrong signal timing** - boot_download/boot_wr not held long enough
2. **dpram not getting write enable** - Signal path broken
3. **Memory clearing** - Something clears boot ROM after we write it
4. **Address calculation bug** - Writes go to wrong addresses (but this was ruled out earlier)

## Why Real Boot ROM Test Works

The real boot ROM test uses the SAME `load_test_program()` function but works. This suggests:
- The function itself is correct
- Something DIFFERENT happens between loading and execution in the failing tests
- Possibly cart download or reset timing interferes

## Next Steps

1. Remove cart download simulation - it might be clearing boot ROM
2. Add more cycles between boot ROM load and reset release
3. Verify boot ROM memory directly (if possible with Verilator public access)
4. Compare exact initialization sequence between working and failing tests

## Test Status

Currently 16/18 tests passing:
- ✅ Real boot ROM execution - WORKS (uses same load function!)
- ❌ JP/CALL tests - FAIL (boot ROM all zeros)

**The failing tests are NOT CPU bugs - they are test infrastructure bugs!**

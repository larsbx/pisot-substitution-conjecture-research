# Compiled N2 checked addition

This receipt concerns the x86-64 executable built from PSC revision
`9a1357ed5dae3b4502d29c34396d0e9403ccca75` with Mojo
`1.1.0.dev2026090805 (34562fa1)`. The inspected ELF SHA-256 is
`8698153ffc6436ee155c15e8535634303bdafeee870a03f77c03bdeba6f2a204`.
Two builds in the same checkout and toolchain directory had that digest.
The executable embeds absolute source and toolchain paths.

At entry `0xaa96`, `r12` holds the old count and `rbp` the increment.
The sign tests select the corresponding signed bounds. Either overflow
test leads to `0xaac8`. The other path reaches the register ADD at
`0xab17`. The executable LOAD segment has equal file and virtual offsets
for both slices. A restricted x86-64 decoder recognizes the instruction encodings in both
slices. Lean evaluates the decoder at each of the 20 instruction addresses
and symbolically executes the decoded sequence with projected registers and
flags. The two stack reload values are arbitrary in the theorem. The model
assumes those reads succeed.

`N2MachineSlice.checked_binary_count` proves that the decoded execution rejects
exactly the overflowing sums of two nonnegative signed 64-bit operands,
and that the accepted register value equals the integer sum. This
discharges the arithmetic behavior of the modeled slice for every such
register pair.

## Replay

Using the recorded Mojo toolchain and Lean pinned by PSC:

```sh
(cd kernel && mojo build -I . tests/test_word_counter_overflow.mojo -o /tmp/psc-word-counters)
sha256sum /tmp/psc-word-counters
readelf -lW /tmp/psc-word-counters
objdump -d --start-address=0xaa96 --stop-address=0xaac8 /tmp/psc-word-counters
objdump -d --start-address=0xab01 --stop-address=0xab1a /tmp/psc-word-counters
lean --run proof/WordCounters/N2MachineSlice.lean /tmp/psc-word-counters
```

The Lean command checks both instruction slices. The digest identifies
the full recorded executable separately. A changed byte in either slice
or a file truncated before the second slice must be refused. The
arithmetic theorem's axiom report lists only `propext`,
`Classical.choice`, and `Quot.sound`.

The remaining binary obligations are to relate the projected instruction
semantics to an independent x86-64 semantics, establish the entry invariant
from the array loads, connect the ADD to the store and the rejection branch
to the returned error, and prove the loop and runtime behavior for N2, N3,
and N4. This receipt supplies no full-function or compiler-wide
refinement claim.

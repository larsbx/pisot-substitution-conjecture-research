# Compiled N2 checked addition and overflow return

This receipt concerns the x86-64 executable built from PSC revision
`9a1357ed5dae3b4502d29c34396d0e9403ccca75` with Mojo
`1.1.0.dev2026090805 (34562fa1)`. The inspected ELF SHA-256 is
`8698153ffc6436ee155c15e8535634303bdafeee870a03f77c03bdeba6f2a204`.
Two builds in the same checkout and toolchain directory had that digest.
The executable embeds absolute source and toolchain paths.

At entry `0xaa8a`, the two indexed loads read the increment and old count
from little-endian memory. The sign tests select the corresponding signed
bounds. Overflow takes the branch to `0xaac8`. The successful path adds the
operands and stores at `0xab39`. The model stops at the rejection branch
or immediately after the store.

A restricted x86-64 decoder recognizes the 29 recorded instruction
encodings. Lean symbolically executes their projected registers, flags,
and byte memory. The memory model assumes valid reads and writes. Its
stack-base premise requires that the reload at `rsp + 0xb0` restore the
initial output base in `r13`. The other stack reload is unrestricted.

`N2MachineSlice.checked_binary_update` proves that for nonnegative
loaded operands, overflow reaches rejection with identical memory.
Otherwise, the decoded store writes the exact sum at the same indexed
address from which the old count was loaded. `writeWord_outside` gives
the byte-level frame for the other addresses.

The overflow continuation checks 42 more instructions across error
preparation (`0xaae7–0xab00`), conditional cleanup (`0xacbd–0xad03`), and
the return block (`0xad04–0xad4d`). It checks the 33 message bytes at `0xd5b0`.
`overflow_produces_error` composes this projection with the checked update
and proves that an overflowing input produces tag 1, message length 33
and the relocated address of `checked integer addition overflow`. It also
establishes the return-buffer pointer and models the frame consumption
through the return to the saved caller address.

The cleanup theorem covers both skip branches and both calls. It records
a free of the first allocation exactly when the ownership byte is nonzero,
then a free of the second allocation exactly when the saved signed count
is positive. The decoded displacements target `0xacd7` and `0xad04` for
the skips and the same aligned-free PLT entry for both calls. Each of the
four paths reaches the return block with the message fields preserved and
tag 1.

The projection assumes a valid frame and disjoint ABI fields. Its inputs
represent the ownership byte, saved signed count, allocation bases, return
buffer, and saved caller address. The free-call model assumes each call
returns with the projected state and stack intact. It records which frees
were requested and leaves allocator behavior to a separate contract.
The stack-trace call and the control-flow transition from preparation
to cleanup remain summary boundaries.

## Replay

Using the recorded Mojo toolchain and Lean pinned by PSC:

```sh
(cd kernel && mojo build -I . tests/test_word_counter_overflow.mojo -o /tmp/psc-word-counters)
sha256sum /tmp/psc-word-counters
readelf -lW /tmp/psc-word-counters
objdump -d --start-address=0xaa8a --stop-address=0xaac8 /tmp/psc-word-counters
objdump -d --start-address=0xab01 --stop-address=0xab3e /tmp/psc-word-counters
lean --run proof/WordCounters/N2MachineSlice.lean /tmp/psc-word-counters
```

The Lean command checks the instruction slices and the error message bytes. The digest identifies
the full recorded executable separately. A changed byte in either slice
or a file truncated before the second slice must be refused. Mutations of
the cleanup skip displacements at `0xaccb` and `0xacf5` or the second
free-call displacement at `0xacfd` are also refused. The axiom reports
list only `propext`, `Classical.choice`, and `Quot.sound`.

The remaining binary obligations are to relate the projected instruction
semantics to an independent x86-64 semantics, derive the address, memory
validity, stack-base, and nonnegativity premises from the compiled loop
invariant, and verify the omitted control-flow transitions and runtime
contracts used by the error projection.
The N2, N3, and N4 loops and runtime still require their own proofs.

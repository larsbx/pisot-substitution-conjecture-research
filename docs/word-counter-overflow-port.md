# Checked scattered-subword counters in PSC

The PSC comparison base is `06dac7ea4e83a6b5a2c7c36bfe84cfec75da3903`.
The vendored `substitution_dynamics` package matches
[finite-math-kernels #98](https://github.com/larsbx/finite-math-kernels/pull/98)
at head `c4afbbd5e7a069fe578aea45700820c272594cc8`. That PR merged as
`da0683512cf31ce19048c1f64efe3bed9574e234` into
`verification/lean-foundations-2026-11-06`. All vendored packages use that merge revision to preserve PSC's shared upstream
pin. The `finite_exact` snapshot also includes upstream's `word_range.mojo`
and its documentation entry. The existing `checked_int.mojo` is byte-identical.

For valid alphabet indices, checked square and cube dimensions bound the
row-major indices. The streaming recurrence appends the current letter to
each shorter prefix subsequence before updating the shorter counters.
Each accumulation checks representability before addition. Two successful
nonnegative counts have a representable signed difference. Any failed
operand propagates its error through the difference and its consumers.
The fixed-alphabet degree-four recurrence uses the same addition check
because the first-defect classifier can reach it after both lower differences
vanish. Its dimensions are compile-time constants.

An arithmetic refusal aborts the affected evaluation. It supplies no
defect classification, component verdict, or certificate result. A caller
must use the command's successful exit status as well as any diagnostic
output. The checks apply to these word counters and their differences.
Separate tensor operations and other machine-integer routines retain their
own arithmetic contracts.

## Replay

From `kernel/`, run:

```sh
pixi run mojo run -I . tests/test_word_counter_overflow.mojo
pixi run mojo run -I . tests/test_words_streaming.mojo
pixi run test
pixi run verify
pixi run defect-degree-census
pixi run degree3-catalog
pixi run wedge-productivity-catalog
```

Compare the successful certificate and census output with the same commands
at the comparison base using the same pinned toolchain. The new regression
checks the largest fitting constant triple count and the first refusal,
the four-million-letter reproduction, multiplication overflow before
allocation, saturation of the addition primitive used in prefix updates,
and propagation through the PSC classification path. The prefix saturation
probe exercises the arithmetic primitive directly. It avoids allocating
billions of letters to drive an actual prefix pair counter out of range.

The [upstream Lean and native-conformance run](https://github.com/larsbx/finite-math-kernels/actions/runs/42268160923)
checked the mathematical counter model and independently compared native
observations at the #98 head. PSC's regressions exercise the vendored native
code through the PSC bindings. A proof that compiled Mojo implements the
Lean model for every valid input remains a separate refinement obligation.
There is no new Lean assertion about the PSC degree-four implementation.

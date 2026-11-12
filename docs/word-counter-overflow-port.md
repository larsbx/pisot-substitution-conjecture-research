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

## Verification record

The original PSC binary returned `-7780085407041551616` on the four-million-letter
input. The patched native regression reached its contract receipt using Mojo
`1.1.0.dev2026090805 (34562fa1)`. The baseline and port produced byte-identical
ten-check spectral certificate reports (SHA-256
`6225bb4a203a3f006b766c1e99c549318e00cafd3572394334c172a6480973f8`).
The existing small streaming, kernel and census-library regression reports
also matched byte for byte.

PSC [run 43171890790](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43171890790)
passed the Mojo kernel, spectral replay and Lean proof jobs at initial port
head `294ae330de2938c4eea2cc7c6234639fb8780437`. The dedicated
[defect census run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43171890744)
passed all three catalogues. Initial Python and provenance gates found
historical source-pin drift and a mixed vendor revision. The coordinated
snapshot restores the single vendor revision. The historical Class-C Mojo
audit reads Git blobs at its original recording revision. The Class-D
[rebind packet](../evidence/class-d-word-counter-rebind-2026-11-12/README.md)
validates the fresh complete replay for the three changed archived source paths.

At `9419b59b7560eda99f067deaec8a433ff4ccf1bb` the local Python suite passed
2,112 tests and 28 subtests, with 12 skips. The three affected native
catalogues matched the baseline byte for byte:

| Report | SHA-256 |
| --- | --- |
| First defect degree | `0a7da71455fae0e861a05681f90a81a9a08711cda59aab0c7248e301faaf5a7e` |
| Degree-three taxonomy | `d45788245bc114f38f679d41815ae684a8e173070bdebcfdb65d22c2150351ce` |
| Wedge productivity | `8b12a09d8961813b5b9014bb5f8b2f08c59fdf6c366b08f3ad53efa6238cb0bb` |

The Class-C integration workflow also verifies the preserved historical
audit at its recording revision `3632f28242aa484485ecee752c5e28f9b713cf81`.
The resulting provenance report remains byte-identical to the archive. The
current-source native and independent-oracle steps still compare their
outputs to the original certificate packet.

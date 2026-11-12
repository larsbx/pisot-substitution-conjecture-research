# Full-bank consumer import repair

The complete audit at candidate `ed8251b95a770476fdb96248e42ef10ac54d0c93`
compiled all three new overlap modules, but rejected two older consumers
of the narrowed `Cyclicity` imports:

| Consumer | Missing declaration | Explicit import added |
| --- | --- | --- |
| `ParikhRank` | `minpoly.eq_of_irreducible_of_monic` | `Mathlib.FieldTheory.Minpoly.Field` |
| `DescendantSpan` | `dotProduct_self_eq_zero.mp` | `Mathlib.LinearAlgebra.Matrix.DotProduct` |

Every other byte of these two source files, including theorem statements
and proof bodies, matches the failed candidate. The three new overlap
modules and their 42-module development dependency graph are unchanged.
`consumer_import_repair_receipt.json` records the two exact import additions
and source hashes. All 20 historical source manifests passed without a
registry edit. Its pending development status is the status at capture;
later results are recorded separately in the implementation PR.

The failed [physical-mass audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43125122949)
and the [dedicated full audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43125122828)
are preserved as losslessly compressed raw logs, revision/job receipts,
and a readable diagnostic extract. `archive-index.json` authenticates the
decompressed bytes. Successful compilation of the three new modules does
not turn this failed full-bank run into an accepted audit.

The canonical acceptance requirement remains a fresh complete
`tools/check_lean.sh` build and compiled declaration/axiom audit at the
corrected published revision. [PR #549](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/549)
records that result and the status of the other checks. The
[earlier evidence archive](../c4-named-overlap-balance-2026-11-11/README.md)
is retained unchanged.

`SHA256SUMS` authenticates this directory's files. No mathematical
hypothesis, axiom budget, claim status, or verification gate is weakened.

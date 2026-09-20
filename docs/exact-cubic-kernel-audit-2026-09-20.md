# Auditing the exact cubic kernel — correctness, envelope, cost, 2026-09-20

A pass over the arithmetic the overlap and coincidence work rests on:
`psc/perron_field3.mojo` (exact `Z[beta]` arithmetic and the Perron sign
oracle), `psc/pisot.mojo` (the PIP screen), `finite_linear_algebra/mat3.mojo`,
`psc/automata.mojo`, and the state bound in `psc/pisot_state.mojo`.

Three questions, in order: is it right, what is its domain, and where does its
time go. Everything below is measured or proved; the differential dumps and
their oracles are reproducible from the recipe at the end.

## 1. Correctness: exact, or it raises — never wrong

The kernel's own claim is that every theorem-facing operation is checked and
that a successful run is exact. That was tested against oracles that share no
method with it.

**Small-coefficient sweep.** 20 distinct corpus cubics against a 9^3
coefficient grid: 14,580 `sign_at_perron` verdicts, checked against an exact
rational oracle that isolates `beta` by bisection on `chi` over `(1, B]` and
then brackets `Q` over the isolating interval by its endpoints and vertex.

```
compared: 14580  agree: 14580  disagree: 0  raised: 0
```

**Wide-magnitude sweep.** The harder question is whether the kernel ever wraps
*silently* at large coefficients instead of raising, which would be a
correctness defect rather than a robustness one. 21,620 records over
`sign_at_perron`, `cubic_mul`, `cubic_mul_beta` and `charpoly`, at coefficient
magnitudes `10^2, 10^4, 10^6, 10^9, 10^12, 10^15`, each checked against a
Python big-integer oracle (polynomial product reduced mod `chi`; `c2 = -tr`,
`c1 = sum of principal 2x2 minors`, `c0 = -det`).

| operation | compared | agree | disagree | raised |
| --- | --- | --- | --- | --- |
| `charpoly` | 20 | 20 | **0** | 0 |
| `sign_at_perron` | 2,488 | 2,488 | **0** | 4,712 |
| `cubic_mul` | 4,792 | 4,792 | **0** | 2,408 |
| `cubic_mul_beta` | 7,200 | 7,200 | **0** | 0 |

**Zero disagreements at any magnitude.** The fail-closed discipline holds end
to end: where the kernel answers it is exact, and where it cannot it raises.

Of `cubic_mul`'s 2,408 refusals, 2,406 were *necessary* — the true product
genuinely leaves `Int64`. Only 2 were conservative, and both had a true value
within 13% of `Int64.MAX`, refused because the degree-4 coefficient before
reduction overflowed. That is as tight as the algorithm can be without a
wider intermediate.

Checked by reading, all sound:

- `_checked_mul` refuses a product equal to exactly `Int.MIN` — conservative,
  never wrong.
- The Sturm–Tarski chain starting `P, rem(P'Q, P)` is sound because the
  remainder agrees with `P'Q` at every root of `P`, so the Cauchy index is
  preserved; the omitted pseudo-division scales are positive, so the sign
  variations are unchanged.
- `_perron_integer_bound = max|chi_i| + 1` is a valid Cauchy bound, and for a
  Pisot cubic `beta` is the only root in `(1, B]`.
- `is_pisot_charpoly` case B: `beta |z|^2 = det`, so `|z| < 1` iff
  `det < beta`; the quadratic factor `(t-z)(t-z_bar)` is positive on all of
  `R`, so `sign chi(t) = sign(t - beta)` and the test is `chi(det) < 0`. Its
  precondition — irreducibility, which is what excludes a root at exactly 1 —
  is discharged by every one of its three production callers.
- `charpoly` by Newton's identity `c1 = (t1^2 - t2)/2` agrees with the
  principal-minors formula on all 20 corpus cubics.
- `is_primitive` checks `M^1..M^5`; Wielandt's exponent for `n = 3` is
  `n^2 - 2n + 2 = 5`.

## 2. The envelope: one stated bound is not the effective one

`sign_at_perron` decides coefficients up to roughly `2 * 10^6` and raises past
that. On the family `beta^2 - p beta + p` over `x^3 - x - 1`, bisection puts
the exact threshold at **458,007**. The binding term is `A * A * A * c * c` in
`_quadratic_terminal_sign`'s terminal resultant `R`, which is a cubic form in
`(A, B, C)` with `A, B, C` linear in `Q`'s coefficients — so the chain costs
one cube of the input range.

**This never bites in practice.** Instrumenting every call:

| driver | `sign_at_perron` calls | largest coefficient seen |
| --- | --- | --- |
| coincidence-formula-census | 23,762,617 | **66** |
| overlap-contracting-census | 278,662 | **36** |

Four orders of margin. But one guard does not say so:

> **`ENTRY_BOUND = 1 << 52` in `psc/pisot_state.mojo` advertises a domain
> about `2 * 10^9` times wider than the kernel can decide.**

A state that passes that guard with entries near `2^52` yields a `CubicElt`
far outside anything `sign_at_perron` can settle, so the run raises anyway.
Nothing wrong is ever returned — the failure is closed — but the bound named
in the source is not the bound that governs. Either document the effective
ceiling beside it, or route the refusal as in §4(ii), which removes it.

## 3. Where the time goes: 60% of the hot primitive was wasted

`sign_at_perron` is the hot primitive of the coincidence census: 23.76M calls
in a ~58s run. Classifying each call by the cheapest method that would have
sufficed:

| class | calls | share |
| --- | --- | --- |
| coefficients all of one sign | 7,535,437 | 31.7% |
| endpoint bracket over `[1, B]` | 6,724,655 | 28.3% |
| genuinely needs the remainder chain | 9,502,525 | 40.0% |

Three in five calls built a degree-5 resultant they did not need.

## 4. What changed, and what is left on the table

### Landed — both behaviour-identical, both measured

**(a) A two-step shortcut in `sign_at_perron`.** Before any remainder is
built: if the coefficients are all of one sign the answer is that sign, since
`beta > 1 > 0`; otherwise, if the vertex of the quadratic falls outside
`(1, B)`, the two endpoint values bound `Q` over the whole enclosure and a
bound excluding zero proves the sign. Both are exact and one-sided — a `0`
return means *undecided here*, never *zero* — and neither can narrow the
decidable domain: the first does no arithmetic at all, and the second falls
through on an overflow the authoritative path is free to report itself.

Paired alternating runs of the coincidence census, same container:

| run | baseline | shortcut |
| --- | --- | --- |
| 1 | 56.70 s | 50.31 s |
| 2 | 59.56 s | 50.46 s |
| 3 | 58.90 s | 47.89 s |
| **mean** | **58.39 s** | **49.55 s** |

**−15.1%**, with every pair favouring it. Census output byte-identical.

**(b) A hash index in `psc/automata.mojo`.** `_subset_index` and `minimised`
both scanned a `List[String]` linearly, and `minimised`'s inner loop had no
early exit, so it always scanned the full class list. Both are now
`Dict[String, Int]`. Indices are still assigned by first encounter, so the
automata are *identical*, not merely language-equal — which is what the new
regression pins.

| numeration-conversion-census | scan | hash |
| --- | --- | --- |
| `PROJECTABLE = 200` (shipped) | 11.58 s | 10.95 s |
| `PROJECTABLE = 1500` | 21.78 s | 18.79 s |

Both changes are guarded by new regressions: four in
`tests/test_exact_interval.mojo` (including a 2,184-case differential of the
fixed-width oracle against the unbounded rational one, and the envelope of
§2 pinned as *refuses*, never wraps) and one in `tests/test_automata.mojo`.
All 39 test files, `verify.mojo`, and every pinned census line pass unchanged.

### Not landed — two measured recommendations

**(i) `PROJECTABLE = 200` is over-conservative by measurement.** The census
comment argues the letter-map projection "costs the conversion's size
squared", and the cap leaves 27 specimens unverified. The constant is small
enough that it does not:

| `PROJECTABLE` | letter maps carried across | too large | seconds |
| --- | --- | --- | --- |
| 200 (shipped) | 88 | 27 | 10.9 |
| 400 | 107 | 8 | 13.9 |
| 800 | 112 | 3 | 16.0 |
| **1500** | **115** | **0** | 18.8 |

Full coverage costs **+8 seconds** and reports 13,800 letter verdicts with 0
mismatches. It is left for a decision rather than taken, because it widens
what the census claims and needs the two `grep -Fx` pins at
`.github/workflows/ci.yml:287,289` moved with it.

**(ii) The rational-interval layer has no production caller.**
`psc/perron_interval.mojo` answers the same sign question over unbounded
`finite_exact` rationals. Its only importer is its own test. On the family of
§2:

| `p` | fixed-width chain | interval layer |
| --- | --- | --- |
| `10^5` | decides (`-1`) | `-1` |
| `10^6` | **raises** | `-1` |
| `10^8` | **raises** | `-1` |

Routing the *refusal* case to it makes `sign_at_perron` a four-rung ladder —
coefficient signs, integer bracket, remainder chain, rational enclosure — in
which the ceiling of §2 disappears and fail-closed is preserved, because the
enclosure returns "undecided" rather than a guess, so an unresolved bracket
re-raises. Not taken here: it widens the kernel's contract, and at a largest
observed coefficient of 66 nothing in the corpus demands it. It becomes the
obvious move the moment a driver works with powered substitutions or larger
digit alphabets, where the coefficients are not bounded by 66.

## How this was measured

- **Differential dumps.** Two Mojo drivers outside the repository tree (Mojo
  resolves `psc.*` from anywhere with `-I .`) print one record per operation —
  inputs, and either the kernel's answer or `RAISE`. Python checkers replay
  every record against big-integer oracles. A refusal is classified by asking
  whether the true value fits in `Int64`: if it does the refusal was
  conservative, if not it was necessary.
- **Call counts and coefficient ranges.** `sign_at_perron` temporarily prints
  one line per call; the census is run and the lines aggregated. The
  instrumentation is reverted before anything is committed.
- **Timings.** Paired alternating runs on one container, never against CI
  numbers, per the discipline of
  `docs/census-performance-handoff-2026-09-18.md`: a probe must print an
  aggregate depending on every value it computes, or the work is optimised
  away and the layer measures as free.

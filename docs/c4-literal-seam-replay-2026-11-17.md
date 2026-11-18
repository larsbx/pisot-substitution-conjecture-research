# Literal occurrence replay of one-track seam returns

**Status:** Bounded executable cross-check of the one-track seam inputs.
The strict-component spectral identification remains conditional, and the
uniform neutral-weight exclusion remains open. This note does not register
or promote a governed claim.

## Targeted literature stop/go check

The target is the explicit verification gap in [the seam-spectrum
note](c4-one-track-seam-spectrum-2026-11-17.md): its independent comparison
multiplies counts of periodic interior states, endpoint letters and legal
seams. Equal counts alone do not identify the actual cells or occurrences.
The proposed replay enumerates literal self-occurrences and compares full
labelled offsets and ordered adjacent-cell identities.

The following primary sources were inspected before implementation:

| Source | Relevant construction and boundary |
| --- | --- |
| [Barge–Diamond, §§2–3, Theorem 4](https://arxiv.org/pdf/math/0702669) | Legal two-letter words give transition edges. The last/first-letter map acts on them, and its eventual range has both component and cycle information. Endpoint compatibility alone is insufficient to declare a bigram legal. |
| [Baker–Barge–Kwapisz, §4 and Remark 4.3](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | Same-class integral edge states and actual coincidence are the geometric objects. Finite state or occurrence agreement does not supply the universal coincidence assertion. |
| [Barge, §3, Lemma 21 and Theorem 22](https://arxiv.org/pdf/1301.7094) | Periodic allowed words and asymptotic boundary information enter cohomology restrictions. The rank-two theorem retains its Pisot and odd-norm hypotheses; it does not exclude every neutral odd eigenvalue. |

**Decision: proceed with the existing contract at a narrower evidence scope.**
This is a literal-word verification of the published-in-repository seam
construction, not a new spectral theorem. Preserve the productive
`01/12/021` control with positive correction at minus one. Do not assert
nonpositivity of every seam correction, strict-joining membership of every
product pair, or property (F) from a finite list of powers.

## Work shown

### Assumptions and hypotheses

The comparison uses the four named unit PIP3 substitutions of the seam note
and the complete overlap boxes supplied by `PeriodicOverlapGraph`.
The independent constructor consumes the substitution words and a positive
power, not the overlap rows, the zero-fibre catalogue, its cycle lengths, or
the last/first seam-saturation procedure. All offsets are bottom minus top.
The inherited `PrototileMap` input gate admits original images of at most
six letters. This is separate from the 100,000-letter bound on expanded
images; all four fixtures satisfy both. Replay helpers consume the
constructor's actual expanded words and do not independently authenticate
arbitrary caller-supplied images against a source substitution and power.

### Derivation / reduction

For every expanded word `sigma^n(b)`, scan every self-occurrence
`P b Q` with both `P` and `Q` nonempty. Solve

\[
(M^n-I)v=\operatorname{Parikh}(P)
\]

and retain exactly the integral solutions. The inventory records `n`; each
interior record keeps `b`, its actual ordinal, the prefix vector and `v`.
The equation and the
original word replay the record. Since the substitution has positive
Perron lengths and expansion greater than one, the nonempty prefix and
suffix imply `0 < ell(v) < ell_b`.

A fixed first letter `c` yields the cell `(c,b,-v)` with top ordinal zero.
A fixed last letter `a` yields `(a,b,e_a-v)` with the actual last top
ordinal. Their original prefix equations give the same cell after `n`
inflations. A legal top bigram `ac`, whose last and first letters return,
yields the ordered seam

\[
(a,b,e_a-v)\mid(c,b,-v).
\]

Both cells retain the same bottom interior occurrence. Legal bigrams are
enumerated separately by expanding all three letters and retaining their
actual adjacent positions until the cumulative pair set stabilizes. For a
primitive nonerasing substitution every letter occurs among the expanded
images at each level. Thus the next pair set is the internal one-step
pairs together with last/first images of the previous pairs; stabilization
is complete. Each accepted bigram keeps its first literal witness.

The comparison checks bijective sets of these endpoint cells and ordered
seam pairs against the fixed nodes of the canonical maps. A return at
power `n` is included once even when its minimal period divides `n`.
First-endpoint, last-endpoint and whole-seam populations remain separate.

**Arithmetic bound.** The constructor caps each expanded image at at most
100,000 letters and constructs `M^n` by counting those actual words.
Writing `B=100001`, entries of `M^n-I` have magnitude at most `B`, its
cofactors at most `2 B^2`, and every determinant or
adjugate-times-prefix intermediate at most `6 B^3 < 2^63-1`.
The existing integer-matrix kernel is therefore used within a proved
machine range, including when a solution is rejected as nonintegral.
Accepted solutions are additionally checked by the vendored checked
matrix-vector operation. No arithmetic package is copied or modified.

### Evidence and replay

The implementation is `kernel/psc/literal_seam_replay.mojo`, and its
regression is `kernel/tests/test_literal_seam_replay.mojo`. All 48
specimen/power comparisons pass with the repository-pinned Mojo runtime.
Each compares all first-endpoint cells, last-endpoint cells, ordered seam
pairs and integral interior states; it also checks for duplicates and
replays every original occurrence and legal-bigram witness.

| Ordered images | Powers checked | Powers with nonempty seam populations |
| --- | --- | --- |
| `01/12/021` | 1–12 | 6 |
| `1/02/202` | 1–12 | 6 |
| `1/2/021` | 1–12 | 0 |
| `01/02/0` | 1–12 | 0 |

```sh
cd kernel
pixi run --locked mojo run -I . -I tests tests/test_literal_seam_replay.mojo
pixi run --locked mojo run -I . -I tests tests/test_one_track_seam_spectrum.mojo
pixi run --locked mojo run -I . -I tests tests/test_periodic_overlap_returns.mojo
```

The existing seam and periodic-overlap regressions also pass. The
[evidence packet](../evidence/literal-seam-replay-2026-11-17/README.md)
retains source hashes and logs. No new whole-library Lean or full Mojo
suite execution is implied. An independent automated review checked the
completeness argument and arithmetic bounds; human review remains pending.

### Negative controls

Fourteen checks refuse the affected comparison: same-size endpoint
replacement, duplicate endpoints, reversed-seam identity comparison,
reversed-seam occurrence replay, duplicate seams, altered prefix,
same-letter occurrence substitution, shared boundary, changed endpoint
ordinal, illegal bigram, excessive arithmetic scope (`word_cap=100001`),
word-cap exhaustion, record-cap exhaustion and power zero. The upper
arithmetic guard is load-bearing for the determinant and adjugate bound.
Empty populations remain finite checks; the positive seam control supplies
a nonempty comparison.

### Non-claims / remaining gaps

This replay concerns full boxes on the declared productive specimens.
It does not construct a strict PIP3 sink, decide the coincidence rank,
prove the conditional bigon-to-overlap trace identification in Lean, or
verify the seam spectrum at every power. Selection of an actual strict
joining still needs its own membership evidence. The remaining uniform
obligation is a bound on the corrected odd multiplicity relative to the
required neutral defect rank in every literal candidate sink, or another
literal constraint excluding such sinks. A1′, BH, C4 and PSC remain open.

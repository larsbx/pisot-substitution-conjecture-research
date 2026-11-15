# C4 actual descendant spans and fixed-row escape

The complete ordered descendants of any nonempty balanced ternary word pair
have full rational Parikh span in **every consecutive three-level window**, provided
the rational incidence characteristic polynomial is irreducible. A nonzero
fixed rational row therefore detects a literal descendant occurrence in that
window. The witness records both its depth and its list ordinal.

The Lean module is
[`DescendantSpan.lean`](../proof/PscVerif/PscVerif/DescendantSpan.lean), namespace
`Psc.DescendantSpan`. This is a deductive specialization of the
[existing two-generation span argument](c4-two-generation-parikh-span-2026-11-02.md),
including that note's consecutive-window observation. It does not claim a new
cyclic-vector theorem or establish the missing common row in the C4 proposal.
The [pre-code stop/go](c4-finite-carrier-dual-literature-2026-11-10.md), branch B,
records the primary-source review and the decision to formalize this precise
scope.

## Work shown

### Assumptions and hypotheses

For an alphabet `α`, a word is a `List α`, and a word pair is an ordered pair
of lists. The substitution is an arbitrary function `s : α → List α`.
Let

\[
  M_{ac}=|s(c)|_a,
  \qquad p(T)_a=|T_{\rm top}|_a,
\]

with counts cast to `ℚ`. The definitions `incidenceQ`, `parikhQ`, and `mass`
reuse `Psc.Incidence.inc` and `Psc.ParikhIntertwiner.parikh`; they do not
introduce another reduction or population-count convention.

The mass identity requires only a finite alphabet with decidable equality
and a balanced source pair:

\[
  \operatorname{Equiv1}(T_{\rm top},T_{\rm bottom}).
\]

The source need not itself be an irreducible balanced block. Empty images are
allowed in this identity. Depth zero is the one-element list `[T]`, even when
`red T.top T.bottom` has several factors.

The span and detection statements additionally assume:

1. `α = Fin 3`;
2. `T.top ≠ []`;
3. `Irreducible (incidenceQ s).charpoly` over `ℚ`.

There is no finite carrier, legality, SCC, primitive, Pisot, positive-length,
unimodular or separately supplied nonerasing premise. An independently
provided strict carrier can contain the witness through actual child closure;
the local theorem does not need such a carrier.

The word **fixed** in “fixed row” is essential: the same `f : Fin 3 → ℚ`
must be used on all levels in the window. A different row at each level is
outside the statement.

### Derivation / reduction

#### 1. The complete ordered mass sum

`Psc.Descendants.descR s n T` follows the full child relation. Every child
is retained in its original order, repeated equal factors occur repeatedly,
and coincidence blocks continue to inflate. The first theorem is

\[
  \sum_{U\in\operatorname{descR}(s,n,T)}p(U)=M^n p(T).
  \tag{1}
\]

This is `mass_sum_descR`. The summation is over a **list**, not over its
deduplicated support.

At depth zero, (1) is the identity `p(T)=I p(T)`. At positive depth,
`Descendants.descR_succ` identifies the exact descendant list with the complete
reduction of the two iterated source words. `Reduction.red_top` says that
concatenating its top factors recovers the full iterated top word. Parikh
vectors add under concatenation, and `parikhQ_iterate_subst` gives

\[
  p(s^n(w))=M^n p(w).
\]

No support-size estimate, sampled minor, native oracle, or rank assumption
enters this proof. It is literal counting followed by the incidence identity.

#### 2. Three consecutive levels span the whole space

For a given starting level `n`, define

\[
  W_n=\operatorname{span}_{\mathbb Q}
    \{p(U):U\in\operatorname{descR}(s,k,T),\ n\le k\le n+2\}.
\]

The Lean definitions are `windowMasses` and `windowSpan`. A set is adequate
for this span; equation (1) continues to use the complete list with all
multiplicities.

Every summand in (1) at a level in the window lies in `W_n`. Closure under
addition therefore gives

\[
  M^n p(T),\quad M^{n+1}p(T),\quad M^{n+2}p(T)\in W_n.
  \tag{2}
\]

Nonempty words have a nonzero rational Parikh vector
(`parikhQ_ne_zero`). The existing
`Cyclicity.det_ne_zero_of_irreducible` implies `det M ≠ 0`, so
`w=M^n p(T)` is nonzero for every `n`. The already proved
`Cyclicity.cyclic_of_irreducible` says that

\[
  w,\ Mw,\ M^2w
\]

are linearly independent. They are three vectors in a three-dimensional
space, so (2) gives `W_n = ℚ³`. This is `windowSpan_eq_top`.

The determinant step is needed for arbitrary starting level `n`; a nonzero
source by itself would not ensure a nonzero later mass for an arbitrary
matrix. Irreducibility supplies this step within the stated hypotheses.

#### 3. A row detects an actual ordinal

For a fixed rational row `f`, let `L_f(v)=f·v`. If `f` vanishes on every
descendant in the window, `W_n` lies in the kernel of this linear map.
Since `W_n=ℚ³`, evaluate at `v=f`: `f·f=0`, and hence `f=0` over `ℚ`.
This is `row_eq_zero_of_window`.

Its contrapositive, `exists_detecting_occurrence`, returns

\[
  \exists k,j,U:\quad
  n\le k\le n+2,\qquad
  \operatorname{descR}(s,k,T)[j]?=\operatorname{some}(U),\qquad
  f\cdot p(U)\ne0.
  \tag{3}
\]

`List.mem_iff_getElem?` supplies the ordinal of the actual list occurrence.
Thus (3) is stronger as an interface than a statement that some abstract mass
or state label exists. Equal factors at different positions remain distinct
possible witnesses. The `n=0` specialization is
`exists_detecting_occurrence_le_two`.

#### 4. A supplied strict carrier contains the same occurrence

The separate adapter
[`DescendantSpanStrict.lean`](../proof/PscVerif/PscVerif/DescendantSpanStrict.lean)
imports the local theorem and the existing `StrictSystem` definitions. For a
supplied strict system `C` and source `T ∈ C`, its theorem
`Psc.DescendantSpanStrict.exists_detecting_occurrence` returns the same
depth `k`, ordinal `j`, factor `U`, and nonzero row evaluation as (3), together
with

\[
  U\in C,\qquad U_{\rm top}\ne U_{\rm bottom}.
\]

The proof first converts the actual list membership into full child
reachability using `Descendants.reflTransGen_iff_mem_descR`. The existing
`StrictSystem.reflTransGen_mem` then puts the occurrence in `C`, whose
`noncoincident` field gives the final assertion. Neither the list witness
nor the complete descendant graph is pruned or replaced in this step.

The adapter also gives `row_eq_zero_of_carrier`: a fixed row vanishing on
every member of this supplied carrier is zero. It selects any source from
the carrier's recorded nonemptiness and applies the local window theorem.
This is a direct closure corollary, not a new construction of `C` or a new
source of a common row. No geometry modules enter the adapter.

### Evidence and replay

The theorem bodies use the existing complete reduction, incidence,
finite-dimensional span, matrix nonsingularity and cyclicity proofs.
The literal controls are in `Psc.DescendantSpan.Controls` and use kernel
reduction for finite word equalities and exact rational normalization for
row values. There are no new axioms, admitted declarations, or private
theorem-facing declarations in the module.

The local development replay passed with exit code zero and no diagnostics:
the complete new module body was checked against the production
`Descendants` import and verbatim copies of the existing cyclicity and
nonsingularity proof bodies with their narrow Mathlib dependencies. No
statement, hypothesis, or proof body was weakened for that replay. This
development check does not replace the production-import/full-bank receipt.
The complete strict adapter also passed a combined narrow replay against the
same span body and verbatim existing `StrictSystem` structure and
`reflTransGen_mem` proof. Its only notices concerned the existing duplicated
`StrictSystem.StrictSystem` namespace in the helper; the production strict
source already disables that namespace linter.

The production replay from the repository root is:

```sh
cd proof/PscVerif
lake build PscVerif.DescendantSpan PscVerif.DescendantSpanStrict
```

Full-bank build and declaration-audit receipts belong to the integrating
revision; the independent native controls and the bounded model controls
are additional regressions, not premises of the Lean theorem.

### Negative controls

#### Depth two can be necessary, and pruning loses the witness

Take

\[
  s=1/02/202,\qquad T=01/10,\qquad f=(1,-1,0).
\]

The complete lists are:

| Depth | Ordinal | Actual factor | Mass | `f · mass` |
| --- | --- | --- | --- | --- |
| 0 | 0 | `01/10` | `(1,1,0)` | 0 |
| 1 | 0 | `102/021` | `(1,1,1)` | 0 |
| 2 | 0 | `021/120` | `(1,1,1)` | 0 |
| 2 | 1 | `2/2` | `(0,0,1)` | 0 |
| 2 | 2 | `0/0` | `(1,0,0)` | 1 |
| 2 | 3 | `2/2` | `(0,0,1)` | 0 |

`sharp_first_two_levels_vanish` and `sharp_depth_two_ordinal_two` check the
specific loss at the first two levels and the detecting ordinal. The only
detected factor in this depth-two list is a coincidence. Filtering away
diagonal factors removes it; `sharp_pruned_level_vanishes` checks the failure
directly. Consequently the full-descendant theorem must not be transferred
to a graph where coincident children are omitted or made terminal without
another argument.

The recorded native PIP classification and determinant witnesses for this
example are in the preceding
[two-generation note](c4-two-generation-parikh-span-2026-11-02.md). The new
finite Lean controls assert their literal word and row evaluations; they do
not silently reclassify a finite test as the proof of the general theorem.

#### Multiplicity is necessary for the mass identity

The two occurrences of `2/2` in the displayed list both contribute to (1).
The true depth-two mass sum is `(2,1,3)`. Deduplicating the list gives
`(2,1,2)`, which is different. `sharp_multiplicity_matters` checks both exact
values. Set support is sufficient for a span, but it cannot replace the
ordered list in the mass identity.

#### Irreducibility cannot be replaced by the strict-carrier example

For the established reducible calibration

\[
  s=10/102/211,\qquad T=102/210,\qquad f=(1,0,-1),
\]

the masses in levels zero through two are:

| Depth | Masses, in actual list order |
| --- | --- |
| 0 | `(1,1,1)` |
| 1 | `(2,4,2)` |
| 2 | `(2,4,2)`, `(1,1,1)`, `(1,1,1)`, `(1,3,1)`, `(1,1,1)` |

Every mass has equal first and third coordinates. The nonzero row `f`
vanishes on the complete three-level list; `reducible_three_levels_vanish`
checks that fact. The prior calibration identifies the characteristic
polynomial as `(x−1)(x²−2x−2)` and the complete strict carrier. This module's
finite control neither assumes irreducibility nor claims that these three
levels alone establish the carrier.

#### Empty sources have zero mass

At depth zero the empty source is the sole occurrence and has zero mass;
at positive depth its descendant list is empty. `descR_empty_succ` and
`Controls.empty_window_vanishes` preserve this failure of the nonempty-source
premise for every substitution and every rational row.

### Non-claims / remaining gaps

This module rejects a **supplied nonzero common annihilator** of complete
descendant masses. It does not construct that row from phase-flatness,
missing synchronization, a finite mark recurrence, or an additive cut-label
potential. The [current proof obligations](c4-next-proof-obligations-2026-11-10.md),
Candidate B, retain that missing implication.

The [complete-cone audit](c4-complete-cone-rank-hub-audit-2026-11-03.md)
already records full-rank flat PIP cones. Full mass span at depth two therefore
does not imply a synchronizing newborn at depth two. The
[collared-cut analysis](c4-collared-cut-cycles-2026-11-04.md) also prevents
treating a finite scalar potential as the missing nonzero row without new
hypotheses.

The finite-interior-carrier development in the same integrating branch is
mathematically independent. Neither theorem manufactures a common legal
limit, a productive forced-crossing route, or the common functional needed
to connect the two proposed routes. Uniform C4, general G1, Concentration,
and PSC remain open. Independent human review remains pending; verified
exactly scoped dependencies remain usable under the repository's progression
convention.

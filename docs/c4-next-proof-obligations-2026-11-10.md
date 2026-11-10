# C4 next proof obligations — 2026-11-10

**Status:** research roadmap and verification reconciliation. The inspection
baseline is `main@c38e381cc8105d87597b0a9bfbe418b7bca86fc0`, through
[PR #530](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/530).
This note records the next deliverables; it supplies no new universal proof,
finite certificate, or governed claim promotion. General C4, Concentration,
A1′, BH, G1 and PSC remain open. The direct C4 tracker is
[#461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

The primary next formal task is **actual occurrence transport followed by
first-diagonal-to-newborn extraction**. The parallel algebraic task is the
**degree-five reciprocal polynomial and image-rank theorem**. The main new
mathematical target is then a uniform argument forcing at least one productive
physical crossing in a hypothetical fully strict component.

## 1. Accepted inputs and exact verification scope

| Input | Implemented contribution | Remaining boundary |
| --- | --- | --- |
| [#522](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/522) | Ternary degree-five 48-dimensional shuffle-annihilator/Lyndon basis; integral substitution and signed child identities under degree-four balance; defect columns in the Lie span. | Lower-degree balance is required on every state. |
| [#524](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/524), [#525](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/525), [#527](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/527) | Equivariant quotient-to-image transport, mixed Lie weights, and lifting roots of the actual image polynomial to nonzero image eigenvectors. | A source eigenvalue in the defect kernel is not an image eigenvalue; numerical collisions of weights do not identify their content spaces. |
| [#528](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/528) | Signed Perron sieve, full reciprocal root orbit, and determinant-cube necessary bound. | Reciprocal multiplicities/rank and literal strict-child realizability remain separate obligations. |
| [#531](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/531) | Orientation-safe finite controls and generic relational Lean path/closed-set lemmas. | The actual occurrence, common-factor and newborn arguments remain prose. |
| [#529](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/529), [#530](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/530) | Productive PIP crossings without the nominated left alignment, then without either endpoint alignment. | These productive controls fail fully strict child closure. They refute proposed intermediate routing rules, not C4. |

At the inspection baseline, the
[exact-main Lean job](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42768131163/job/129669358430)
compiled the whole proof bank, including `Degree5Sieve`, and audited **4,048
declarations and 3,070 theorems**, with all named proofs reached. Its new sieve
theorems use the listed standard axioms `propext`, `Classical.choice` and
`Quot.sound`. This supersedes the earlier local exit-137/pending-integrated-build
description on #528. The accepted #528 head is
`0f0043c98c69313ac927f7640e85ca12e882e00e`; its
[whole-bank workflow](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42743831329)
also succeeded.

At #530 head `5b7b4bbb30c8199911cc5ed3bf18863a49026ec1`,
[C4 recurrent flat exits](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42765452559)
passed canonical Mojo replay, the independent oracle, and the standalone
orientation-safe Lean check. That Lean check validates the generic relational
reduction, not the still-prose occurrence-to-factor argument.

The same baseline's
[Python integrity job](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/42768131163/job/129669358400)
had one failure, `test_every_evidence_packet_is_pinned`, with 1,654 tests passed,
five skipped and six subtests passed. Of 131 top-level evidence directories,
only `evidence/c4-orientation-safe/` lacked `SHA256SUMS`. This documentation
change supplies that missing manifest over the existing `OrientationSafe.lean`
bytes. Historical failed runs remain evidence of the earlier tree; acceptance
of this change requires its own revision's checks. The unrelated source-pin
redesign [#526](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/526)
does not supply this manifest.

## 2. Next formal bridge: actual occurrences to a one-step newborn

### Input contract

Use a **supplied finite, nonempty, strict child-closed SCC of actual
irreducible balanced pairs** for a ternary primitive irreducible Pisot
substitution. Retain complete ordered child factorization and the genuine
Barge–Diamond witness used by the endpoint/hub reduction. The supplied
component hypothesis does not establish global G1 extraction.

A marked overlap carries both selected occurrences and their full addresses,
source letters, exact residual Parikh vector, physical track order,
normalization signs, parent state, ordered child-factor ordinal, and strict
interior/boundary classification. Use the existing residual convention and
affine transport of the
[ordered-word contract](c4-ordered-word-completion-interface-2026-11-02.md).
Legal contexts must be derived where required; legality of arbitrary swap
seeds or all state words is not an additional standing assumption.

### Required lemmas

1. **Common-factor transport.** Complete balanced factorization partitions
   the two tracks into the same physical intervals. An actual child-tile
   overlap with a common positive-length interior therefore lies in one
   common factor interval. Prove that its occurrence addresses, residual,
   orientation and child ordinal transport to that factor.
2. **Packet refinement.** Prove soundness of accepted packet transitions
   against actual occurrences and completeness relative to the explicitly
   declared occurrence universe as separate statements. Account for split
   descendants and terminal misses. A later use of infinite abstract paths
   needs a separate consistent-lifting argument.
3. **Perron injectivity at cuts.** Formalize the existing cubic-irreducibility
   argument converting equality of Perron lengths of integer Parikh columns
   into equality of those columns. Do not add independence as an axiom.
4. **First diagonal gives a newborn.** The first diagonal on an actual marked
   path is a singleton coincident child in its immediate noncoincident
   irreducible parent. At least one singleton boundary is interior; it gives
   `Sync_+` or `Sync_-` at a one-step newborn cut of that parent.
5. **Strict-closure contradiction.** Compose these concrete statements with
   `C4Orientation.strict_excludes_productivity`, preserving membership of
   every transported parent in the supplied component.

The endpoint side, track order and newborn side are distinct fields. A
right-end route can produce a `Sync_+` newborn. A direct diagonal route is
also a valid input to extraction. The current
[orientation-safe note](c4-orientation-safe-transfer-2026-11-09.md) contains
the prose proof; its generic Lean file is the starting point, not the full
formalization of these five statements.

**Acceptance:** Lean statements over the actual definitions, kernel/axiom
replay, canonical Mojo occurrence receipts, and independent oracle checks of
the existing controls. Quint should expose bounded failures of weakened
transition/quantifier contracts. Bounded model replay does not replace the
universal Lean implication. Preserve the existing degree-four interfaces.

## 3. Uniform target: one productive forced crossing

After the endpoint and hub reductions, let `F(C)` denote the actual physical
crossings forced in a remaining hypothetical component `C`. The useful
candidate theorem has the quantifiers

\[
\forall C\text{ under the full strict PIP and hub hypotheses},\quad
\exists x\in F(C),\quad
\exists\text{ an actual occurrence path from }x\text{ to a diagonal}.
\]

The next formal bridge converts that path into the literal interior newborn.
The theorem is uniform in the size of `C`. It needs neither productivity of
every forced crossing nor termination of every possible path.

For a fixed root, no diagonal route is equivalent to a successor-closed,
diagonal-free set containing it. `no_route_iff_closed_avoiding` already proves
this relational equivalence without a graph-finiteness assumption. Full
strict child closure transports the forced crossing into such an avoiding
lift. **The open step is to rule out that lift for at least one forced
crossing under the actual PIP and ancestry hypotheses.** A finite sink-SCC
certificate is one sufficient mechanism when its complete occurrence graph
and coverage are proved; the graph equivalence alone supplies no exclusion.

### Why a nominated good-edge visit cannot be the required target

For `01/20/200`, the actual pair `(01200,20001)` has two complete flat,
noncoincident factor generations. Its nominated good pair `{1,2}` is
witnessed on both ends. Nevertheless the first crossing has a complete
73-state, 152-edge occurrence graph with neither alignment of that pair in
either track order. A direct diagonal is reached at depth five and yields
`Sync_+` at local cut six. Diagonals in the third factor generation prevent
this from being a fully strict closed component. The
[#530 control](c4-both-end-route-obstruction-2026-11-09.md) therefore removes
an overstrong intermediate routing requirement while preserving the direct
diagonal target.

### Candidate A: realizable hierarchy recurrence

Use the existing [legal ancestry towers](c4-legal-ancestry-towers.md) and
[relative hierarchy offsets](c4-relative-hierarchy-offset.md). Seek a theorem
that a repeated realizable relative state either forces a diagonal/newborn or
produces incompatible recognizable decompositions of the **same legal limit
configuration**. Prove consistent realization before invoking a pumping or
compactness step. Repeated finite states and separate legal contexts do not
identify a common configuration, and recognizability of each hierarchy alone
does not synchronize their boundaries.

This is the useful place for the Penrose-style hierarchy analogy: preserve
interface ancestry through supertiles and investigate persistent mismatch.
The [Penrose bridge program](bridges/penrose-2d-to-psc-interface-program.md)
is a source of candidate mechanisms, not a supplied PSC premise. A geometric
import must respect non-unit coordinates and the exact named target.

### Candidate B: a common descendant-Parikh annihilator

Independently test #461's proposal that complete phase-flat strict closure
forces one nonzero rational functional annihilating all relevant descendant
Parikh columns. Such a functional would contradict the established
[rank-three descendant span](c4-two-generation-parikh-span-2026-11-02.md).
The missing work is deriving a single functional and transporting it across
every actual child occurrence. The existing rank-three, two-generation flat
PIP control forbids replacing that work with a short-depth rank inference.

Keep these two candidates independent until a proved transfer connects them.
An exact counterexample to either proposed intermediate lemma is a useful
outcome and should record its first failed premise.

## 4. Parallel degree-five completion and realizability

Let the incidence roots be `r0,r1,r2`, set `d = det M = r0 r1 r2`, and write
the incidence cubic as `t^3 - e1 t^2 + e2 t - d`. Let `Q5` be the actual
degree-five defect map and `q5` the characteristic polynomial on its rational
image. Retain all hypotheses of `Degree5Sieve`, particularly degree-four
balance on **every** child-system state.

The accepted sieve classifies each image root as `d^2/ri`; a nonzero image has
all three roots. When the image is nonzero, it also proves
`|det M|^3 <= beta`. The next narrow Lean
deliverable is the factorization

\[
g(t)=t^3-d e_2t^2+d^3 e_1t-d^5,\qquad
q_5=g^k,\qquad \operatorname{rank}Q_5=3k.
\]

This is a proposed formal completion. The existing note gives the argument:
the symmetric functions of `d^2/ri` give `g`, and
`Q(d^2/ri) = Q(ri)` gives irreducibility. Rational factorization then fixes
the multiplicities. Include `k=0` for the zero image and derive positive `k`
only from an actual nonzero column. The source characteristic polynomial
cannot substitute for the image polynomial.

A second proposed formal corollary is
`beta < |det M|^3 -> Q5 = 0`, obtained by contradiction from the accepted
nonzero-image bound. In particular, `|det M| >= 2` and `beta < 8` exclude a
nonzero degree-five image under the same child-system assumptions. These
arithmetic exclusions are not C4 closure.

After this bounded formal task, prioritize actual word realizability. The
[spectral transport note](c4-degree-five-spectral-transport.md) gives the
plastic-cubic abstract control with reciprocal polynomial `t^3+t^2-1` and a
nonzero invariant Lie subspace satisfying the scalar bound. It supplies no
literal strict child carrier. A useful new invariant must inspect ordered
first cuts, balance of every state, complete child closure, or occurrence
data that the abstract control lacks.

Preserve the older frontiers: degree three's determinant sector, degree
four's configuration (R), and higher first-defect degrees still need their
own realization/coverage arguments. Generic degree-six-and-higher
defect/Lie/sieve formalization and the `StrictSystem` first-defect wrappers
beyond degree four remain separate work. Concentration concerns the `K2=0`
branch; the nonzero-`K2` branch also remains relevant to the SCC programme.
See the [Concentration inventory](c4-concentration-attack-2026-11-06.md) and
[canonical ledger](conjecture-ledger.md). Repeating isolated degree-six,
degree-seven, etc. basis computations should wait for a concrete downstream
word argument that uses them.

## 5. Adversarial controls and evidence boundaries

| Retained control | Rejection layer / implication being tested |
| --- | --- |
| [#530 `01/20/200`](c4-both-end-route-obstruction-2026-11-09.md) | A productive forced crossing can avoid either alignment of a nominated good pair. It fails complete strict closure. |
| [#529 `1/02/002`](c4-good-edge-route-obstruction-2026-11-09.md) | The left-aligned nominated edge can be unreachable while a right route and a direct diagonal exist. |
| [`01/12/021`, saturated rank three and two flat generations](c4-two-generation-parikh-span-2026-11-02.md) | Rank and flat phase do not force synchronization by depth two. |
| [Productive PIP packet cycle with offsets `0 -> 1 -> 0`](c4-ordered-word-completion-interface-2026-11-02.md) | Existential productivity can coexist with avoiding cycles; blanket monotone-offset/all-path termination is too strong. |
| [Strict reducible/non-Pisot and literal G/F controls](c4-ordered-word-completion-interface-2026-11-02.md) | Preserve the exact PIP and literal factorization hypotheses; aggregate algebra and endpoint masks are insufficient. |
| [Equal source-prefix Parikh data with distinct parents](c4-cut-attractor-window-2026-11-05.md) | Zero source defect alone does not identify parent tiles. |
| [Legal ancestry and finite offset controls](c4-relative-hierarchy-offset.md) | Local legality, finite states and recurrence alone do not exclude a strict avoiding lift. |
| [Degree-five plastic reciprocal control](c4-degree-five-spectral-transport.md) | Scalar spectral bounds permit an abstract survivor; literal child realizability is additional information. |

Use the canonical Mojo corpus/child machinery and an independent oracle where
it adds value. Searches must be deterministic and report caps, coverage and
the first failed premise: PIP, realization, factorization, closure, strictness,
the proposed invariant, or its conclusion. An exhausted budget is
inconclusive. Another passing finite corpus is not a uniform theorem.

## 6. Integration order and acceptance

| Order | Deliverable | Acceptance condition |
| --- | --- | --- |
| 1 | Evidence-manifest repair and frontier reconciliation (this change). | Existing packet bytes pinned; document/provenance checks pass; stale pending statements corrected against recorded jobs. |
| 2 | Actual occurrence transport and first-diagonal-to-newborn formalization. | Lean theorem with the concrete address/factor definitions, exact replay and all negative controls at their proper rejection layer. |
| 3, independently of 2 | Reciprocal polynomial/multiplicity and degree-five rank theorem. | `q5=g^k`, `rank Q5=3k`, zero-image handling and determinant exclusion under unchanged hypotheses. |
| 4 | Uniform forced-crossing exclusion. | A theorem for arbitrary supplied component size, or a literal reproducible counterexample to the precise intermediate claim. |
| 5 | Compose the successful bridge into C4. | Every input/output type, quantifier, realization premise and dependency is discharged; global extraction stays separate. |

Reconcile open [#497](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/497),
[#509](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/509),
and [#510](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/510)
against current main before using their finite-overlap or R3/R4 scaffolds.
Retain R1/R2 adversarial and R3/R4 independent interfaces as recorded in
[#511](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/511).
Finite mass loss, a quotient kernel, or prefix-seeded returns become C4 inputs
only through their proved literal transfer premises.

For the supplied-component route, G1/renewal extraction remains separate.
The conditional implication from universal aligned coincidence is preserved
in [the C4 definition note](c4-finite-domain-closure-2026-11-05.md), with its
open aligned premise tracked through #138. The one-way
`C4 -> C3-local -> C2 -> SCC Producer` chain does not turn C4 alone into PSC.
Preserve the non-unit, legality, independence and realization boundaries of
the canonical ledger. Human review remains final validation debt rather than
a research-progress gate.

This planning/inventory change introduces no mathematical implementation.
New theorem-facing code must perform the targeted literature stop/go check
required by `AGENTS.md`, use Lean for universal deductions and Quint for
bounded adversarial models, and follow the canonical Mojo implementation
policy. Existing pinned evidence is retained; no archive or theorem status
is rewritten to make a check pass.

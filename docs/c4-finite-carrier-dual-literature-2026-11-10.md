# C4 finite occurrence carriers and descendant duals: stop/go

**Decision, 2026-11-10: proceed with two independent finite-word reductions.**
This note precedes their new theorem-facing source and controls. The base is
`main@35b4d4101d36288f41f7cb04851f4bf98e0092c5`, the merge of
[PR #534](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/534).
The new work must preserve its distinction between actual occurrence
realization, uniform productive-route existence and global extraction.

## Sources and transferred hypotheses

| Primary source inspected | What transfers; what does not |
| --- | --- |
| Barge–Diamond, [*Coincidence for substitutions of Pisot type*](https://www.numdam.org/item/10.24033/bsmf.2433.pdf), Theorem 1 and the geometric substitution construction. | The good letter pair and inflation of actual labelled segments motivate the C4 crossing interface. The theorem supplies neither a common rational functional on block masses nor productivity of an arbitrary forced overlap. Keep the full Pisot hypotheses whenever using that good-pair result. |
| Martensen, [*A Generalized Balanced Pair Algorithm*](https://arxiv.org/html/math/0309194v1), §2 and §3. | Population vectors transform by the incidence matrix; balanced-pair iteration substitutes and completely reduces each occurrence. These literal counting laws transfer without legality assumptions. Dynamical conclusions about allowed sequences or tiling flows retain their own hypotheses. Reducible examples do not supply irreducible-incidence conclusions. |
| Akiyama–Lee, [*Algorithm for determining pure pointedness of self-affine tilings*](https://arxiv.org/html/1003.2898v1), the overlap and inflated-overlap definitions and §4. | Real overlaps have intersecting interiors and inflate through actual digit occurrences. In one dimension, a positive common inflation scale lets a point avoid the finitely many child boundaries. Multiplicities remain relevant to a weighted graph. The paper's spectral criteria require a tiling and Meyer hypotheses; a supplied finite balanced-pair carrier alone does not supply them. |
| [Mathlib characteristic polynomials](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.html), the pinned finite-type/list sources, and the repository's `Cyclicity.lean`. | Cayley–Hamilton, finite images and finite recurrence are standard tools. The existing `cyclic_of_irreducible` is the checked algebraic input. New claims are the specialization to actual ordered descendants and marks, not novelty for cyclic vectors, finite pigeonhole arguments or interval subdivision. Acceptance uses the pinned local sources, not the current online documentation. |

The existing side ledger already rules out using mere finite recurrence,
finite cut-label potentials, or two flat generations as the missing C4
contradiction. The two reductions below do not revive those claims.

## A. Finite actual interior support and successor existence

For a supplied finite carrier `C` of actual word pairs, index every mark by
its actual letter position. The packet image is finite, with cardinality at
most

\[
  \sum_{U\in C}|U_{\rm top}|\,|U_{\rm bottom}|.
\]

Filtering for strict physical interior overlap gives the finite interior
support. Repeated packet labels may be identified for membership, while
actual marks and digit witnesses remain distinct occurrence data. No
weighted-adjacency multiplicity theorem follows from set membership alone.

For positive letter lengths `ℓ`, positive scale `β`, and the exact equations

\[
  \operatorname{length}_{\ell}(\sigma(a))=\beta\ell(a)
  \quad\text{for every letter }a,
\]

prove that every strict interior packet has an interior digit successor.
Scale its open overlap interval, remove the two finite sets of image-word
boundaries, and locate the selected point in both actual image words.
The previously proved affine identity then gives the independent digit
edge. The scaling equations imply nonempty images; no separate global
nonerasure assumption is needed for this statement.

Compose with the existing actual-child lift and supplied strict-system
closure. The resulting finite interior support is closed, every member has
a successor, and no member is diagonal. A finite recurrence consequence
must use actual compatible marked occurrences, or state explicitly when it
only concerns packet labels. It does not create a shared legal limit
configuration, synchronize two recognizable hierarchies, or prove a
productive route exists. A weighted physical-mass identity and exact
production graph serialization retain separate interfaces.

**Necessary negative:** positivity of `ℓ` and nonerasure alone are
insufficient. For `σ=1/012/1`, source `01/10`, selected indices `(0,1)` and
the wrong positive row `(2,1,1)`, the selected source intervals are
`[0,2]` and `[1,3]`. Their selected singleton images occupy `[0,1]` and
`[4,5]`; no interior successor exists. The correct row `(1,2,1)` has scale
`β=2`. A second direct control is `σ(0)=000, σ(1)=1` with unit lengths:
indices `(1,1)` in `0011/1100` overlap before inflation, but their images
occupy `[3,6]` and `[1,2]`.

Retain boundary-contact, erased-image, omitted-child and productive-cycle
controls. Native `TargetPacket.interior` denotes an interior left factor
boundary, not the geometric `Packet.Interior`; tests must not identify them.

## B. Actual descendant mass and fixed-row escape

For any balanced pair with nonempty top word, retain every occurrence in
the complete ordered `descR` list, including repeated factors and continued
inflation of coincident blocks. Prove the all-depth identity

\[
  \sum_{U\in\operatorname{descR}(\sigma,n,T)}p(U)=M^n p(T).
\]

At depth zero the list is the single whole source pair, even when that pair
is reducible. The identity permits erasure and needs no finite carrier.

Under rational irreducibility of the ternary incidence characteristic
polynomial, `M` is invertible and every nonzero rational column is cyclic.
Consequently each consecutive three-level window `n,n+1,n+2` spans `ℚ³`.
Every nonzero fixed rational row therefore detects an actual occurrence in
that window. The witness must include its depth and actual list ordinal.
At `n=0`, this gives the local depth-at-most-two rejection of a common
annihilator. Supplied child closure transports such a witness into its
actual carrier.

This specializes the existing
[two-generation spanning argument](c4-two-generation-parikh-span-2026-11-02.md)
and its recorded consecutive-window observation. It needs no primitivity,
Pisot spectrum, legality, SCC, unimodularity or new independence axiom.
It does **not** derive a nonzero row from phase-flatness. That proposed
derivation remains the missing part of the common-annihilator route.

**Required controls:** for `1/02/202` and source `01/10`, the row
`(1,-1,0)` vanishes on depths zero and one but detects the depth-two
singleton `0/0`. Omitting diagonal children loses this witness; deduplicating
repeated singleton factors breaks the mass sum. An empty source and a
reducible strict carrier must retain their failure of the nonzero/cyclicity
premises. The existing full-rank flat PIP cones still do not force a
synchronizing newborn at depth two.

## Acceptance and non-claims

Use actual repository word, mark, digit, reduction and strict-system
definitions. Compile the complete Lean bank and audit all declarations at
the published revision. Reuse canonical Mojo kernels for executable
regressions, with independent bounded Quint controls and explicit mutation
failures. The runner must bind model, runner and Git revision and refuse
incomplete test selection or infrastructure failures as mathematical evidence.

Keep the two developments independent. Record side findings and exact
receipts without changing governed claim statuses. Uniform productive
forced-crossing existence, a common legal limit, general C4, global G1,
Concentration and PSC remain open.

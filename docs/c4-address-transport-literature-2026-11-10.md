# C4 global addresses and affine transport: targeted stop/go

**Decision (2026-11-10): proceed with the concrete finite-word refinement
below.** This review precedes its new proof code and controls. The baseline
is `main@666e701d7cffde398e1265dd4ee95becf54fef53`, after
[PR #533](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/533).
The previous [occurrence review](c4-concrete-occurrence-literature-2026-11-10.md)
and [accepted local bridge](c4-concrete-occurrence-2026-11-10.md) remain inputs.

## Primary sources and transfer boundaries

| Source inspected | Relevant construction and limitation |
| --- | --- |
| Barge–Diamond, [*Coincidence for substitutions of Pisot type*](https://www.numdam.org/item/BSMF_2002__130_4_619_0/), Bull. SMF 130 (2002), 619–626. | Strong coincidence matches a letter after prefixes with equal abelianization. This identifies the eventual target of a realized address. Its two-letter theorem and partial higher-alphabet result do not supply the missing uniform ternary forced-crossing theorem. |
| Akiyama–Lee, [*Algorithm for determining pure pointedness of self-affine tilings*](https://arxiv.org/html/1003.2898v1), §2.5 and §4, especially (4.1)–(4.2). | An inflated overlap uses actual descendant tiles. Translation changes by the expansion applied to the old displacement plus the difference of the selected child digits. The occurrence multiplicities matter. Real overlaps have intersecting interiors; potential overlaps form a larger universe. The global spectrum criterion assumes a self-affine tiling and Meyer return set; neither is inferred here from a finite word pair. |
| Martensen, [*A Generalized Balanced Pair Algorithm*](https://arxiv.org/html/math/0309194v1), §2 and §§3.1–3.3. | Population vectors satisfy `p(sigma(w)) = M p(w)` with incidence columns given by image populations. Iteration substitutes and completely reduces balanced pairs. The local counting identities need no legality assumption, but the paper's dynamical conclusions involve their stated allowable-word/system hypotheses. Reducible examples prevent identifying geometric balance with population balance without an independent argument. |
| [Mathlib list take/drop](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/TakeDrop.html) and [list flatten](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Flatten.html), with the repository-pinned sources inspected locally. | `take`/`drop` reconstruct a selected indexed letter and its surrounding words; flatten concatenates ordered chunks. Mere `mem_flatten` supplies a containing value but forgets which repeated occurrence was selected. The implementation must establish the numerical prefix-length decomposition and an actual ordinal, rather than substitute set membership. Current online documentation is orientation only; Lean acceptance uses the pinned toolchain and mathlib revision. |

These are standard substitution, population-vector and indexed-list
constructions. The contribution sought is their checked refinement into this
repository's concrete word, factor and occurrence definitions, not a new
coincidence theorem.

## Exact narrow target

1. **Global index to factor occurrence.** For an in-range letter index in
   either track of a supplied complete balanced factorization, construct its
   factor ordinal, local index, prefix, selected letter and suffix. Prove
   that the global index equals the sum of preceding factor lengths plus
   the local index, and that reconstruction returns the original word and
   selected letter. Specialize to `Reduction.red`, using its existing
   flattening and balance theorems. Repeated equal factor words keep distinct
   ordinals. Out-of-range indices are outside the accepted contract.
2. **Common physical occurrence.** Compose this lookup with
   `OccurrenceNewborn.red_common_factor` for positive tile lengths and
   strictly intersecting interiors. The result identifies the same actual
   factor occurrence on both tracks. Endpoint contact is insufficient.
3. **Concrete affine square.** Let selected source indices be `i,j`, with
   letters `a,b`, and selected within-image digits be `p,q`. Prove their
   inflated indices are `|sigma(u[:i])|+p` and `|sigma(v[:j])|+q`, with
   actual selected child letters. For the convention

   ```text
   r = Parikh(u[:i]) - Parikh(v[:j]),
   r_next = M r + Parikh(sigma(a)[:p]) - Parikh(sigma(b)[:q]).
   ```

   prove equality with the residual computed from those actual inflated
   prefixes. Removing the same balanced factor-prefix from both tracks
   leaves this residual unchanged. Swapping the tracks must swap source
   indices and digits and negate the complete residual; retain the chosen
   normalization sign explicitly. Equality of normalized factor values
   alone does not identify this edge or its orientation.

The algebraic address identity is over literal finite words and valid
digits. It requires no Pisot hypothesis. Nonerasure supports the intended
whole-address descent and the accepted newborn theorem; valid digits alone
already imply that the two selected images are nonempty. Geometric
alignment-to-Parikh equality still uses the previously derived incidence
irreducibility/eigenrow interface. Do not insert that equivalence as an
unproved assumption or use integer-length controls as Perron vectors.

The canonical executable interfaces are
[`target_packets.mojo`](../kernel/psc/target_packets.mojo) and
[`c4_addressed_newborn.mojo`](../kernel/psc/c4_addressed_newborn.mojo).
The similarly named Lean `OverlapPacket` is a separate finite-mass
certificate interface and is not the definition of an addressed word edge.

## Adversarial controls and acceptance

Retain the previous boundary-touch, erasure, inherited-cut and malformed
suffix controls. Add bounded checks which distinguish:

- a global index from its local index after a nonempty factor prefix;
- repeated equal factors at different ordinals;
- a valid final index from the exterior index at the word's length;
- the signed affine update from one omitting `M`, one omitting a digit
  correction, or one failing to negate after a track swap;
- a transition staying in one common child from valid digits whose marked
  descendants split across two children;
- an actual repeated letter occurrence from a replacement having the same
  letter or factor value but a different address.

Use deterministic, explicitly bounded literal-word domains for Quint and
regression fixtures. They may include non-PIP substitutions and are not a
Pisot census. Reuse canonical Mojo implementations rather than add a second
production arithmetic or factorization implementation. A mutation counts as
rejected only when its declared assertion is reached and fails; parser,
download, timeout or empty-selection failures supply no mathematical result.

Acceptance requires the new Lean source and compiled axiom audit, exact-head
canonical Mojo replay, and the independent bounded controls with their
source-bound receipts. Record any new side finding in the append-only ledger
as part of integration.

## Explicit remaining boundary

An algebraically correct affine tuple is not by itself a realized packet
edge. This step must state which direction of refinement is established for
the actual address/occurrence universe. Finite path composition, completeness
of all accepted packet edges and consistent lifting of infinite quotient
paths require their own statements. No finite-index lookup, affine identity,
normalization lemma or passing finite domain proves that a forced crossing
has a productive path. General C4, global G1 extraction, arbitrary strict
child realizability and the uniform forced-crossing theorem remain open.

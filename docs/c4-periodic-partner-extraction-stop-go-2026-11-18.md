# Periodic partners after UP′: targeted source decision

**Status:** Pre-implementation literature gate for a conditional reduction and
finite Lean lemmas. No strict system is excluded and no governed claim changes.

## Proposed claim

Starting from the asymptotic partners supplied by round-four Lemma C(c),
preserve both memberships in the strict component while making all three
tilings substitution-periodic. Separate this from requiring the common fibre
to be the identity fibre, and from deriving a rank-two contradiction.

The starting revision is `main@4f8b3581605028b2e842c8b095ccbe164be8bdaa`,
the merge of PR #609. The relevant entries of the append-only
[side-notes ledger](side-notes-ledger.md) and the round-four, rank-two wall,
periodic-fibre, and unique-partner notes were inspected before choosing the
target. In particular, neither a common cut nor a finite periodic fibre
implies noncoincidence.

## Primary sources checked before proof code

| Source | Passage inspected | What transfers / boundary |
| --- | --- | --- |
| Barge–Diamond–Swanson, [The branch locus for one-dimensional Pisot tiling spaces](https://arxiv.org/pdf/0804.0930), §2 p. 5 and Example 3 pp. 7–8 | Simultaneous periodicization of a distinct asymptotic pair by a unique common translation; finite special-tiling set; explicit nonzero branch points | Applies to primitive aperiodic Pisot substitution tilings, including the standing class. Periodicization is prior art, attributed there to Barge–Diamond (2001). It does **not** put the pair in the identity fibre. Example 3 has two letters and is only a control against this overstrong inference, not against PIP3 at rank two. |
| Baker–Barge–Kwapisz, [Geometric realization and coincidence](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), Proposition 2.3, Definition 4.1 and Theorem 4.2 | Inflation is a homeomorphism; geometric realization has uniformly finite fibres; rank counts pairwise noncoincident tilings | A periodic base fibre is permuted by a suitable power of inflation, so all of its members are periodic. Fibre cardinality alone is not coincidence rank. Use the legal hull inside the paper's possibly larger strand space. |
| Barge, [Factors of Pisot tiling spaces and the coincidence rank conjecture](https://arxiv.org/pdf/1301.7094), Lemma 13 and its proof | Partners of the same tiling are densely eventually coincident at rank two; uniqueness additionally assumes the stack relation is trivial | Supports the boundary already stated in (W4). An asymptotic pair of partners is compatible with this conclusion. Do not import the uniqueness conclusion without its extra hypothesis. |
| Barge–Diamond, [Cohomology in one-dimensional substitution tiling spaces](https://arxiv.org/pdf/math/0702669), §3, eventual-range construction and Theorem 4 | Endpoint dynamics on legal seams and its cohomological use | Supports the existing periodic vertex construction. It provides neither a matching of partners without the covering hypothesis nor a new three-letter parity rule. |

The cited passages were read in their primary PDF texts during this task.
The 2001 paper cited by the branch-locus article is not independently imported:
the simultaneous-periodicization statement is taken as an explicitly cited
external result from the latter article. No novelty is claimed for it or for
periodicity of a finite invariant fibre.

## Controls and narrowed target

- Preserve the documented `1/012/21` failure of (NM_V). Endpoint merging can
  destroy the difference between two limiting vertex germs; do not use
  compactness alone to preserve distinctness.
- Preserve `012/120/201` as a rank-at-least-three triangle control, outside
  the nonsingular PIP3 hypotheses.
- Test the stronger inference “two distinct asymptotic partners force a
  triangle or a parity contradiction” using explicit finite partner data.
  Such data can refute a finite inference without realizing a strict tiling
  component.
- State a sufficient, additional zero-fibre hypothesis: after putting a
  right-asymptotic pair's branching vertex at the origin, their two left
  letters never merge under the last-letter map. The mirror uses the
  first-letter map. Inflation along a common endpoint period then preserves
  two distinct limiting vertex tilings. Closedness and (Z4) retain the
  common partner in the zero fibre.

## Decision

**Proceed with the narrowed target.** Prove the finite-fibre lifting step in
Lean, make endpoint persistence and finite partner obstructions checkable,
and write the geometric reduction with its external periodicization input
explicit. Periodic extraction into an unspecified periodic fibre is available;
universal zero-fibre extraction under (NM_V), and a contradiction after such
extraction, remain separate obligations. No census or new numerical
substitution algorithm is proposed.

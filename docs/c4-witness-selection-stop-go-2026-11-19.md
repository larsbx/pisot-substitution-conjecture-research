# Witness selection under (NM_V): source decision

**Status:** Source decision for gap 1 of the
[periodic-partner extraction](c4-periodic-partner-extraction-2026-11-18.md#non-claims--remaining-gaps)
(gap 2 of the [conditional formalization](c4-periodic-partner-formalization-2026-11-19.md#non-claims--remaining-gaps)):
under the surviving strict rank-two hypotheses and (NM_V), select a witness whose branch
letters pass the two-step endpoint test, or treat the periodic branch fibres that fail
it. Starting revision: `main@9774624` (merge of #613). No governed claim changes.

## Exact target

Lemma C(c) gives a tiling `T` with two distinct partners `S, U` that agree on a
half-line. Lemma P periodicizes the triple by one translation. The question is where
the periodic pair branches and what its leaves are there. Two targets:

1. a **deduction**: under (NM_V), (R4) and (E1), which branch configurations a periodic
   asymptotic pair can have, stated with explicit inputs and checked in Lean;
2. a **finite census**: whether the configuration that the deduction leaves open
   actually occurs among zero-fibre members of the unit corpus where (NM_V) holds.

## Sources

| Source | Input and boundary |
| --- | --- |
| Barge–Diamond–Swanson, [The branch locus for one-dimensional Pisot tiling spaces](https://arxiv.org/abs/0804.0930), §2 (re-read for [#612](c4-periodic-partner-formalization-stop-go-2026-11-19.md); not re-opened here) | A common translation makes two asymptotic tilings inflation-periodic. Already the named input `BDSPeriodicization`. Silent on where the periodic pair branches. |
| Baker–Barge–Kwapisz, [Geometric realization and coincidence](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), Theorem 4.2 | Finite fibres of `h`, so periodic fibres are permuted and the partner lifts (Lemma P). Unchanged import. |
| Barge–Diamond, *Cohomology in one-dimensional substitution tiling spaces*, Proc. AMS 136 (2008), Thm 4 and the eventual range | Vertex-type members of `F₀` are the seams of `ER`; a periodic tiling with a tile starting at `0` carries the ray of that tile. Supplies the local law `VertexLaws.periodic_ray`. |
| Barge, *Pure discrete spectrum for a class of one-dimensional substitution tiling systems*, Bull. SMF 143 (2015), asymptotic cycles before Cor. 25 (not re-opened here) | Asymptotic relations among members of the identity fibre, including interior ones. Context for the census object only. |
| Sirvent–Solomyak, Canad. Math. Bull. 45 (2002), Thm 5.6 and §§3–5, via [the overlap-depth gate](bpa-overlap-depth-literature-gate-2026-10-02.md) | Overlap states closed under inflation. Reused only through the existing exact decision `psc.zero_fibre_asymptotes.asymptotic`. |
| Round-4 note, [§3.1–3.3](c4-round4-2026-11-17.md#31-setting) (internal) | (R4), (E1), Lemma A, the definition of (NM_V). |

## Hypotheses that transfer, and those that do not

- **Transfer.** Lemma A's location argument (`x* ≤ βᵠ x*`) and branch uniqueness are
  already local laws (`RightBranchLaws`). (R4) is already a named input. (E1) is a short
  written argument from uniform continuity of `h`; it becomes the named hypothesis
  `AsymptoticSameFibre`. (NM_V) is a hypothesis of the target, stated as `NMVRight`.
- **Local, stated as contracts.** Existence of a first branch point of two distinct
  asymptotic tilings (`BranchExistence`, the infimum in Lemma A), symmetry of ray
  agreement, a tile after every vertex, and the periodic-ray law. They are elementary on
  the hull; discharging them on `PeriodicPartnerHull` is deferred.
- **Does not transfer.** No source selects a branch letter pair, says which fibre a
  periodic asymptotic pair lies in, or relates the branch of a periodic pair to the
  partners of a strict system. BDS Example 3 shows that periodic asymptotic pairs can lie
  over nonzero periodic points, so "periodic asymptotic ⇒ zero fibre" may not be assumed.
- **Census boundary.** The exact asymptote decision covers members of `F₀` only. Pairs in
  nonzero periodic fibres are outside it; the census says nothing about them.

## Controls

- `1/012/21`: a vertex member of `F₀` asymptotic to an interior one with its branch away
  from the origin. It shows that the vertex step needs (NM_V).
- The constant endpoint map: every pair merges. It shows that the collapsed-pair step
  needs two periodic letters.
- Literal word rays, sharing no code with the overlap decision, for one left and one
  right residual pair.

## Decision

**Proceed** with the deduction (Theorem S) and the census of its residual in `F₀`.
Novelty is claimed only for the vertex-leaf exclusion under (NM_V), the reduction to
the collapsed pair, and the exact residual count. **Defer** a selection theorem: the
census finds the residual configuration inside `F₀` on (NM_V) specimens at
`β₁(ER) = 2`, so (NM_V) by itself cannot supply one.

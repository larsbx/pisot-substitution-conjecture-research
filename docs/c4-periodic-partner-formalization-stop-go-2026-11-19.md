# Periodic-partner deductions: formalization source decision

**Status:** Pre-code decision for formalizing the conditional deductions of
PR #610. The starting revision is
`main@15c4098e53dfc4a1a45fd1f134ee6fbb5dd1da1a`. No governed claim changes.

## Exact target

Turn the written deductions of Lemmas P, E and M in the
[extraction note](c4-periodic-partner-extraction-2026-11-18.md) into Lean
theorems with inspectable, explicit inputs. Reuse the finite-fibre and
ternary endpoint theorems already checked in `PscVerif.PeriodicPartner`.
The target is conditional dynamics and metric geometry. It is not a new
proof of asymptotic periodicization, geometric realization, or universal
zero-fibre witness selection under (NM_V).

The previous [source decision](c4-periodic-partner-extraction-stop-go-2026-11-18.md)
and the append-only [side-notes ledger](side-notes-ledger.md), including its
2026-11-18 periodic-partner entry, were read before choosing this target.
Repository inspection found finite/right-infinite word and address models,
but no formal legal two-sided tiling hull, physical branch relation, local
tiling topology, or complete geometric-realization map to instantiate here.

## Primary sources rechecked before proof code

| Source | Relevant input and boundary |
| --- | --- |
| Barge--Diamond--Swanson, [The branch locus for one-dimensional Pisot tiling spaces](https://arxiv.org/pdf/0804.0930), introduction and section 2, printed page 5 | The legal primitive aperiodic hull is a metric space with translation and inflation; distinct asymptotic pairs admit a common translating periodicization. The latter remains an explicitly named quantified input. It supplies neither a zero-fibre conclusion nor a rank-two contradiction. |
| Baker--Barge--Kwapisz, [Geometric realization and coincidence](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), introduction and Theorem 4.2 | Inflation/translation covariance, semiconjugacy and finite fibres. The formal lifting argument uses injectivity and finite invariant fibres; these hypotheses must not be replaced by a conclusion asserting a periodic triple. |
| Barge, [Factors of Pisot tiling spaces and the coincidence rank conjecture](https://arxiv.org/pdf/1301.7094), Lemma 13 | Co-partner eventual coincidence is consistent with the remaining configuration; uniqueness requires an additional stack-relation hypothesis. This formalization cannot import that stronger conclusion. |
| Barge--Diamond, [Cohomology in one-dimensional substitution tiling spaces](https://arxiv.org/pdf/math/0702669), sections 2--3 | Legal bi-infinite substitution words, endpoint dynamics, and the eventual range. These support the existing vertex interpretation but do not instantiate a formal tiling hull or supply noncovering partner matching. |

These passages were re-opened in the primary PDF texts for this continuation.
The source claims are unchanged from #610. The formal work checks their
consequences; it does not upgrade imported mathematics to an internal proof.

## Noncircular hypothesis design

- **P:** finite semiconjugacy, injective dynamics, injective common
  translations, diagonal invariance of the joining, same-fibre partners,
  and a named common-periodicization input. Derive the common period and
  preserve both joining links and distinctness.
- **E:** define a branch using right-ray agreement and two different
  labels ending at that position. Use one-step translation/inflation
  transport, uniqueness of a label at a fixed endpoint, and the local
  fact that agreement starting strictly before an endpoint forces equal
  endpoint labels there. Derive branch-position uniqueness and
  `y = beta^q * y`, rather than assuming either result. Use (R4) only in
  the form periodicity **and** an origin endpoint imply identity-fibre
  membership; derive the reverse implication from finite-fibre dynamics.
- **M:** an agreement relation on centred neighbourhoods has restriction
  to smaller positive radii, one-step inflation of radius, and a uniform
  metric compatibility modulus. A common half-ray and equal endpoint
  labels supply a positive-radius common patch. Derive growing agreement,
  convergence of the distance, and equality of existing subsequential
  limits. Do not assume convergence or compactness as a substitute.
- **Exact rays to metric asymptoticity:** use the local fact that a ray
  covering a centred neighbourhood gives centred agreement, together
  with translation transport and the metric modulus. Derive convergence
  under the translation flow and use it to pass a published metric BDS
  input to the exact-ray consumer. A positive abstract model exercising
  this bridge must make its ray agreement compatible with its metric;
  assigning unrelated discrete colour distance is insufficient for it.

Every external geometric assertion is a theorem argument or a field of an
explicit data contract. No `axiom`, `sorry`, or target conclusion hidden as
an interface field is permitted. Metric separation is required when
concluding equality of limits; expansion and tile lengths are positive.

## Controls and decision

Preserve the literal `1/012/21` endpoint merge, the singular rank-three
triangle, the connected finite nontriangle model, and the fixed-base
period-two lift from #610. Add concrete nonvacuity models for the new
abstract contracts and controls for any newly exposed indispensable
hypothesis. Label those models as abstract dynamical/metric examples,
without claiming a Pisot tiling realization.

**Proceed.** Formalize P/E/M and their joint ternary consumer at exactly
this conditional scope, audit all compiled declarations, and retain a
separate explicit obligation to construct the legal tiling realization and
discharge the imported geometric hypotheses. No census, new executable
substitution algorithm, or C4/PSC exclusion is proposed.

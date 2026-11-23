# Measured translation spectrum of the literal σₖ family

## Source decision

The next claim is a measure-preserving almost-everywhere inverse for the full-history geometric realization and a dense complex L² span of its actual translation eigenfunctions for k ≥ 2. The input is the proved conull Gδ set of singleton fibres for normalized Haar. The set carries the subspace topology and its Borel structure. The conclusion uses the actual family hull, inflation and real translation.

- Baker, Barge and Kwapisz, *Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces*, Theorems 4.2 and 5.1 and Corollary 5.2, use the solenoid character pullback and generic fibre multiplicity to obtain the pure-discrete conclusion. The local proof will construct the inverse and the surjective pullback explicitly for the factor already built here. [Published article](https://www.numdam.org/item/AIF_2006__56_7_2213_0.pdf)
- Barge and Kellendonk, *Proximality and pure point spectrum for tiling dynamical systems*, §2.2 and Theorem 2.25, identify the measured scope as generation of L² by continuous eigenfunctions. The present route already has singleton fibres on a particular Haar-conull set and does not invoke their criterion. [Author preprint](https://arxiv.org/html/1108.4065v1)
- The pinned Mathlib supplies `IsClosedMap.restrictPreimage`, `Equiv.toHomeomorphOfContinuousClosed`, `MeasurableEmbedding.measurable_extend` and `Lp.compMeasurePreservingₗᵢ`. The closed-map result supplies continuity of the inverse on the conull subspace. The L² isometry still needs a proof of surjectivity. [Pinned Mathlib sources](https://github.com/leanprover-community/mathlib4/tree/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib)

Proceed using the existing geometry and character-frequency certificates. The zero-fibre seam pair precludes a global two-sided inverse. The measure proof should establish the equalities almost everywhere for the two specified probabilities.

## Measure and inverse

Let π be the ordinary-hull factor and A the chosen Haar-conull Gδ set of singleton fibres. The actual π is closed by continuity and compactness into the Hausdorff solenoid. The restriction from π⁻¹(A) to A is a continuous closed bijection, so its inverse is continuous for the subspace topology. Extend this inverse measurably by a fixed legal tiling to obtain s on the whole solenoid.

Write μ for Haar and ν for the pushforward of μ by s. The identity π ∘ s = id holds μ-almost everywhere, so the pushforward of ν by π is μ. Also s ∘ π = id holds ν-almost everywhere by singleton uniqueness. The same latter argument applies to any measure projecting to μ. Pushing forward through s then identifies that measure with ν. The measure is therefore independent of the choices in the measurable extension.

For each real time and for inflation, the pushforward of ν by the corresponding hull map projects to the pushforward of μ by the corresponding solenoid map. Those base maps preserve μ. Uniqueness of the Haar lift proves invariance of ν. The argument only uses the conull set for constructing the inverse and establishing fibre uniqueness.

## Measured eigenfunctions

Pullback along π is a complex linear isometry from L²(μ) to L²(ν). For each class u in L²(ν), composition u ∘ s defines a class in L²(μ), and its pullback is u by the hull almost-everywhere inverse identity. This proves surjectivity and gives a linear isometric equivalence. The actual Koopman map at each real time is also onto, using the opposite-time translation as its inverse.

Each certificate gives a unit L² vector represented by the existing continuous eigenfunction on the hull. For its real frequency ξ, composition at time t multiplies this vector by exp(2πi·tξ). The dense Haar L² span of certificate characters therefore transfers to a dense hull L² span. The theorem `C4FamilyMeasuredSpectrum.pureDiscrete_translation` states that the closed complex span of the nonzero joint translation eigenvectors is the whole L² space, for every k ≥ 2 with the specified invariant Borel probability.

## Controls and scope

The actual seam pair obstructs a global left inverse for π. A two-atom counting-measure factor that collapses both atoms shows that a measure-preserving map can have a proper L² pullback range. Its indicator of one atom has no preimage. The audit also refuses the everywhere inverse type and the opposite phase sign in the explicit frequency law.

The measured result concerns real translation on the ordinary legal tiling hull.
At the #650 revision, symbolic transfer was a separate obligation; the
dated continuation below records its subsequent completion. Universal
Pisot cases remain separate questions.

## Continuation, 23 November 2026

The [symbolic transfer from #653](c4-family-symbolic-spectrum-2026-11-22.md)
proves the itinerary conjugacy, continuous roof correction and constant-strip
factor for the same ordinary legal hull. Its
`C4FamilySymbolicSpectrum.pureDiscrete_shift` theorem establishes pure discrete
complex `L²` spectrum for the actual two-sided legal word shift with its
induced invariant `wordMeasure`, for every `k ≥ 2`.

The [canonical-measure follow-up](c4-family-canonical-measure-2026-11-23.md)
proves `hullMeasure_eq_of_invariant` and
`invariant_probability_eq_wordMeasure`. The first identifies every
real-translation-invariant hull probability with this note's Haar lift.
The second identifies every invariant symbolic Borel probability with
`wordMeasure`; its normalized corrected constant-strip suspension recovers
the supplied base measure and has Haar solenoid marginal. An explicit
measure-equality theorem then transports the existing symbolic spectral
endpoint. These results retain `k ≥ 2` and do not change the original
`pureDiscrete_translation` theorem or its historical acceptance.

The [new local acceptance packet](../evidence/c4-canonical-measure-2026-11-23/README.md)
pins proof commit `68e5ba028e863efedd4774ce4e07bd8678dc9143`, before the
current main integration. [Integration acceptance](c4-canonical-measure-integration-2026-11-23.md)
and independent human review are separate. The #652 periodic-origin classification and
corrected census remain an additional zero-fibre route. The physical
variable-roof Lebesgue disintegration, a separate frequency-defined
canonical measure, and general PSC/BH/A1′/C4 conclusions are not supplied
by this continuation.

## Replay

PR #650 merged at `968fabde6c1c056d5157abc77460a5a4e2a4cfd1` from head
`686c266f09016d0475e128cb395d6a1bccf566b3`. The proof uses the finite-automaton
witnesses. The family gate includes the measured spectrum root and its
endpoint and axiom audit. [PR #650](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/650) · [Local acceptance](../evidence/c4-family-measured-spectrum-2026-11-21/acceptance.json)

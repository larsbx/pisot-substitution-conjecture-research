# Ordinary hull topology: source decision

**Decision: proceed with the narrowed topology target below.** Starting
revision: `ec026774e666fb8e8ac43b1ba975b9a4df8891b2` (after PR #623).
This is a pre-implementation source review, not a compilation receipt.
The relevant November 19 entries in [the side-notes ledger](side-notes-ledger.md)
were reviewed, including the exact-agreement hull, geometric realization,
spectral contraction, and target topology. No governed claim changes.

## Exact proposed claim

Give the existing legal tiling carrier an ordinary, translation-tolerant
topology without replacing the exact-agreement metric used by the current
periodic-partner proofs. Use a separate topological presentation of the same
tilings. Write `H_exact` for the existing metric hull and define its new
topology as the final (coinduced) topology of

`q : Real x H_exact -> H_local`, `q(t,T) = translate t T`.

Here `translate t T` means `T - t`, as in the existing source. Prove:

1. Fixed translations are homeomorphisms of `H_exact`, and `q` is an open
   quotient map.
2. The new topology has the usual small-translation/window description.
   For `epsilon > 0` and a natural radius `n`, put
   `N(T;epsilon,n) = {translate t U | abs(t) < epsilon and Agree n T U}`.
   A set `O` is open exactly when every `T` in `O` has such a neighbourhood
   contained in `O`. Thus the final topology is identified with the
   ordinary local tiling topology; its name is not the only justification.
3. Translation `Real x H_local -> H_local` is jointly continuous.
4. Literal inflation `H_local -> H_local` is continuous, using the proved
   agreement transport and `inflate (translate t T) =
   translate (beta*t) (inflate T)`.

These are standard topological facts, specialized to the repository's
literal half-open tile sets. No novelty in the ordinary topology is claimed.

## Three primary sources checked

| Source and inspected location | Relevant statement and boundary |
| --- | --- |
| Baker, Barge and Kwapisz, [*Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces with an application to beta-shifts*](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), Ann. Inst. Fourier 56 (2006), pp. 2218-2221: Proposition 2.3, Definition 3.1, equations (3.8)-(3.12). | The strand-history model projects homeomorphically to their tiling space, and realization takes strand vertices to compatible quotient coordinates. The proof of Proposition 2.3 uses recognizability for the backwards histories. Footnote 5 on p. 2218 warns that their global-attractor convention may contain extra nonrecurrent translation orbits. Ordinary topology on our legal hull therefore does not by itself identify that hull or its realization with their full model. |
| Barge, Diamond and Swanson, [*The branch locus for one-dimensional Pisot tiling spaces*](https://www.impan.pl/shop/en/publication/transaction/download/product/89123), Fundamenta Mathematicae 204 (2009), pp. 215-217, especially p. 216. | This is the legal hull: every finite patch occurs in a substituted word. Their topology allows a small translate to agree on a large neighbourhood of the origin. Under their standing primitive and aperiodic hypotheses, inflation is a homeomorphism and translation is a flow. Their subsequent asymptotic arguments use this ordinary topology, not the repository's finer exact-agreement topology. |
| Barge and Diamond, [*Cohomology in one-dimensional substitution tiling spaces*](https://arxiv.org/pdf/math/0702669), section 2, manuscript pp. 2-3. | They describe the same local topology on labelled interval tilings, state continuity of literal inflation on the ambient tiling space, and restrict to allowed words for the legal hull. They distinguish that elementary continuity statement from invertibility: on a primitive aperiodic hull, the homeomorphism assertion relies on recognizability. Section 3's inverse-limit representation is an additional construction, not needed for the present target. |

All three texts were opened and the indicated passages read for this
decision. The review uses no uninspected recognizability theorem as a new
proved dependency.

## Hypotheses that transfer

The local proofs use the existing `LengthSubst`: positive lengths, nonempty
substitution images, and the length-eigenvector equation. A nonempty
alphabet gives `beta > 0`. No determinant, Pisot contraction, primitivity,
recognizability or finite-fibre premise is needed for the four claims above.
The intended PIP3 application has a finite nonempty alphabet, but the
topology argument should not introduce a stronger hypothesis without using
it.

The exact-agreement cylinders are open in `H_exact`. A fixed translation
only shifts the required agreement window, so it acts there by a
homeomorphism. To prove that `q` is open, take a product neighbourhood at
`(t,U)` and pull its image back through an arbitrary representative
`(s,V)` of the same tiling. A fixed translation carries a sufficiently small
exact neighbourhood of `V` into the chosen neighbourhood of `U`; the open
interval in the time coordinate absorbs the change from `s`. This gives
openness of the entire inverse image, as required by the final topology.

The product of an open quotient map with the identity is again an open
quotient map. Translation continuity then descends from addition of the two
time coordinates. Inflation continuity descends from the continuous map
`(t,T) -> (beta*t, inflate T)` on `Real x H_exact`. The neighbourhood
criterion follows by applying openness of `q` to interval-times-cylinder
neighbourhoods. These arguments provide a proof route without selecting a
discontinuous origin-tile coordinate.

## Negative controls and stronger claims to refuse

- **Small translates in the old metric.** For a unit-interval tiling, small
  nonzero translations change the exact tile positions at the origin, so
  they do not converge in the exact-agreement metric. They must converge in
  the new topology. This distinguishes the two presentations and tests the
  purpose of the construction.
- **Inflation need not be invertible.** The periodic one-letter
  substitution `a -> aa` has a circle of translates; inflation doubles
  the phase and is not injective. Continuity of inflation cannot discharge
  recognizability.
- **Bare bijectivity is insufficient.** The old exact hull has no proved
  compactness. A bijective self-map of it does not acquire a continuous
  inverse merely from being bijective. Do not replace the recognizability
  hypothesis with an asserted homeomorphism.
- **Realization continuity is a separate theorem.** The target already has
  a continuous flow. Descent of the source realization still requires a
  proof of its continuity on transverse data (or an equivalent direct
  ordinary-hull argument). Its convergent series and set-level
  equivariance alone are not such a proof.

These are design controls; this note does not claim that new Lean control
theorems or replay checks have already run.

## Stop/go result and next boundary

Proceed with the open quotient, its explicit local-neighbourhood
characterization, joint translation continuity and inflation continuity.
Keep the existing metric consumers intact through the separate
presentation. Record compiled evidence and the achieved theorem names in
the implementation note after the proof is checked.

Do not claim compactness, continuity of inverse inflation, recognizability,
continuity or surjectivity of realization, the normalized BBK
identification, finite fibres, BDS periodicization, or a global rank-two
contradiction in this increment. Once the local topology is available,
compactness/local recognition and continuity of the concrete realization
are the next distinct formalization obligations.

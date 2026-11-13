# Named forward carrier: pre-code source decision

Decision: **proceed with a finite, literal forward-closure certificate**.
The user-facing date is 2026-11-12 (America/New_York); the source retrieval
and decision occurred on 2026-11-13 UTC. This note precedes the new
`ForwardCarrier.lean` and `NamedForwardCarrier.lean` sources, on parent
`2f7c058fdd50ff65fbcf00543bece49913d47ad5`.

## Exact proposed claim

For a finite alphabet with decidable equality, a substitution `s`, and a
literal finite list `states` of ordered word pairs, check that:

1. every actual ordered swap seed `([a,b],[b,a])`, `a != b`, belongs to
   `states`;
2. for every listed noncoincident pair `T`, every member of the actual
   Lean reduction `red (subst s T.1) (subst s T.2)` belongs to `states`.

A successful check then implies `(bpaStatesNC s).Finite`, and finite
actual `ChildNC` reachability from every listed state. Coincidences are
terminal exactly as in `ChildNC`. The list may be a finite closed
superset; exact reachability, uniqueness, minimality and discovery data
are unnecessary for this implication.

The two intended concrete instances are precisely `1/021/001` and
`1/012/001`. Canonical Mojo supplies proposed ordered state words using
the existing bounded forward BPA engine. Lean recomputes their actual
children; the generic theorem trusts no exported adjacency, normalized
quotient, completeness flag or search cap. Complete ordered child rows
may also be exported for independent replay, but that replay and the
Lean states-only certificate have distinct contracts.

## Three primary-source checks

1. **V. F. Sirvent and B. Solomyak, *Pure Discrete Spectrum for
   One-dimensional Substitution Systems of Pisot Type*, Canadian
   Mathematical Bulletin 45 (2002), 697–710,
   [doi:10.4153/CMB-2002-062-3](https://doi.org/10.4153/CMB-2002-062-3),
   [publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/4BC0FD9DBA6ECA027A32568F9E5C1D12/S0008439500017537a.pdf/pure_discrete_spectrum_for_onedimensional_substitution_systems_of_pisot_type.pdf).**
   Fresh inspection of section 3, equation (3.1) and Theorem 3.1 confirms
   the standard construction: iterate substitution and irreducible
   balanced-pair reduction; termination means that their union is
   finite. Reaching a coincidence is a separate condition. The paper
   uses prefix-derived initial pairs, so its initialization is not an
   imported identification with this repository's six swap seeds. Its
   full-child convention also differs at diagonal states; the existing
   `finite_bpaStates_iff` supplies the repository's precise finite-
   alphabet bridge. The finite invariant-set proof proposed here is
   standard, not a new balanced-pair criterion.
2. **M. Barge, S. Štimac and R. F. Williams, *Pure discrete spectrum in
   substitution tiling spaces*, Discrete and Continuous Dynamical
   Systems 33 (2013), 579–597,
   [doi:10.3934/dcds.2013.33.579](https://doi.org/10.3934/dcds.2013.33.579),
   [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf).**
   Fresh inspection of the definition preceding Theorem 3.2 separates
   finite irreducible-factor closure from eventual coincidence for
   every factor. Theorem 3.2 and Corollary 2 add Pisot and independence
   or irreducibility assumptions to obtain pure discrete spectrum.
   This increment discharges only a concrete finite-closure premise.
   The existing strict-exclusion consumer supplies the separate
   productivity argument after its own hypotheses and acceptance are
   retained. No spectral theorem or geometric realization is imported.
3. **B. F. Martensen, *A Generalized Balanced Pair Algorithm*, Topology
   Proceedings 28 (2004),
   [arXiv:math/0309194](https://arxiv.org/abs/math/0309194),
   [author-uploaded PDF](https://arxiv.org/pdf/math/0309194).**
   Fresh inspection of Example 3.13 and section 4 preserves the relevant
   boundary: a rewritten Morse–Thue system has forced coincidences but
   does not terminate, and changing the equivalence relation changes
   the algorithm. A finite search prefix or an existing coincidence
   witness cannot replace a complete closure check. The checker will
   retain literal ordered words and exact Parikh reduction, without
   changing balance or passing to a generalized equivalence relation.
   This example is a scope control, not a counterexample to the
   standing irreducible Pisot conjecture.

## Repository contract and hypotheses

[`Descendants.bpaStatesNC_subset`](../proof/PscVerif/PscVerif/Descendants.lean)
already proves containment of all seed-generated paths in any seed-
containing set closed under every actual child of its noncoincident
members. Apply it to the set represented by the finite list. For an
arbitrary listed starting state, induction on `ReflTransGen (ChildNC s)`
gives the same containment. This reasoning needs neither nonerasure,
primitivity, Pisot expansion nor a geometric model. Listed states need
not be assumed reachable or irreducible for this upper-bound theorem;
actual seed descendants retain their already proved block condition.

The [canonical Mojo engine](../kernel/psc/bpa.mojo) normalizes track swaps.
The exporter must expand the ordered double cover, including each
diagonal once. Lean independently checks every ordered seed and every
raw child, so soundness does not require trusting that expansion.
Exhausted state or length budgets refuse a native completeness verdict.
The earlier corpus fold and inverse-overlap archives cannot replace the
new literal-state check. Vendored search code remains unchanged.

## Controls and decision boundary

- An empty list or a list missing an ordered seed must fail.
- The normalized Fibonacci representatives alone must fail ordered-seed
  coverage; the genuine three-state ordered terminal-child carrier
  passes, while its two seeds without the diagonal exit fail.
- The three-state Fibonacci carrier deliberately omits `(1,1)`: its
  acceptance guards the terminal-coincidence convention, since full
  `Child` closure would require that extra state.
- A finite closed superset, including extra terminal states or duplicate
  entries, may pass. Such acceptance is sound for the upper-bound claim
  and is not an assertion of exact or minimal enumeration.
- The genuine two-state Thue–Morse carrier passes finiteness while its
  existing strict-system theorem excludes productivity. Closure alone
  must not imply termination with coincidence.
- Bind named conclusions to `NamedPrefixCompact.substitution fixture`
  itself. A theorem for a freely chosen substitution does not discharge
  a named fixture, even when incidence matrices agree.

Proceed with this narrowed target. The permitted result is conditional
checker soundness, followed only after exact concrete checking and
required acceptance by named seed-generated finiteness and the existing
conditional termination consumer. No claim covers arbitrary unlisted
balanced blocks, universal G1, general C4, pure discrete spectrum or PSC.
At this decision no new proof source has been written or compiled and
no concrete carrier has been accepted.

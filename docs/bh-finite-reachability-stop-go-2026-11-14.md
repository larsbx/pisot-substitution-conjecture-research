# Finite overlap packets to finite actual word reachability

Date: 2026-11-14. Baseline: `6bf0b9704501eb763cbb4323c3fd1f939d6f11c8`
(PR #573). This note records the pre-code decision for the next conditional
bridge. It was restored after an execution-workspace reset; restoration is not
a compilation receipt.

## Decision and exact target

Proceed with the missing formal bridge, using the repository's existing actual
marks, integral packets, `InteriorStep`, complete balanced-pair reduction and
terminal-child relation. Do not assume a finite word carrier or a factor-length
bound in the public endpoint.

Let `s : Fin 3 -> List (Fin 3)`, let every letter length be positive, and suppose
`physicalLength l (s a) = beta * l a` for every letter with `beta > 0`.
For an actual balanced seed `T`, assume a finite set `C` covers every pair of
strictly overlapping selected tiles in every actual iterate of `T`. Assume
every `p in C` has a finite composable `InteriorStep` path to a packet whose
**integral** displacement is zero. Then the set of all irreducible factors of
all iterates of `T` is finite. If `T` is an irreducible balanced block, its
actual `ChildNC` reachable set is finite as well.

A companion occurrence-ancestry theorem should derive the all-iterate coverage
premise from two conditions on the same packet set: coverage of the seed's
actual overlapping marks, and closure under **every** actual `InteriorStep`.
This makes the finite-carrier consumer usable without an extra infinite
coverage assumption. It does not prove such a carrier exists for every Pisot
substitution.

## Primary-source review and prior coverage

The bounded-gap principle is established mathematics, not a claimed new
mechanism. Sirvent and Solomyak, *Pure discrete spectrum for one-dimensional
substitution systems of Pisot type* (2002), Theorem 5.6, relates finite prefix
balanced-pair algorithms, half-coincidence termination, and bounded gaps:

<https://www.cambridge.org/core/services/aop-cambridge-core/content/view/4BC0FD9DBA6ECA027A32568F9E5C1D12/S0008439500017537a.pdf/pure_discrete_spectrum_for_onedimensional_substitution_systems_of_pisot_type.pdf>

Their fixed-point/prefix formulation and rational independence assumptions
must not silently be substituted for this repository's literal integral
packet hypotheses. An integral zero displacement directly supplies balanced
prefixes, so the proposed conditional bridge does not need to infer integral
equality from equality of physical lengths.

Barge, Stimac and Williams, *Pure discrete spectrum in substitution tiling
spaces*, Section 3, Theorem 3.2 and Corollary 2, use finiteness of the full set
of irreducible balanced factors together with eventual coincidence of each
factor:

<https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf>

The repository's `TerminationFactors` now formally binds that full-iterate
condition to the actual `ChildNC` definition. The spectral theorem itself is
external and has its own hypotheses. The new bridge supplies finiteness only;
it does not erase the separate productivity requirement.

Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*
(2014), Theorems 9.2 and 9.10, distinguish multiple tiling from tiling and use
additional property (F) and strong-coincidence assumptions:

<https://www.numdam.org/item/10.5802/aif.2884.pdf>

This source does not license an unconditional nonunit tiling conclusion from
the proposed packet-finiteness bridge. Its additional finite-place and
coincidence hypotheses remain separate.

Locally, `docs/bpa-termination-by-overlap-depth-2026-10-02.md` already gives the
hand bounded-gap derivation and explicitly records its missing Lean binding.
`OccurrenceTransport` supplies literal inflation and affine packet paths;
`OccurrenceSuccessor` supplies actual mark selection away from boundaries.
The new work formalizes the missing composition, rather than repeating the
older hand derivation or presenting a new universal result.

## Derivation to be checked

1. Choose one finite zero-displacement path for each packet in `C`, and take
   the maximum path length `D`. Finite choice is sufficient; no computable
   bound in terms of the substitution is claimed.
2. Lift each path from the actual overlapping marks without discarding its
   original tile interval. An integral zero residual gives equal Parikh
   prefixes. Pad shorter paths by substitution to the common depth `D`.
3. Put `M = max_a l(a)`. If an irreducible factor at level `D+n` has physical
   length greater than `2 * beta^D * M`, its central open interval remains
   nonempty after deleting that margin at both ends.
4. Pull a point in this interval back to level `n`, avoiding the finitely
   many top and bottom prefix boundaries. The two selected original tiles
   overlap strictly, and their inflated tile interval lies strictly inside
   the factor in question. Its zero-residual path supplies a balanced cut
   there, contradicting consecutive irreducible-factor boundaries.
5. The positive minimum letter length turns the physical bound into a word
   length bound. The alphabet is finite, so all late factors lie in a finite
   word-pair set. The first `D` generations add only a finite union of finite
   reduction lists.
6. Apply `TerminationFactors.finite_factors_iff_finite_reachableNC` for an
   `IsBlock` seed.

The ancestry companion decomposes each actual mark in a substituted word
into its actual parent mark and digit mark. Positivity and exact length
scaling pull any strict child-overlap point back to a strict parent-overlap
point. Induction on generation then transports seed coverage through complete
`InteriorStep` closure. Nonerasing need not be a separate premise: a mark in
an empty image cannot exist, and the length assumptions already exclude such
images when needed.

## Negative controls and non-claims

- A physical zero offset is insufficient. With unit lengths, the genuine
  irreducible balanced seed `021/120` has overlapping middle `2` tiles at the
  same physical position, but their integral residual is `e_0-e_1`; there is
  no balanced cut in that selected tile interval at depth zero.
- An abstract packet graph must be bound to actual seed occurrences and all
  actual digit edges. A selected successor or sampled list is not complete
  closure.
- The existing identity-substitution control has finite factors without
  coincidence productivity.
- The existing non-Pisot `00001/011` control has immediate productive exits
  but an infinite actual reachable set. The bridge must not infer its finite
  carrier from productivity alone.
- No Pisot, primitivity, irreducibility or rational-independence assumption
  is needed for this conditional bridge. Conversely, none of those words in
  a theorem title supplies the missing packet cover or zero-hit hypothesis.
- No universal BH, A1-prime, C4 or PSC status is promoted.

## Acceptance boundary

Compile the new modules with the pinned Lean release and unchanged dependency
revisions. Audit the complete declarations owned by those modules, permitting
only the established three standard axioms; compare independently written
public endpoint types and reject missing and wrong-typed controls. Run the
source-isolated gate and the unchanged full proof-bank gate at the published
revision. Regenerated inventory and historical local receipts remain distinct
from compiled acceptance. Interrupted or lost local sessions have no credited
terminal result.

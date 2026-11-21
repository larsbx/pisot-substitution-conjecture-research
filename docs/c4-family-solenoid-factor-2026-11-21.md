# The solenoid realization for the literal σₖ hull

## Source decision

Proceed with the literal family's desubstitution and geometric realization
for `k ≥ 1`. The [legal-patch proof](c4-family-legal-coincidence-2026-11-21.md)
uses the factor at `k ≥ 2`. The family has determinant two, so a point of
the target retains its full inverse-limit history.

- [Solomyak, unique composition](https://doi.org/10.1007/PL00009386)
  gives the corresponding recognizability result for aperiodic self-similar
  FLC tilings. Here the literal images allow a direct proof using the `2`
  tile and the two consecutive `0` tiles. Existence of desubstitution can
  use exact-window recurrence and closedness of inflation.
- [Baker–Barge–Kwapisz, §3 and Theorem 4.2](https://doi.org/10.5802/aif.2238)
  use the nonunit solenoid and bound fibres by pulling bounded windows
  through desubstitution. For the repository map, the analogue is the
  stable-series bound on the normalized lift. A bounded integer lattice
  difference leaves finitely many possible local patches in each fibre,
  with a bound independent of depth.
- [Barge–Štimac–Williams, Theorem 2.3 and Corollary 1](https://doi.org/10.3934/dcds.2013.33.579)
  use the finite-to-one maximal equicontinuous factor and its same-fibre
  witnesses. The geometric step consumes these on the ordinary legal hull.

Reuse the unchanged continuity proofs from
[#627 at `23ffa29`](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/627)
where they apply. The existing realization controls show why a single
torus coordinate cannot replace the solenoid history for a nonunit system.

Surjectivity can use the explicit coordinates without a separate density
theorem for irrational torus lines. Lift the $n$-th coordinate of a target
point to the unit cube. Under $M^{n-j}$, its stable projection tends to
zero for each fixed $j$, while its unstable projection is the $j$-th
coordinate of a translation of zero. The ordinary hull is a compact image
of the anchored exact hulls and a bounded translation interval. Therefore
the image is closed and contains the dense orbit of zero, using the
periodic seam tiling that realizes to zero.

## Lean results

For every $k\ge 1$, inflation is bijective on the legal hull. A tile
labelled 2 determines the position of its parent of type 1. Two
consecutive tiles labelled 0 determine the beginning of a parent of
type 2 because both alternative placements force a 1 in the second
position. The remaining child tiles determine the one-child parents of
type 0. The range of inflation is closed on the exact hull. Every legal
window occurs in a translate of an inflated legal tiling, and every such
translate is itself an inflation, so the range is dense as well.

The actual incidence matrix supplies irreducibility and Pisot
contraction. The resulting map from the ordinary hull to the full
inverse limit is continuous, onto, and intertwines both translation
and inflation. Its zero fibre contains the legal tiling with seam
`1.1`, which is fixed by squared inflation.

The vector lift is bounded uniformly on the hull, and its length
coordinate is the negative start of the origin tile. Equality of a
torus coordinate makes the difference of two vector lifts a bounded
integer vector. Relative to a reference tiling in the fibre, a small
window can contain the origin tile or its immediate neighbours. The
possible starts of these tiles lie in a fixed finite set after
subtracting the reference origin start. This holds at every
desubstitution depth. A finite list of distinct tilings is distinguished
in a sufficiently large finite window. At sufficient depth the
inflations of the small windows cover this large window, so the size
of the list is bounded by the number of possible small windows.

Every member of the zero fibre is inflation-periodic. For $k\ge 2$,
three exact window agreements at radius one, two at the origin and
one after a common shift, give the closed-origin witnesses required
by the [periodic common-tile theorem](c4-family-legal-coincidence-2026-11-21.md).
This is the precise remaining hypothesis of
`common_tile_of_zero_fibre_witnesses`.

## Comparison with the published factor

Each translation orbit in the ordinary legal hull is dense. Thus
any continuous equivariant map into this solenoid with the same time
parameter differs by a constant in the solenoid. Lean proves the
resulting equality of fibres in `solenoidRealize_fibres_eq_of_equivariant`.

For the written identification, §3 of Baker–Barge–Kwapisz takes
$\Sigma=\Gamma=\mathbb Z^3$ for the irreducible incidence matrix. A
two-sided history $(p_j)_{j\in\mathbb Z}$ with $p_{j+1}=Mp_j$
is determined by its entries $p_{-n}$, $n\ge 0$. Its unstable
translation vector is normalized by the Perron lengths through
$\ell\cdot u=1$. With tilings translated as $T-t$, negating the
target coordinates reconciles the sign with Lean's convention.
Theorem 5.1 identifies the continuous eigenvalue group and pulls
its eigenfunctions back through this published map. On the minimal
hull this gives the maximal equicontinuous factor. The Lean
comparison applies once this target and action identification is
used. Barge–Štimac–Williams Corollary 1 then supplies the exact
same-fibre agreements, and their Theorem 3.1 gives the published
spectral implication.

The target identification with the published construction and
the use of Corollary 1 remain written arguments. Lean still needs
the same-fibre witnesses and the passage from coincidence rank one
to the invariant-measure $L^2$ conclusion. The
[existing written spectral proof](c4-family-spectral-closure-2026-11-14.md)
already covers the family.

## Replay

Run `tools/check_c4_parameter_family.sh` from the repository root.
The endpoint fixture matches the theorem types for the literal
family, checks their owning modules and scans their axiom
dependencies. It also checks that the literal torus endomorphism is
noninjective for every $k\ge 1$. The half-integer vector
$(1/2,0,1/2)$ maps to $(1,1,0)$, while its own class is nonzero.

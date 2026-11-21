# Concrete realization continuity: source decision

**Decision: proceed with the direct exact-hull route below.** Starting
revision: `c8d582ff502b18745f7b0a73037458c92e705ad9` (after PR #625).
This is the pre-code investigation decision, not a claim that the proposed
compactness, inverse-continuity or realization-continuity lemmas have been
proved. The agent policy and the relevant November 19 entries of the
[side-notes ledger](side-notes-ledger.md), including the ordinary-topology
entry, were read before choosing this route.

## Exact proposed claim

For the existing finite-alphabet `LengthSubst S`, assume the existing
`hR : Bijective inflateH`, `P : PisotData S`, and `1 < S.beta` where the
flow-equivariance theorem needs it. Prove that the actual concrete map
`realizeLocal P hR` is continuous for the ordinary hull topology introduced
in PR #625.

The final theorem must not add `Continuous (desub hR)`, a local recognition
radius, compactness, or continuity of the realization as a new premise.
The investigation is to prove the required compactness and inverse lemmas
from finite tile data, then use the existing uniform contraction estimate.
Bijectivity of inflation itself remains the explicitly supplied
recognizability input; this target does not prove recognizability.

## Primary sources checked

| Source and location re-read | Relevant statement and hypothesis boundary |
| --- | --- |
| Baker, Barge and Kwapisz, [*Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces with an application to beta-shifts*](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), Ann. Inst. Fourier 56 (2006), pp. 2218-2220: Proposition 2.3, its proof and footnote 5, then Definition 3.1. | The strand-history presentation and tiling presentation are homeomorphic; uniqueness of backward histories uses recognizability, while the stable contraction identifies their lifts. Their realization takes compatible strand vertices modulo the return lattice. Footnote 5 warns that their global-attractor convention may include extra nonrecurrent orbits. Continuity of our existing legal-hull map will not by itself prove the normalized BBK correspondence or import finite fibres. |
| Barge, Diamond and Swanson, [*The branch locus for one-dimensional Pisot tiling spaces*](https://www.impan.pl/shop/en/publication/transaction/download/product/89123), Fundamenta Mathematicae 204 (2009), pp. 215-216. | They define the legal hull by allowed patches and the local topology by a small translate agreeing on a large window. Under their standing primitive and aperiodic assumptions the hull is compact metrizable and inflation is a homeomorphism. Those assumptions justify the source's recognizability statement; they must not be silently substituted for our actual `hR`. |
| Barge and Diamond, [*Cohomology in one-dimensional substitution tiling spaces*](https://arxiv.org/pdf/math/0702669), section 2, manuscript pp. 2-3. | They state compactness and metrizability of the ambient finite-prototile tiling space and continuity of literal inflation, then restrict to allowed words. Their homeomorphism statement on the primitive aperiodic hull separately invokes recognizability. This distinguishes the elementary finite-patch compactness argument from the theorem that supplies injectivity. |

These texts were opened and the indicated compactness, topology and
recognizability passages re-read for this decision. The ordinary tiling
topology and continuity of geometric realization are standard constructions.
The contribution sought here is a proof about the repository's existing
literal carrier and exact realization formula, not a new mathematical
continuity theorem.

## Chosen route: compact anchored fibres in the exact hull

Do not assume compactness of the full exact-agreement hull. In an inhabited
hull, small distinct translates give infinitely many separated exact
origin windows; an empty hull is compact. This obstruction is stronger than
mere discontinuity of the orbit map. It is enough here to prove compactness
after fixing the exact tile containing zero.

1. **Exact local limits.** Prove that a compatible limit of eventually
   constant windows still covers every point uniquely and is legal.
   Coverage and uniqueness are decided in a sufficiently large window;
   every bounded patch in the limit is eventually an identical patch of
   one of the original legal tilings. This supplies completeness or the
   equivalent closed-limit statement needed below.
2. **Anchored compactness.** For a fixed tile `p` containing zero, let
   `C_p = {T | origin T = p}`. A finite alphabet gives a positive minimum
   tile length. There are consequently only finitely many labelled
   windows of any fixed radius anchored at `p`: a bounded number of tile
   lengths and labels determines their positions from that anchor.
   Combine this finite-window property with the local-limit argument to
   prove `C_p` compact in the exact metric. Empty anchored fibres cause
   no exception.
3. **Finite possible parents.** Fix the origin tile `q` of an inflated
   tiling. Its parent's label is one of finitely many letters, and its
   location has the form
   `(q.start - length(prefix)) / beta`, with `prefix` an initial segment
   of that parent's substitution image. Thus all preimages of `C_q`
   lie in a finite union of compact anchored fibres. The preimage is
   closed, since exact inflation is continuous and `C_q` is closed.
4. **Derive exact desubstitution continuity.** Restrict inflation to
   that compact preimage. By `hR` it is a continuous bijection onto
   `C_q`, a Hausdorff metric subspace, so its inverse is continuous.
   The origin-tile fibres are also open in the exact topology, allowing
   these local inverse statements to prove continuity of the already
   defined `desub hR` on the whole exact hull. Equivalently, use those
   compact preimages to prove that inflation maps closed sets to sets
   closed on every open origin fibre, hence is a closed map; the inverse
   then has closed preimages of closed sets. No continuous-inverse
   premise is introduced.
5. **Continuity of the series.** Origin tiles are locally constant in
   the exact topology. Prove the same property for the chosen prefix
   count `offset`, using the origin tiles of a tiling and its inflation.
   Equal origin data gives the same predicate defining the chosen prefix;
   proof irrelevance then identifies the choices. Continuity of desubstitution
   then gives continuity of every level and each finite-depth prefix
   term. The existing estimate
   `norm(M^k * proj(c_k(T))) <= P.C * P.offsetBound * P.rho^k`
   is uniform in `T`, and its right side is summable. Uniform summation
   therefore proves continuity of `realVec` on the exact hull, then of
   `torusRealize` and every coordinate of the concrete solenoid map.
6. **Ordinary-hull conclusion.** Apply PR #625's proved
   `continuous_realizeLocal_iff`, using its existing target-flow
   continuity and equivariance, to obtain actual ordinary-hull
   continuity. This final step uses the established exact-source
   continuity rather than restating it as a hypothesis.

The known alternative is to construct compact Hausdorff topology on the
whole ordinary legal hull, for example from the suspension of the closed
legal-word subshift, and apply the compact-to-Hausdorff inverse theorem to
inflation. Its inverse continuity can be upgraded to exact continuity by
inflating a small aligning translation and using the already proved
small-translation rigidity control to force that translation to be zero.
The anchored route is chosen first because it directly supplies the
inverse needed for the series and does not require full ordinary-hull
compactness or separation as an intermediate deliverable.

## Assumptions and negative controls

- **Finite alphabet is substantive.** Positive individual lengths alone
  do not provide a uniform positive minimum or finitely many anchored
  windows for an infinite alphabet. The intended compactness theorem
  must retain the finite-alphabet premise.
- **Use exact fibres, not a compact exact hull.** The established theorem
  `not_continuousAt_exact_orbit` prevents treating the exact metric as
  the ordinary flow topology. Anchoring removes its continuous position
  parameter for the compactness argument; it does not identify the two
  topologies.
- **Do not assume continuity of origin in the ordinary topology.** It
  jumps when the origin crosses a tile seam. The finite series terms and
  `realVec` are to be treated on the exact hull only. The torus/solenoid
  map descends through the lattice and equivariance; a globally
  continuous ordinary-hull vector lift is not the target.
- **Keep bijectivity visible.** The periodic substitution `a -> aa`
  continuously doubles phase on a circle and is not injective. No
  inverse theorem is available merely from forward continuity or
  finite tile data.
- **Keep contraction visible.** The existing doubled-substitution
  control has no `PisotData`; continuity by uniform geometric tails
  cannot use it as an accepted model. The proof must support `rho = 0`
  as well as `0 < rho < 1`, because the existing Thue-Morse data has
  zero contraction factor.
- **No extension of source imports.** BDS periodicization, the
  normalized BBK identity, finite fibres, surjectivity and strict-system
  exclusion are not consequences of continuity alone.

## Stop/go result

**GO** for the anchored compactness, finite-parent, exact inverse,
uniform-series and concrete continuity proofs at the stated hypotheses.
Record incomplete proof attempts and compilation outcomes honestly; do
not turn a missing compactness or inverse lemma into a new field of the
final theorem. No proof code or acceptance outcome is supplied by this
source decision. No C4 or PSC claim is promoted.

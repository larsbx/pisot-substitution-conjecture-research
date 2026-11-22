# Next obligations after finite automaton hull replay

## Source decision before implementation

The starting proof tree is `7fb5bfaffab2d24bd1c0a74186438108317ca941`,
published in draft PR #649 at `c76b99d8ce29cc7afb045b85b43e6fe24d8cbccb`.
For every `k >= 2`, it interprets the finite signed tile automaton in the
actual legal hull, proves dense eventual coincidence in every concrete
solenoid fibre, and proves exact common-shift windows for every pair over
zero. The next obligations are ordinary proximality and the maximal
equicontinuous factor, simultaneous finite-fibre coincidence, and the
explicit character interface needed by the later measured conclusion.

### Primary sources and hypotheses

1. Barge--Kellendonk, *Proximality and pure point spectrum for tiling
   dynamical systems*, [author preprint](https://arxiv.org/pdf/1108.4065),
   Lemma 2.12, Theorem 2.25 and Theorem 5.4. Closed proximality and rank
   one must be kept distinct from Haar-almost-everywhere singleton fibres.
   The measured theorem has an almost-everywhere fibre-distality input;
   finite fibres alone do not discharge that input. The substitution
   argument uses geometric patch information and inflation dynamics.
2. Baker--Barge--Kwapisz, *Geometric realization and coincidence for
   reducible non-unimodular Pisot tiling spaces*,
   [published PDF](https://www.numdam.org/item/AIF_2006__56_7_2213_0.pdf),
   Theorems 4.2 and 5.1 and Corollary 5.2. The generic multiplicity and
   spectral conclusions are standard published results, but their
   realization and hypotheses must be matched to the actual factor.
   Finite-coordinate solenoid characters retain past coordinates; the
   nonunit system cannot be replaced by its zeroth torus coordinate.
3. Barge--Stimac--Williams, *Pure discrete spectrum in substitution
   tiling spaces*, [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf),
   Theorem 3.1 and Corollary 2. Legal-patch eventual coincidence provides
   the established finite-intersection mechanism. This work specializes
   and reuses that mechanism; it does not claim a new spectral criterion.

The local closure at `4b02c2d4c55fb62bf37f25aa0bbc4e44bec0b6a7` already
contains verified generic and family modules for ordinary proximality,
rotation factors and equicontinuous descent. Its acceptance rebuilt 70
project sources without project-artifact reuse. Six downstream modules
have no tile-chain imports, and their 47 existing dependencies are
byte-identical to this starting tree. Reuse those modules with a small
adapter to `C4FamilyFiniteZeroFibre`; do not import or duplicate the
alternative `TileChains`/`ZeroFibreClosure` proof. The accepted generic
topological transport uses compactness and the existing ordinary hull.
It is an explicit reused boundary, not a newly finite proof of topology.

### Proceed with these targets

- Discharge the existing zero-anchor hypotheses from the automaton
  witnesses. Derive the actual fibre/proximality equivalence, closedness,
  nonproximal fibre rank one, and unique continuous equivariant descent
  through the actual solenoid. Preserve the compact-topology dependency.
- Use finite fibres, finite intersections of open dense eventual sets,
  and a maximum of finitely many inflation depths to synchronize an
  entire fibre after finite inflation. No uniform bound in the base
  point, open synchronization neighbourhood, or full-measure statement
  is assumed by that finite construction.
- Export the existing bounded-integer-lattice finiteness lemma without
  changing its proof. Its finite image under the length functional
  bounds every equal-fibre origin displacement. A finite minimum then
  gives a positive separation for nonzero origin displacements. This
  prepares the later exact-alignment step without assuming an open
  synchronized set or introducing a sequence argument.
- After those finite witnesses compile, move their common patch to an
  actual transformed base fibre using bijective inflation and translation.
  Use the positive origin gap and the already established compact closed
  factor map to obtain an open set of synchronized fibres, if that
  assembly closes. The closed-map theorem is reused topology, explicitly
  separate from the finite gap and finite synchronization constructions.
  An open seed still does not supply Haar ergodicity of inflation.
- Construct finite-coordinate characters and their translation law on
  the actual solenoid. Reuse existing Mathlib character and approximation
  infrastructure where appropriate. Any continuous or `L2` density
  theorem must state its space and measure precisely. Pullback cannot
  be called surjective until the almost-everywhere inverse is proved.
- For the subsequent finite-Bessel route to inflation ergodicity, test
  the precise finite-algebra precursor: a continuous character periodic
  under a positive power of inflation has frequency `xi` satisfying
  `beta^p * xi = xi`, hence is trivial by the already proved dense real
  flow. Establish this with the actual shift and character maps if the
  finite proof closes; it does not itself supply Haar orthogonality,
  `L2` completeness or ergodicity.

### Controls and remaining boundary

The distinct zero-fibre seam pair remains a counterexample to universal
injectivity and universal fibre distality. Rank one counts pairwise
nonproximal subsets, not the cardinality of an exceptional fibre.
Simultaneous coincidence after inflation is not coincidence before
inflation; arbitrary fibres do not have the zero-fibre periodicity used
by the previous extraction. The finite automaton certifies unbounded
integer outputs, not a bounded enumeration of every displacement.
Characters pulled back through the factor are constant on its fibres.
Their existence and separation on the solenoid do not establish density
in the hull's invariant-measure `L2` space. Haar-a.e. singleton fibres,
the measurable inverse and surjectivity of `L2` pullback remain explicit
obligations unless new proofs in this increment discharge them.

Decision: **proceed** with reuse and the finite constructions above;
do not import a published measured theorem as an extra Lean axiom, and
do not replace a missing geometric or measure hypothesis by a label.

## Implemented topological consumers

`C4FamilyFiniteProximal` discharges the existing anchor hypotheses with
`C4FamilyFiniteZeroFibre.zero_fibre_windowWitnesses` and
`zero_fibre_common_tile`. The resulting statements hold for every `k >= 2`:

| Endpoint | Exact conclusion |
| --- | --- |
| `same_fibre_topologicallyProximal` | Equal actual solenoid images imply ordinary proximality. |
| `same_fibre_iff_topologicallyProximal` | Ordinary proximality is exactly the concrete factor's fibre relation. |
| `isClosed_topologicallyProximal` | This relation is closed in the product ordinary hull. |
| `concreteFibreRank_eq_one` | The supremum of sizes of finite pairwise nonproximal subsets of each fibre is one. Surjectivity supplies the lower bound. |
| `rotation_factor_descent` | A continuous equivariant map to a Hausdorff topological-group rotation descends uniquely, continuously and equivariantly through the actual solenoid. |
| `equicontinuous_factor_descent` | The same unique descent holds for every Hausdorff uniform equicontinuous target action. Together with equicontinuity of the actual solenoid flow, this is its intrinsic maximal-factor property. |

Seven support files are byte-identical to the accepted local closure:
the generic and family OrdinaryProximal, RotationFactor and
EquicontinuousFactor modules, and generic FibreDistal. The family
FibreDistal module changes only its imported adapter and opened namespace.
The new adapter has six theorem bodies. The alternative CoincidenceChains,
TileChains and ZeroFibreClosure modules are absent from this import graph.
The dedicated audit actively rejects their presence.

The source comparison originally found 47 unchanged existing dependencies.
This increment intentionally exports `finite_lattice_ball` in
`PeriodicPartnerRealizationFinite`, removing `private` and adding its public
docstring while preserving the proof body. The other 46 original dependency
files remain unchanged. All current dependencies are rebuilt for acceptance.

The retained fibre-distality module states an equivalence between a.e.
fibre-distality and a.e. unique preimages for an explicitly supplied measure.
Its implication retains the a.e. premise as an argument. The concrete
`zero_not_fibreDistal` control remains proved; the equivalence is not a
proof that either a.e. proposition holds.

## Synchronizing an entire finite fibre

`PeriodicPartnerFiniteCoincidence` takes a finite family of actual tilings
and one anchor. The intersection of its finitely many open dense
eventual-coincidence sets supplies a common point. Each anchor comparison
has a finite inflation depth. Their maximum advances every comparison to
the same depth, where uniqueness of the tile covering that point in the
anchor identifies all the candidate common tiles.

This gives one labelled tile shared by the entire family. Its midpoint
supplies a positive common window, and further finite inflation expands
that window to any prescribed radius. The pinned
`pow_unbounded_of_one_lt` used here is the Archimedean/Bernoulli finite
power argument in `Mathlib.Algebra.Order.Archimedean.Basic`; it does not
introduce an asymptotic-limit theorem.

The actual family specialization has the quantifiers

```text
for every k >= 2, base z and R > 0,
there exist one n and one t such that
for every T and U with g(T)=z=g(U),
  Agree R (translate t (inflate^n T)) (translate t (inflate^n U)).
```

The finite index type is the full subtype `g^-1(z)`, supplied by the
already proved finite-fibre theorem; surjectivity supplies the anchor.
The proof is not an executable enumeration of all members of that fibre,
and does not supply a uniform computable bound for `n` over all `z`.

`fibre_common_window_at_shifted_base` proves that the transformed tilings
comprise the entire fibre over `flow t (shiftS^n z)`. For an arbitrary
member of that target fibre, undo translation, use surjective iterated
inflation, then cancel the base translation and the injective solenoid
shift. This is the needed full-fibre statement, not merely an inclusion
of selected representatives. `exists_fibre_common_window` consequently
produces an actual nonempty synchronized fibre for each prescribed radius.
The selected fibre may depend on that radius.

## A finite origin gap gives an open synchronization set

`PeriodicPartnerOriginSeparation` reuses the existing uniform lift bound
`||realVec(T)|| <= K` and the exact length identity for that lift. If two
torus realizations are equal, their vector difference is an integer vector
of norm at most `2*K`. The public bounded-lattice lemma gives a finite set
of such vectors. Its image under the length functional contains every
equal-torus origin displacement.

Finite induction gives a positive lower bound for the absolute values of
its nonzero elements. Thus there is one `epsilon > 0` such that equal-torus
origin starts differing by less than `epsilon` are equal. This statement
does not say the entire integer length group is discrete in the real line:
the bounded integer coefficients are essential. The pre-existing lift
bound and length identity retain their original realization-series proofs.

`C4FamilyOpenSynchronization` centers a common tile of a synchronized
fibre. Every member then contains `(a,-ell(a)/2)`. Put

```text
delta = min(ell(a)/4, epsilon/4).
```

Nearby ordinary patches preserve that tile up to shifts `s` with
`abs(s) < delta`. Two nearby tilings over the same base have the same
torus image and origin starts `-ell(a)/2-s` and `-ell(a)/2-t`. Their
difference is smaller than `epsilon`, so the finite gap forces `s=t`.
They therefore share the same tile covering the window of radius
`ell(a)/4`.

Let `O` be the union of those source patch neighborhoods over the entire
centered fibre. The base set is

```text
W = complement (g '' complement O).
```

The existing compact ordinary hull and continuous map into the Hausdorff
solenoid make the excluded image closed. Thus `W` is open, contains the
seed base, and every preimage of every point of `W` belongs to `O`.
Using `g(O)` would guarantee only one suitable preimage and would not
prove the result. The implemented endpoint is exactly

```text
exists r > 0, exists W open and nonempty,
  for every z in W and every T,U with g(T)=z=g(U), Agree r T U.
```

This closes the geometric open-seed obligation. It reuses the established
compact closed-map theorem and adds no sequence-limit construction.
It does not yet say that fibres over `W` are singletons.

## Finite character certificates and continuous eigenfunctions

`PeriodicPartnerSolenoidCharacters` uses the exact certificate type

```lean
Certificate alpha := (Nat × alpha) →₀ Int
```

For a compatible history `z`, its phase is the finite sum of integer
multiples of the selected history/letter coordinates in `R/Z`. Its
unit-circle exponential is `character S c`, a continuous complex-valued
map. Adding certificates multiplies characters, negating them conjugates
characters, and each character respects addition of solenoid points and
has norm one. The certificate labels may be redundant because the
histories satisfy compatibility equations; no unique dual normal form
is assumed.

The exact frequency is

```text
xi(c) = sum_(n,a in support c) (c(n,a) : Real) * u(a) / beta^n.
```

The proved translation identity is

```text
character(c, flow(t,z)) = exp(2*pi*i*t*xi(c)) * character(c,z).
```

Every history level is retained. A single coordinate character separates
any two distinct solenoid histories. The generated star algebra is proved
equal to the complex linear span of all finite-certificate characters.
Mathlib's existing Stone--Weierstrass theorem then proves this span dense
in the continuous complex functions on the actual compact solenoid.
This density endpoint explicitly reuses the library approximation theorem.

`C4FamilySolenoidCharacters` pulls these functions back through the
actual continuous factor. For `k >= 1`, they are continuous unit-modulus
translation eigenfunctions with the same finite frequency formula, and
two hull points have all these eigenfunction values equal exactly when
their full solenoid images are equal. Density is asserted on the
solenoid, not in the hull's invariant-measure `L2` space.

### Actual nonunit counterexample

The family module verifies the following exact right inverse of the actual
incidence matrix:

```text
R_k(v) = (v1 - k*v2 - (v0-v2)/2, v2, (v0-v2)/2).
```

The compatible history `z_n = [R_k^n (1,0,0)]` satisfies `z_0=0`, while
its depth-one letter-2 coordinate is `1/2 mod Z`. The corresponding
single-coordinate character equals `-1`. Hence this history is nonzero
and projection to the zeroth torus coordinate is not injective for the
actual family. A depth-zero-only character argument would miss this
control.

## Finite inflation-orbit samples

`C4FamilyCharacterOrbits` proves the finite-algebra precursor to the
proposed Bessel argument. Actual solenoid inflation scales the real flow
by `beta`, directly from `M*u = beta*u`; finite iteration scales it by
`beta^n`. Composing a character with `shiftS^n` therefore gives a
continuous unit-modulus group character with real-flow frequency
`beta^n*xi(c)`.

Equality of two orbit characters implies equality of those real
frequencies. The proof uses equality at every real flow time. If their
frequency difference `d` were nonzero, time `(1/2)/d` would make the
difference `1/2 mod Z`, a contradiction. Equality at one time alone
would not suffice. A zero-frequency character is one on the already
proved dense real flow and hence everywhere by continuity. Thus a
nontrivial character has nonzero frequency, cancellation is valid, and
strict monotonicity of powers of `beta > 1` gives distinct orbit depths.

The two principal endpoints, for `k >= 1`, are:

```text
character(c) != 1 -> Injective (n |-> character(c) composed with shiftS^n)

for every N, those orbit characters indexed by Fin N are injective.
```

`orbitCharacter_norm` and `orbitCharacter_map_add` retain the actual
character properties. No Haar orthogonality or Bessel inequality is
assumed by these endpoints.

There is a concrete control for the nontriviality premise. The certificate

```text
c = single(0,2,1) - single(1,1,1)
```

is nonzero, but the actual third incidence row gives `u(1)=beta*u(2)`.
Its frequency `u(2)-u(1)/beta` is zero and its represented character is
identically one. The premise must therefore be `character(c) != 1`,
not merely `c != 0`. This also demonstrates why no unique certificate
normal form was presumed in the continuous-density proof.

## Remaining measured obligations

The remaining route is narrower than an imported coincidence-rank theorem:

1. Equip the actual solenoid with normalized Haar measure and prove that
   its actual inflation shift preserves Haar measure and is ergodic.
   The finite-character construction and distinct finite inflation-orbit
   samples are now proved; the remaining proposed route is the
   finite-Bessel argument described below.
2. For the proved open seed `W` and radius `r`, choose a finite `N_R` with
   `beta^N_R * r >= R`. The forward saturation
   `E_R = union_(n >= N_R) shiftS^n(W)` is open, has positive Haar measure,
   and is forward invariant. Inflation expands the agreement window, so
   every fibre over `E_R` agrees on radius `R`. Ergodicity would make
   `E_R` conull. Literal equality of its image with itself is unnecessary;
   the available `Ergodic.ae_empty_or_univ_of_image_ae_le` handles forward
   invariance. This is a route, not a theorem asserted by the current
   geometric modules.
3. Intersect the conull sets for natural radii. Agreement on all windows
   gives equality of tilings; surjectivity gives the unique preimage.
4. Construct a measurable inverse on a measurable conull set of singleton
   fibres. Restricting the existing closed factor map to that set yields
   a continuous closed bijection; the available restriction/homeomorphism
   lemmas give an inverse. Extending it by one fixed tiling and pushing
   Haar forward specifies an actual invariant hull measure.
5. Use `ContinuousMap.toLp_denseRange` for solenoid `L2` density and
   `Lp.compMeasurePreservingₗᵢ` for pullback. The a.e. inverse must supply
   surjectivity before the pullback can be called a unitary equivalence.

For the finite-Bessel route in step 1, an invariant function has the same
coefficient along each inflation orbit of characters. Nontrivial finite
character orbits are now excluded. Once Haar orthogonality is proved,
Bessel's inequality on any finite number `N` of distinct orbit
characters gives `N*abs(coefficient)^2 <= norm(function)^2`. An
Archimedean contradiction forces a nontrivial coefficient to vanish.
Character density would then give ergodicity. This avoids adding a new
sequence-limit contraction argument, but the Haar and `L2` premises still
have to be constructed and checked.

The separate written family spectral proof remains available through its
published criterion. This increment does not promote that written proof
to a checked invariant-measure spectral theorem, does not supply a
symbolic-shift transfer, and does not settle universal C4, BH, A1' or PSC.

## Acceptance and replay

The local acceptance freshly rebuilds **76 project library modules** and
replays **eight audit fixtures** from repository sources in an initially
empty project-output directory. All 84 source hashes, exact compiler
commands and exit codes are recorded in
`evidence/c4-finite-fibre-obligations-2026-11-21/`. No project artifact from
the earlier local closure or the development overlays is reused by this
acceptance. The compiler is the pinned Lean `4.34.0-rc2`, with the project
flags `-DautoImplicit=false -Dpp.unicode.fun=true` and Mathlib revision
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.

Existing pinned external package artifacts are reused. Thirty previously
absent Mathlib modules needed by the character construction are compiled
from those pinned sources into an external-only overlay; their source
hashes, exact commands and artifact hashes are separately recorded.
No vendored source or package revision changes.

The four new audits cover all sixteen added library modules:

| Audit | Owned declarations | Theorem constants | Independent endpoint types/owners | Refusal controls |
| --- | ---: | ---: | ---: | ---: |
| `C4FiniteProximalAudit` | 50 | 45 | 44 | 88 |
| `C4FiniteSynchronizationAudit` | 14 | 14 | 14 | 34 |
| `C4SolenoidCharactersAudit` | 72 | 63 | 28 | 64 |
| `C4CharacterOrbitsAudit` | 23 | 21 | 16 | 36 |
| **Total** | **159** | **143** | **102** | **222** |

The declaration inventories include compiler-generated declarations.
The audits recursively allow only `propext`, `Classical.choice` and
`Quot.sound`, check exact module owners, and refuse missing and wrong-typed
declarations. Altered-contract refusals protect quantifiers and premises;
they are not advertised as mathematical counterexamples to every altered
formula. The actual seam, interior-origin, nonunit-history and redundant
certificate controls are separately proved witnesses.

All sixteen added modules compile without warnings. Existing baseline
deprecation warnings remain recorded. The four earlier family,
zero-fibre, finite-automaton and actual-hull audits also pass. The unchanged
native automaton implementation and test are bound to their previous
accepted native receipt by matching source hashes; this increment adds
Lean consumers and no new executable mathematical algorithm.

Canonical repository replay:

```sh
tools/check_c4_parameter_family.sh
```

The local receipt uses the direct pinned compiler with the same project
options and source closure. It is not a claim that this session executed
the full network/bootstrap shell gate or that hosted workflows completed.
Mechanical acceptance supports project progression at this scope;
independent human review remains pending.

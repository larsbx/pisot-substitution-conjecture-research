# Zero-fibre witnesses after PR #643: local proof increment for review

## Result and scope

This candidate proves a new exact characterization of the literal family's
zero fibre, constructs a genuine interior-origin zero-fibre orbit, and
constructs common-shift witnesses between that orbit and the existing seam
anchor for every `k >= 2`. It also proves that the requested all-pairs
witness statement is equivalent to a single-anchor coincidence obligation.

**The universal witness-existence obligation remains unproved in Lean by
this candidate.** The candidate
does not prove that every zero-fibre member belongs to the constructed
orbits, or that every remaining member shares a tile with the anchor. It
does not assert coincidence rank one or the invariant-measure `L2` spectral
conclusion inside Lean. The known written family spectral proof remains
separate. All changes were prepared locally for review; no branch, PR,
comment, or merge was published.

## Exact source baseline

| Source | Inspected revision | State at inspection |
| --- | --- | --- |
| Current main | `7de25513b127d6e72709354d95c39e3d5273e2db` | Includes the merged legal-patch transfer and roadmap updates |
| PR #643 | `7a5025ed7b8104413477ea7fbd15b52206e0959c` | Open draft, mergeable; this candidate's base |
| PR #641 head | `e5d84d054a0a1b29d7a25d2bc13d05974b96c4bb` | Merged |
| PR #641 merge | `e7e6e330b80b560be70c2a5346e217f415fe4711` | Ancestor of the inspected main |

The exact-head family workflow for #643,
[run 44932455316](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/44932455316),
was still queued on the final read. The #641 head's family workflow,
[run 44926785853](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/44926785853),
was also queued in the returned run list. Merged status does not turn those
runs into hosted acceptance. The observation and the first-page scope of
the workflow query are retained in
[the final GitHub receipt](../evidence/c4-zero-fibre-witnesses-2026-11-21/github-final-observation.json).

## The exact consumers of the missing witnesses

The immediate consumer is
`Psc.ParameterFamilySolenoid.common_tile_of_zero_fibre_witnesses`
in `C4ParameterFamilySolenoid.lean`. For `k >= 2`, with two actual hull
members `T,U` realizing to the zero history, it takes auxiliary hull
members `T',U'` and one real translation `t` satisfying

```text
Agree 1 T T'
Agree 1 U U'
Agree 1 (translate t T') (translate t U')
```

and concludes that `T` and `U` contain a common labelled tile at the same
position. The auxiliary tilings need not equal the original pair.

Its downstream family declaration is
`Psc.ParameterFamilyTiling.periodic_common_tile_of_origin_witnesses`.
The generic proof is
`Psc.PeriodicPartnerLegalCoincidence.periodic_common_tile_of_origin_witnesses`.
These consume the three equalities of closed origin patches. The closed
patch retains both adjoining tiles when zero is a seam. The existing
`periodic_of_realize_zero` supplies both inflation periods, and the existing
`hull_dense_eventual` supplies the legal-patch transfer; neither is added as
an unresolved hypothesis in the new family results.

## New machine-checked results

### 1. Exact characterization of zero realization

Let `Phi` be literal inflation, let `x(T)` be the start of the chosen
right-origin tile (the tile beginning at zero when zero is a seam), and
let `ell` be the family's Perron-length functional. For every
`k >= 1`, the new family declaration

`Psc.ParameterFamilyZeroFibreWitnesses.realize_zero_iff_periodic_lattice_origin`

proves

```text
g(T) = 0
  iff
exists n > 0,
  Phi^n(T) = T and
  exists v in Z^3, x(T) = -ell · v.
```

The right side includes interior origins. It is an equivalent description,
not an additional restriction imposed on zero-fibre tilings.

The generic result is in `PeriodicPartnerPeriodicZero.lean`:
`realize_zero_iff_lattice_origin_of_periodic`. The nontrivial direction
reuses the actual realization series. Write its partial sums as `A_N` and
its stable projection as `pi_s`. The existing integer-prefix identity gives

```text
A_N - (-beta^N x_N u) in Z^d.
```

If `p` is an inflation period and `N=pj`, then `x_N=x(T)=-ell·v`.
Adding the integer vector `M^N v` and using the unstable/stable splitting
gives

```text
A_N + M^N pi_s(v) in Z^d.
```

The second summand tends to zero by the already proved Pisot contraction.
The first tends to the actual vector realization. The integer lattice is
closed, so that vector realization is integral and its torus class is zero.

The passage to the full inverse-limit history is also proved. Each
coordinate is periodic under a positive power of the torus endomorphism,
while a forward iterate sends it to the zero zeroth coordinate. Periodicity
and this eventual zero imply that the coordinate was zero. The proof does
**not** assume that the determinant-two torus map is injective. Conversely,
full zero realization makes the actual vector lift integral, and the
existing `dot_realVec` identity gives the claimed origin start.

### 2. An actual interior zero-fibre orbit for every k >= 2

`C4ParameterFamilyInteriorSeed.lean` constructs a legal tiling `I` fixed
by cubed inflation. It uses the existing nested legal seed theorem with
the singleton type-1 tile starting at `-ell(0)`. Three explicit literal
child placements return this seed to itself; its support expands in both
directions and its legality is proved on the actual hull.

The three origin tiles have starts

| Tiling | Origin tile | Origin-tile start |
| --- | --- | --- |
| `I` | type 1 | `-ell(0)` |
| `Phi(I)` | type 1 | `ell(0) - ell(1)` |
| `Phi^2(I)` | type 1 | `-ell(2)` |

For the repository's normalization,
`ell = (beta, beta^2, beta+2)`. The origin lies strictly inside the
displayed tiles. Applying the periodic lattice-origin theorem with
`v=e0` puts `I` over the full zero history. Inflation equivariance puts
every phase of its orbit over zero as well.

`Psc.ParameterFamilyInteriorZero.zero_fibre_not_all_vertices` therefore
refutes, uniformly for every `k >= 2`, the proposed shortcut

```text
g(T) = 0 implies T has a tile beginning at zero.
```

This is a counterexample in the literal legal hull, with the actual full
solenoid map. It is not merely an affine integer candidate or a model on
a different dynamical system.

### 3. Genuine common-shift witnesses for the interior orbit

Let `V` be the existing zero-fibre `1.1` seam tiling, fixed by squared
inflation. The new theorem `seam_interior_common_tile` proves that `V`
and `I` both contain the type-0 tile starting at

```text
c = ell(1) + beta * ell(1).
```

On the seam side, a second type-1 child begins at `ell(0)+ell(1)`;
inflating it gives a type-0 child at `beta*(ell(0)+ell(1))=c`.
On the interior side, the second type-1 child of the tile at `-ell(0)`
starts at `ell(0)`, using `beta*ell(0)=ell(1)`. Two more child placements
reach the same type-0 tile at `c`. The periods return the original tilings.

The generic `exactProximal_of_periodic_common_tile` then proves

```text
forall R > 0, exists t,
  Agree R (translate t V) (translate t I).
```

It starts at the midpoint of the shared tile and inflates through a large
common multiple of both periods. The shared interval grows beyond any
requested radius. The original `V,I` can be used as `T',U'` in the
requested triple; the first two agreements are reflexive.

The theorem `seam_interior_orbit_exactProximal` extends this to every
inflation phase of `I` with the same anchor `V`: at depth `4i`, the anchor
returns, while the period-three orbit advances by `i`. The fully
instantiated existence theorem is
`Psc.ParameterFamilyInteriorZero.seam_and_interior_zero_witnesses`.
It supplies actual zero-fibre tilings, not just a conditional shared-tile
lemma. These results are uniform in the parameter, rather than finite
parameter checks.

### 4. A second literal control: equal images do not mean equal origin patches

`zero_fibre_seam_control` constructs the seam tiling `V` and `Phi(V)`.
Both realize to zero. Their right-origin tiles have types 1 and 0, so
their closed origin patches differ and `Agree 1 V (Phi(V))` is false.
This holds for every `k >= 1` and also proves the constructed realization
is not globally injective.

For `k >= 2`, `seam_pair_common_tile` nevertheless gives a common type-1
tile at `ell(0)+ell(1)`, and `zero_fibre_pair_with_exact_shifts` gives
arbitrary-radius common-shift agreement for that actual pair. Thus the
failed direct-agreement implication is distinguished from the true
existential witness statement. Exceptional multiple fibres do not refute
coincidence rank one or almost-everywhere injectivity.

### 5. The witness interfaces and the single-anchor reduction

For any pair over zero and any `R>0`, the new witness module proves the
equivalence of all these predicates:

1. the three exact agreements at radius `R`;
2. the three closed-origin agreements;
3. existence of a common tile;
4. exact common-translation agreement at every positive radius;
5. the open-window version of strong regional proximality.

The equivalences retain the zero-image premises and `k >= 2`. They do
not assert that every zero-fibre pair satisfies the predicates.

`all_pair_witnesses_iff_anchor` proves that the requested all-pairs
statement is equivalent to witnesses between any one chosen zero-fibre
anchor and every other member of the zero fibre. Its transitivity step
uses the actual legal-patch theorem: two common tiles give two dense
open eventual-coincidence sets; their intersection and the existing
transitivity theorem give eventual coincidence of the outer pair;
periodicity then gives an actual common tile. Generic transitivity of
proximality is not assumed.

Combining this with the new zero characterization gives the exact
remaining target, `all_pair_witnesses_iff_periodic_lattice_anchor`:

```text
For one fixed V over zero:
  every legal inflation-periodic U with x(U) in -ell(Z^3)
  shares a labelled tile with V.
```

This is equivalent to the original all-pairs witness problem. The explicit
seam and interior constructions establish substantial instances but do not
exhaust the possible periodic integer-offset origins. No finite search or
fibre-classification theorem is silently substituted for that quantifier.

The characterization is not an enumeration. Its period and integer vector
are existential and unbounded in the theorem statement. Bounding the
origin start bounds the scalar `ell · v`, not all coordinates of `v`.
For example, with this normalization,
`v_m = (-floor(m*beta), m, 0)` satisfies `0 <= ell · v_m < beta` while
its coordinates grow. Such arithmetic candidates need not realize legal
periodic tilings. The existing finite-fibre theorem guarantees abstract
finiteness of the actual zero fibre, but this candidate supplies no
complete list, effective cutoff or verified exhaustive transition graph.

## Why an additional geometric argument is still required

The already constructed continuous, onto, finite-to-one factor does not
by itself supply the strong regional-proximal witnesses. The published
route identifies this map with the appropriate maximal equicontinuous
factor and then uses ordinary regional proximality plus the Meyer
exactification argument. The latter removes a residual small translation
using uniform discreteness of puncture differences. Ordinary local
continuity alone does not make that residual translation exactly zero.

The primary sources, their exact hypotheses, the published-target
correspondence, and a finite-cover countermodel to the abstract
finite-factor shortcut are recorded in the
[source decision](c4-zero-fibre-witness-stop-go-2026-11-21.md).
The new integer-origin characterization offers a second, more literal
route: prove anchor coincidence for every such periodic tiling. Neither
route is completed by renaming an unproved premise as a structure field.

## Minimal remaining interfaces after the geometric obligation

The [spectral interface note](c4-zero-fibre-spectral-interface-2026-11-21.md)
gives the details and primary-source links.

1. **Ordinary proximality and rank one.** Turn arbitrary exact windows
   into ordinary topological proximality. A compactness argument can
   transport an alleged nonproximal same-fibre pair to a pair with its
   first component equal to the fixed zero anchor. The anchor theorem
   would contradict the preserved separation. This proves all concrete
   fibres proximal; the maximal-factor correspondence or universal
   property then identifies the published coincidence-rank-one statement.
   The compactness transport and ordinary proximality infrastructure are
   written arguments in this candidate.
2. **Almost-everywhere singleton fibres.** Supply the substitution theorem
   connecting rank one to generic fibre multiplicity, or the relevant
   almost-everywhere fibre-distality result. Finite fibres alone do not
   prove this. A multiple exceptional zero fibre is permitted.
3. **Invariant-measure `L2`.** On a full-Haar-measure singleton-fibre set,
   construct a measurable inverse and the invariant hull measure, or
   equivalently prove surjectivity of pullback on `L2`. Solenoid characters
   then pull back to translation eigenfunctions and their span is dense.
   This one-way implication need not classify all measurable eigenvalues
   or prove the converse.

Barge--Stimac--Williams Corollary 1 and Theorem 3.1,
Barge--Kellendonk's Meyer/proximality results, and Baker--Barge--Kwapisz
Theorem 4.2 and Corollary 5.2 are published mathematical inputs, not Lean
axioms introduced here. The existing target identification is still
written: it must match the intrinsic lattice, time normalization,
history indexing, sign and the ordinary legal/minimal hull. BBK's ambient
strand space can include nonrecurrent orbits absent from that hull.

## Verification and replay

The baseline was independently rebuilt from an empty project-output
directory with Lean `4.34.0-rc2`, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. The pinned Mathlib revision is
`4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`. All nine dependency source
revisions and tracked working trees matched the lockfile. Existing
external dependency artifacts were reused; project artifacts were rebuilt.

The final replay explicitly used the Lake project options
`-DautoImplicit=false -Dpp.unicode.fun=true`. The exact #643 baseline
replay compiled 49 project modules and the
original family audit. It reproduced 23 audited owned modules,
1,053 declarations, 905 theorem constants, 35 endpoint type checks and
70 refusal controls. All audited dependencies used only `propext`,
`Classical.choice` and `Quot.sound`. The exact clean baseline's generated
proof-bank check and strict dependency-pin check passed.

The new fixture `C4ZeroFibreWitnessAudit.lean` independently spells out
38 public endpoint types, including their literal guards and existential
quantifiers, checks their owning modules, and rejects 76 wrong-type or
missing-declaration controls. It recursively checks every owned
declaration in all seven new modules: 49 declarations, including 45
theorem constants. The candidate was rebuilt against the freshly
compiled baseline closure and uses only the same three standard axioms.
Final replay counts and source
SHA-256 manifests are retained in
[the evidence directory](../evidence/c4-zero-fibre-witnesses-2026-11-21/README.md).

After applying this candidate to exact #643, the ordinary pinned Lake
replay is:

```sh
python3 tools/make_proof_bank.py --check
python3 tools/make_proof_bank.py --pins-only --require-packages
cd proof/PscVerif
lake --no-cache build \
  PscVerif.C4ParameterFamilySolenoid PscVerif.C4ParameterFamilyControls \
  PscVerif.UniversalClosureReduction PscVerif.PeriodicPartnerRealizationModels \
  PscVerif.C4ParameterFamilyZeroFibreWitnesses \
  PscVerif.C4ParameterFamilyZeroFibreControls PscVerif.C4ParameterFamilyInteriorZero
lake --no-cache env lean -DautoImplicit=false -Dpp.unicode.fun=true C4ZeroFibreWitnessAudit.lean
lake --no-cache env lean -DautoImplicit=false -Dpp.unicode.fun=true C4ParameterFamilyAudit.lean
```

The local recorded replay used the same pinned Lean binary directly with
explicit import paths, because this executor has no `elan` command. It
is a fresh project-source replay, not a claimed execution of the
repository's fully isolated shell gate or a hosted workflow. Neither
repository-wide acceptance nor hosted acceptance of this unpublished
candidate is claimed.

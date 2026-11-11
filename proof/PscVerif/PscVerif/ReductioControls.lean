import PscVerif.Degree4Floor
import PscVerif.Degree3Sector
import PscVerif.KernelCofactor
import PscVerif.Descendants
import PscVerif.StrictSystem

/-!
# Leave-one-out controls for the reductio lemmas at the `ChildSystem` level

`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`: `thm:parikh` (line 601),
`prop:cocycle` (line 705), `thm:defect-intertwiner` (line 721), `thm:deg23` (line 728),
`thm:sieve` (line 740), `prob:concentration` (line 787), `ex:nonpisot` (line 1244).
`docs/c4-solidify-stop-go-2026-11-07.md` §5 (the leave-one-out table and the candidate
non-degenerate full control `012/120/201` of `Degree4Floor.ssign_root_bound_of_primitive`)
and §6 (its non-claim, discharged here); `docs/c4-concentration-attack-2026-11-06.md` §8, rows
`KernelCofactor`, `Degree2Sector`, `Degree3Sector`, `Degree4Floor`;
`docs/c4-general-structure-2026-11-06.md` §3 (R2, R3, R3′, R5; written proofs, human review
pending), cited only for the informal remarks marked *(informal)* below.

A **reductio lemma** is a Lean theorem whose hypotheses describe a hypothetical strict
component.  For a family of such lemmas and a hypothesis `h` of it, a **leave-one-out
control** is a concrete child system meeting every hypothesis of the family except `h`,
with `h` proved false.  A control for `h` shows that the other hypotheses are jointly
satisfiable.  It does **not** show that `h` is needed for the conclusion, except where a
negative control (the conclusion fails) is stated.  A **joint-drop** control fails `h`
together with further hypotheses; it is listed as such and never as a control for `h`
alone.

## The hypotheses (namespace `Hyp`)

`Bal`, `Bal2`, `Bal3`: every state `∼₁`, `∼₂`, `∼₃`.  `Irr`: `χ_M` irreducible over `ℚ`.
`SC P`: `N_C = A + B` strongly connected; `SCRaw S`: the raw ordered `Nc S` strongly connected
(the normalisation-free form).  `PerronVec`: some `ℓ > 0` and `β` with `ℓ M = β ℓ`.
`KwCol P`, `K3Col P`, `K4Col P`: some representative with `kw`, `K₃`, `K₄` nonzero; `KwState`:
some state with `kw ≠ 0` (normalisation-free).  `Roots S β α γ`, `Distinct β α γ`,
`Moduli α γ` (`‖α‖, ‖γ‖ < 1`), `RootBound P β` (every root of `χ_S` has modulus `≤ ‖β‖`),
`Prim` (`M^k > 0`), `PisotRoot S β` (`χ_M(β) = 0`, `1 < ‖β‖`, every other root of modulus
`< 1`).  Normalisation (`N`) is the datum `P : Normalisation S`; "`N` dropped" means
`IsEmpty (Normalisation S)` with the normalisation-dependent hypotheses in their raw forms.
`kernelCofactor_of_hyps`, `degree2Sector_of_hyps`, `degree3Sector_of_hyps`,
`degree4Floor_of_hyps` apply `simple_perron_root_rep`, `rank_q2`, `deg23_iii_of_ne`,
`theoremA_of_primitive` from exactly these predicates.

## The controls

* `rotSys k`, `k = 0, 1, 2` (`rotSubst`: `0 ↦ 012`, `1 ↦ 120`, `2 ↦ 201`; `M = J`,
  `χ_M = X²(X − 3)`, primitive, reducible): the states `(σ^{k+1} a, σ^{k+1} b)`, `a ≠ b`,
  with children `(σ^{k+1} x_i, σ^{k+1} y_i)` for `x = σ a`, `y = σ b`, positionwise
  (`rotW_eq`).  `N_C = S = J` on the three representatives.  The first defect degree is
  `k + 2`: the states are `∼₁` with `kw ≠ 0` (`k = 0`), `∼₂` with `K₃ ≠ 0` (`k = 1`), and `∼₃`
  with `K₄ ≠ 0` (`k = 2`).  Only `rotSys 0` is a zero-return system (`rot0_red`).  For
  `k = 1, 2` the children are coarser than `red` (`rot1_not_red`, `rot2_not_red`).  A
  `ChildSystem` takes any balanced factorization.  `rotSubst` is
  `Psc.StrictSystem.cycSubst` (`rotSubst_eq_cycSubst`), and `rotSys 0` is the swap closure of
  the strict component `Psc.StrictSystem.cycC` with `R = cycC` (`rot0_states_eq_cycC`,
  `rot0_reps_eq_cycC`, `rot0_strictComponent`): the `Irr` rows met by `rotSys 0` are met by
  a strict component (`StrictComponent rotSubst cycC`); its reachability from a seed, i.e.
  membership in `B_σ`, is not proved.
* `towSys` (plastic tower): `plasticSubst` (`0 ↦ 1`, `1 ↦ 2`, `2 ↦ 01`), the states
  `(aₙ, aₙ₊₁)`, `n = 4, 5, 6`, with `aₙ = σⁿ(0)` (`tow_tower`) and their swaps.  The children
  come from `σ(aₙ) = aₙ₊₁` and `a₇ = a₄a₅`, `a₈ = a₅a₆`.  The system is unbalanced, all tracks
  are nonempty, and `N_C` is the plastic incidence matrix (`tow_nrep`).
* `diagSys`: the coincident letters `([a], [a])` over `plasticSubst`; it has no
  normalisation.
* `bpaSys`: nine balanced pairs over `bpaSubst` (`0 ↦ 01`, `1 ↦ 201`, `2 ↦ 0`; primitive,
  `χ_M = X³ − 2X² − 1`, the census cubic, Pisot), forming the zero-return system
  (`Psc.Reduction.redSystem`) on the zero-return closure of `(01, 10)` (`bpa_reachable`).  It
  contains the coincidences `([a], [a])`, so it has no normalisation.
* `cyc3Norm`, `cyc4Norm` (`Psc.SectorBridge`): the three relabellings of `wTPair`, `w4Pair`
  over the 3-cycle `cycSubst` (`0 ↦ 1 ↦ 2 ↦ 0`, `χ_M = X³ − 1`, not primitive).  Here:
  `cyc_not_irr`, `cyc_not_prim`, `cyc_root_norm` (every root has modulus `1`), `cyc_roots`
  (`1, ζ, ζ²`), `cyc_rootBound` (`RootBound` at `β = 1`).
* Existing: `Psc.Degree4Floor.plasticEmpty`, `Psc.Degree3Sector.censusEmpty` (empty systems),
  `Psc.SignedIntertwiner.wT`, `exA`, `Psc.Degree4Floor.w4_controls` (`Psc.Defect4.w4Norm`
  over the identity substitution).

## Leave-one-out tables (hypothesis dropped → control → status)

**`Psc.KernelCofactor` representative theorems** (`kernelCofactor_leave_one_out`):

| dropped | control | status |
| --- | --- | --- |
| `N` | `diagSys` (with `SCRaw`) | Lean, non-degenerate |
| `Bal` | `towSys` | Lean, non-degenerate |
| `C ≠ ∅` | `plasticEmpty` | Lean; degenerate by necessity (only `C = ∅` fails it) |
| `SC` | none | **unknown**: a sink component of any instance is a full control *(informal)* |
| `Irr` | `rotSys 0` (primitive), `wT` | Lean, non-degenerate |
| `PerronVec` | none | **not independent**: implied by `Irr` *(Perron–Frobenius, informal)*; for primitive `σ`, `perronVec_of_prim` |

**`Psc.Degree2Sector` `Sector` theorems** (`degree2Sector_leave_one_out`):

| dropped | control | status |
| --- | --- | --- |
| `N` | `bpaSys` (with `KwState`; primitive Pisot `σ`) | Lean, non-degenerate |
| `Bal` | `towSys` | Lean, non-degenerate |
| `KwCol` | `plasticEmpty` | Lean, **degenerate**; a non-empty one is unknown |
| `Irr` | `rotSys 0` (primitive), `exA` | Lean; with `rotSys 0`, `χ_{Λ²M} ∤ χ_S` (negative control `wedge2_dvd_needs_irreducible`) |

**`Psc.Degree3Sector.deg23_iii_of_ne`** (`degree3Sector_leave_one_out`):

| dropped | control | status |
| --- | --- | --- |
| `N` | none | **not constructed** |
| `Bal2` | `towSys` | Lean, non-degenerate; it fails `Bal` too (a control keeping `Bal` falls under the first item of "Not proved here") |
| `K3Col` | `censusEmpty` | Lean, **degenerate**; a non-empty one is unknown |
| `Irr` | none for `Irr` alone | **not constructed** (its required shape: "Not proved here") |
| `Irr`, `Distinct` jointly | `rotSys 1` | Lean (roots `3, 0, 0`; `rot_no_three_roots`) |
| `Irr`, `Moduli` jointly | `cyc3Norm` | Lean (roots `1, ζ, ζ²`, all of modulus `1`; `RootBound` at `β = 1`; not primitive) |
| `Roots`, `Distinct`, `Moduli` alone | none | **unknown**; dropping `Moduli` forces the one-outside class with `r(C) = 3` *(informal; open)* |
| `RootBound` | none | **not independent** for primitive `σ` (`deg23_iii_of_primitive`) |

**`Psc.Degree4Floor.theoremA_of_primitive` and `sieve4_of_primitive`** (Pisot-root form;
`RootBound`, the hypothesis `hρ` of `sieve4`, holds on every row;
`degree4Floor_leave_one_out`):

| dropped | control | status |
| --- | --- | --- |
| `N` | none | **not constructed** |
| `Bal3` | `towSys` | Lean, non-degenerate; it fails `Bal` too |
| `K4Col` | `plasticEmpty` | Lean, **degenerate**; a non-empty one is unknown (`m0_no_degree4` gives content) |
| `Irr` | `rotSys 2` | Lean, non-degenerate; `det M = 0`, so the conclusion `\|det M\| = 1` fails (negative control `theoremA_needs_irreducible`) |
| `Irr`, `Prim`, `PisotRoot` jointly | `cyc4Norm`; `w4Norm` | Lean for `cyc4Norm`; for `w4Norm` see below |
| `Prim` (or `RootBound`) | none | **not independent**: `Irr` and `PisotRoot` force primitivity *(informal)* |
| `PisotRoot` | none | **unknown**: forces the one-outside class with `\|det M\| = 1`, `r(C) = 4` *(informal; open)* |
| `SC` | none | **unknown**: a sink component of any instance meets every other hypothesis, or all but `K4Col` *(informal)* |

`w4Norm` is over the identity substitution: `Psc.Degree4Floor.w4_controls` proves `Bal3`,
`K4Col`, `RootBound` at `1` and `¬Irr`; that `Prim` and `PisotRoot` fail for the identity
is not restated here.  `SC` is not checked on `cyc4Norm` or `w4Norm`.

**`Psc.Degree4Floor.sieve4` in its literal three-root form** (roots `β, α, γ`, `α ≠ γ`,
`1 < ‖β‖`, `‖α‖, ‖γ‖ < 1`, and `hρ`).  The rows `Bal3`, `K4Col` carry over (`towSys`,
`plasticEmpty` over the plastic roots).  The `Irr` row does **not**: on `rotSys 2` no two
distinct roots of `χ_M` lie in the unit disc (`rot_no_sieve4_roots`, a conjunct of the
`rotSys 2` row), so `rotSys 2` drops `Irr` jointly with the root hypotheses.  `cyc4Norm`
drops `Irr` jointly with the moduli (roots `1, ζ, ζ²`).  An `Irr`-only control of `sieve4`
is **not constructed**; it needs `χ_M = X·g` with `g` an irreducible quadratic Pisot
polynomial (the derivation in "Not proved here"), and then `det M = 0`, so the conclusion
`|det M| = 1` would fail on it.

**`Psc.Degree4Floor.ssign_root_bound_of_primitive`**: `rotSys 0` is a **non-degenerate full
control** (`ssign_root_bound_full_control`).  The bound is derived by the theorem itself and
is attained (`χ_S(3) = 0`).  Its balance hypothesis is stronger than the conclusion needs:
`ssign_root_bound_of_top_ne_nil` replaces it by nonempty top tracks (the known route
`Psc.SignedCocycle.Normalisation.cocycle_spectral_bound`), and `towSys` is an unbalanced
instance (`ssign_root_bound_without_balance`).

## Proved here, in full

* `nrep_apply`, `ssign_apply` (`N_C`, `S` as counts of children); `stronglyConnected_of_three`
  (a three-vertex digraph with a Hamiltonian cycle).
* Rotation systems: `rotW_eq`; `rotSys`, `rotNorm` (by `decide`); `rotSubst_eq_cycSubst`,
  `rot0_states_eq_cycC`, `rot0_reps_eq_cycC`, `rot0_strictComponent`; `rot0_red`, `rot1_not_red`,
  `rot2_not_red`;
  `rot_inc`, `rot_incQ`, `rot_charpoly` (`χ_M = X³ − 3X²`), `rot_aeval`, `rot_root_iff`,
  `rot_not_irreducible`, `rot_det`, `rot_incZ_det`, `rot_pisot`, `rot_no_three_roots`,
  `rot_no_sieve4_roots`, `rot_primitive`; `rot_rep`, `rot_card`, `rot_nrep`, `rot_ssign`
  (`N_C = S = J`), `rot_sc`; `rot_left` (`ℓ = 1`, `β = 3`), `rot_bound` (`ρ(S) ≤ 3`),
  `rot_ssign_root` (`χ_S(3) = 0`); `rot_equiv1`, `rot1_equiv2`, `rot2_equiv3`, `rot0_kw`,
  `rot1_k3`, `rot2_k4`.
* Plastic tower: `towSys`, `towNorm`, `tow_tower`, `tow_rep`, `tow_nrep`, `tow_not_balanced`,
  `tow_top_ne_nil`, `tow_sc`, `tow_kw`, `tow_k3`, `tow_k4`, `tow_incQ`.
* `diagSys`, `diag_no_norm`, `diag_balanced`, `diag_sc`; `bpaSys`, `bpa_no_norm`,
  `bpa_balanced`, `bpa_kw`, `bpa_inc`, `bpa_charpoly`, `bpa_irreducible` (from
  `Psc.Degree3Sector.census_irreducible`), `bpa_primitive` (`M³ > 0`), `bpa_pisot`,
  `bpa_reachable` (`bpaStates` is exactly the zero-return closure of `(01, 10)`).
* Over `cycSubst`: `incQ_of_cyc`, `cyc_root_norm`, `cyc_not_irr`, `cyc_no_pisot`,
  `cyc_no_moduli`, `cyc_not_prim`, `cyc_rootBound`, `cyc_roots`.
* The four tables, the two negative controls, `ssign_root_bound_full_control`,
  `ssign_root_bound_of_top_ne_nil`, `ssign_root_bound_without_balance`, `perronVec_of_prim`
  (a restatement of `Psc.PerronExistence.exists_pos_left_eigen_inc`), `plastic_roots_of`.

## Not proved here

* **Any row keeping `N`, the balance hypothesis, nonemptiness of `C` (implied by a nonzero
  defect column) and `Irr`.**  Such a control is a non-empty normalised closed balanced
  system over a substitution with irreducible `χ_M`.  None is known.  *(informal)* Over a
  PIP it would be a three-letter PSC counterexample, by the route in the docstring of
  `Psc.Degree2Sector` (formal productivity; human review pending).  For primitive `σ`: if
  both non-Perron roots lie outside the unit disc, R3 excludes it; in the one-outside class
  it is open (R2 forces `K₂ ≡ 0` there; the exact window search of
  `docs/c4-closed-component-search-2026-11-07.md` finds no strict system with `K₂ = 0` on
  every state and every state of length `≤ 13` among the non-synchronizing specimens with
  images `≤ 3`, a window observation, not a verdict).
  R2 and R3 assume `σ` primitive.  If `χ_M` is irreducible, `M` is irreducible as a
  nonnegative matrix, and it is imprimitive only with period `3`, i.e. `χ_M = X³ − c` (under
  a relabelling, `σ` maps each letter to a power of the next letter).  That case is not
  covered by R3 and is not examined here; it bears only on rows without a Pisot hypothesis
  (the `KernelCofactor` rows `SC`, `PerronVec`), since `Irr` with `PisotRoot` forces
  primitivity.  This item covers the `SC`, `PerronVec`, `Roots`, `Distinct`, `Moduli`,
  `RootBound`, `Prim`, `PisotRoot` rows, and non-empty versions of the defect rows.  For the
  defect rows only the empty systems are given.
* **`Irr` alone for `deg23_iii_of_ne`, and for `sieve4`** *(informal derivation, not
  formalized)*.  Let the integral `χ_M` be reducible, with pairwise distinct roots `β, α, γ`
  (hence all its roots) and `‖α‖, ‖γ‖ < 1`; for `sieve4` the distinctness follows from
  `α ≠ γ` and `1 < ‖β‖`.  It has an integer root `k` (Gauss, rational roots).  If `k ∈ {α, γ}`
  then `k = 0`.  If `k = β`, then `α + γ` and `αγ` are integers (Vieta), and `‖αγ‖ < 1` gives
  `αγ = 0`.  Either way one of `α, γ`, say `α`, is `0`, and `χ_M = X·g` with `g(0) = βγ ≠ 0`.
  If `g` were reducible, `γ` would be an integer of modulus `< 1`, i.e. `γ = 0 = α`.  So `g` is
  an irreducible quadratic Pisot polynomial (`‖βγ‖ ≥ 1` gives `‖β‖ > 1`) and `det M = 0`.
  `rotSys 1`, `rotSys 2` have the double root `0`, so they are not of this form; a control
  for `Irr` alone needs a new construction, and for `sieve4` it would be a negative control
  as well (`|det M| = 1` fails).  None was searched for.
* **`N` for `deg23_iii_of_ne` and `theoremA_of_primitive`.**  A control that is not a full
  control in disguise needs coincident states.  A noncoincident child system can be
  swap-closed (the children of `T.swap` taken as the swapped children of `T`) and then
  normalised.  So the control needs `∼₂` (resp. `∼₃`) states, some with `K₃ ≠ 0` (resp.
  `K₄ ≠ 0`), and coincidences, over an irreducible Pisot `σ`.  No replayable search for one
  has been run, and nothing is claimed about its existence.
* `rotSys 1`, `rotSys 2` are not strict components of `B_σ`: their children are not
  zero-return blocks.  The reductio lemmas restated on strict systems and components, with
  every structural hypothesis discharged, are in `Psc.StrictSystem` ((g), (h)); their
  register is `docs/c4-reductio-lemmas-2026-11-07.md`.  `rotSys 0` is the zero-return
  system of the pinned carrier, but `χ_M` is reducible, so it is not a PIP specimen.  `bpaSys` is the closure of `(01, 10)`
  only: of the seeds of `Psc.Descendants.bpaStates bpaSubst` it contains `(01, 10)` and
  `(10, 01)` alone, and nothing is claimed about the rest of `B_σ`.
* That `PerronVec` follows from `Irr` for imprimitive `M`, that `Irr` with `PisotRoot` forces
  primitivity, and the sink-component arguments are informal.
-/

namespace Psc.ReductioControls

open Matrix Polynomial Psc.Binomial Psc.Incidence Psc.SignedCocycle Psc.ParikhRank
  Psc.Degree2Sector

/-! ### `N_C` and `S` as counts of children -/

theorem nrep_apply {α : Type*} [DecidableEq α] {S : ChildSystem α} (P : Normalisation S)
    (i j : P.Rep) : P.Nrep i j = (S.children j.1).count i.1 + (S.children j.1).count i.1.swap :=
  rfl

theorem ssign_apply {α : Type*} [DecidableEq α] {S : ChildSystem α} (P : Normalisation S)
    (i j : P.Rep) :
    P.Ssign i j = ((S.children j.1).count i.1 : ℤ) - (S.children j.1).count i.1.swap :=
  rfl

/-- A three-vertex digraph with the cycle `a → b → c → a` of positive entries (`N x y > 0`
read as an edge `x → y`) is strongly connected. -/
theorem stronglyConnected_of_three {ι : Type*} [Fintype ι] [DecidableEq ι] {N : Matrix ι ι ℝ}
    {a b c : ι} (h : ∀ i, i = a ∨ i = b ∨ i = c) (hab : 0 < N a b) (hbc : 0 < N b c)
    (hca : 0 < N c a) : Psc.PerronCore.StronglyConnected N := fun i j => by
  rcases h i with rfl | rfl | rfl <;> rcases h j with rfl | rfl | rfl
  exacts [.tail (.tail (.single hab) hbc) hca, .single hab, .tail (.single hab) hbc,
    .tail (.single hbc) hca, .tail (.tail (.single hbc) hca) hab, .single hbc,
    .single hca, .tail (.single hca) hab, .tail (.tail (.single hca) hab) hbc]

/-! ### The rotation substitution `012/120/201` and its inflated systems -/

/-- `0 ↦ 012`, `1 ↦ 120`, `2 ↦ 201`. -/
def rotSubst : Fin 3 → List (Fin 3) := ![[0, 1, 2], [1, 2, 0], [2, 0, 1]]

/-- `rotW k a = σ^{k+1}(a)` (`rotW_eq`), written out. -/
def rotW : Fin 3 → Fin 3 → List (Fin 3) :=
  ![rotSubst,
    ![[0, 1, 2, 1, 2, 0, 2, 0, 1], [1, 2, 0, 2, 0, 1, 0, 1, 2], [2, 0, 1, 0, 1, 2, 1, 2, 0]],
    ![[0, 1, 2, 1, 2, 0, 2, 0, 1, 1, 2, 0, 2, 0, 1, 0, 1, 2, 2, 0, 1, 0, 1, 2, 1, 2, 0],
      [1, 2, 0, 2, 0, 1, 0, 1, 2, 2, 0, 1, 0, 1, 2, 1, 2, 0, 0, 1, 2, 1, 2, 0, 2, 0, 1],
      [2, 0, 1, 0, 1, 2, 1, 2, 0, 0, 1, 2, 1, 2, 0, 2, 0, 1, 1, 2, 0, 2, 0, 1, 0, 1, 2]]]

theorem rotW_eq (k a : Fin 3) : rotW k a = (subst rotSubst)^[k] (rotSubst a) := by
  fin_cases k <;> fin_cases a <;> decide

/-- The six ordered pairs `(σ^{k+1} a, σ^{k+1} b)`, `a ≠ b`. -/
def rotStates (k : Fin 3) : Finset (List (Fin 3) × List (Fin 3)) :=
  {(rotW k 0, rotW k 1), (rotW k 1, rotW k 2), (rotW k 2, rotW k 0),
    (rotW k 1, rotW k 0), (rotW k 2, rotW k 1), (rotW k 0, rotW k 2)}

/-- The representatives `(σ^{k+1} a, σ^{k+1} (a + 1))`. -/
def rotReps (k : Fin 3) : Finset (List (Fin 3) × List (Fin 3)) :=
  {(rotW k 0, rotW k 1), (rotW k 1, rotW k 2), (rotW k 2, rotW k 0)}

/-- The children of `(σ^{k+1} a, σ^{k+1} b)`: pair `σ a` and `σ b` positionwise (they differ
at every position) and inflate each letter pair to `(σ^{k+1} x, σ^{k+1} y)`.  The letters
`a, b` are read off the first letters (`σ^{k+1} a` starts with `a`). -/
def rotChildren (k : Fin 3) (T : List (Fin 3) × List (Fin 3)) :
    List (List (Fin 3) × List (Fin 3)) :=
  ((rotSubst (T.1.headD 0)).zip (rotSubst (T.2.headD 0))).map fun p => (rotW k p.1, rotW k p.2)

def rotSys (k : Fin 3) : ChildSystem (Fin 3) where
  s := rotSubst
  C := rotStates k
  children := rotChildren k
  top := by fin_cases k <;> decide
  bot := by fin_cases k <;> decide
  closed := by fin_cases k <;> decide
  nonempty := by fin_cases k <;> decide

def rotNorm (k : Fin 3) : Normalisation (rotSys k) where
  R := rotReps k
  swap_mem := by fin_cases k <;> decide
  children_swap := by fin_cases k <;> decide
  sub := by fin_cases k <;> decide
  cover := by fin_cases k <;> decide
  not_both := by fin_cases k <;> decide

/-- `rotSubst` is the substitution `Psc.StrictSystem.cycSubst` (`012/120/201`). -/
theorem rotSubst_eq_cycSubst : rotSubst = Psc.StrictSystem.cycSubst := rfl

/-- The states of `rotSys 0` are the swap closure of the strict component
`Psc.StrictSystem.cycC`. -/
theorem rot0_states_eq_cycC :
    (rotSys 0).C = Psc.StrictSystem.swapClosureF Psc.StrictSystem.cycC := by
  decide

/-- The representatives of `rotNorm 0` are exactly `Psc.StrictSystem.cycC`. -/
theorem rot0_reps_eq_cycC : (rotNorm 0).R = Psc.StrictSystem.cycC := by
  decide

/-- So `rotSys 0` comes from a strict component: `Psc.StrictSystem.cyc_strictComponent`. -/
theorem rot0_strictComponent : Psc.StrictSystem.StrictComponent rotSubst Psc.StrictSystem.cycC :=
  Psc.StrictSystem.cyc_strictComponent

/-- `rotSys 0` is the zero-return system of the pinned carrier `012/120/201`. -/
theorem rot0_red : ∀ T ∈ (rotSys 0).C,
    (rotSys 0).children T = Psc.Reduction.red (subst rotSubst T.1) (subst rotSubst T.2) := by
  decide

/-- For `k = 1` the children are coarser than the zero-return blocks. -/
theorem rot1_not_red : (rotSys 1).children (rotW 1 0, rotW 1 1) ≠
    Psc.Reduction.red (subst rotSubst (rotW 1 0)) (subst rotSubst (rotW 1 1)) := by
  decide

/-- For `k = 2` the children are coarser than the zero-return blocks. -/
theorem rot2_not_red : (rotSys 2).children (rotW 2 0, rotW 2 1) ≠
    Psc.Reduction.red (subst rotSubst (rotW 2 0)) (subst rotSubst (rotW 2 1)) := by
  decide

theorem rot_inc : inc rotSubst = Matrix.of fun _ _ => 1 := by
  ext a c; fin_cases a <;> fin_cases c <;> rfl

theorem rot_incQ (k : Fin 3) : incQ (rotSys k) = Matrix.of fun _ _ => (1 : ℚ) := by
  ext a c; fin_cases a <;> fin_cases c <;> rfl

/-- `χ_J = X³ − 3X²`. -/
theorem rot_charpoly (k : Fin 3) : (incQ (rotSys k)).charpoly = X ^ 3 - C 3 * X ^ 2 := by
  rw [Psc.Cyclicity.charpoly_fin_three, rot_incQ]
  simp [Matrix.trace_fin_three, Matrix.det_fin_three, Psc.Cyclicity.wedge2,
    Psc.Cyclicity.pairFst, Psc.Cyclicity.pairSnd]
  rw [map_ofNat]; norm_num

theorem rot_primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc rotSubst ^ k) a c :=
  ⟨1, le_rfl, by rw [pow_one, rot_inc]; intro a c; simp⟩

theorem rot_rep (k : Fin 3) (i : (rotNorm k).Rep) :
    i.1 = (rotW k 0, rotW k 1) ∨ i.1 = (rotW k 1, rotW k 2) ∨ i.1 = (rotW k 2, rotW k 0) := by
  have := i.2
  simpa [rotNorm, rotReps] using this

theorem rot_card (k : Fin 3) : Fintype.card (rotNorm k).Rep = 3 := by
  rw [Fintype.card_coe]; fin_cases k <;> decide

/-- `N_C = J`: each representative's children are the three representatives. -/
theorem rot_nrep (k : Fin 3) (i j : (rotNorm k).Rep) : (rotNorm k).Nrep i j = 1 := by
  rw [nrep_apply]
  rcases rot_rep k i with hi | hi | hi <;> rcases rot_rep k j with hj | hj | hj <;>
    rw [hi, hj] <;> fin_cases k <;> decide

/-- `S = J`: no child is a swapped representative. -/
theorem rot_ssign (k : Fin 3) (i j : (rotNorm k).Rep) : (rotNorm k).Ssign i j = 1 := by
  rw [ssign_apply]
  rcases rot_rep k i with hi | hi | hi <;> rcases rot_rep k j with hj | hj | hj <;>
    rw [hi, hj] <;> fin_cases k <;> decide

theorem rot_equiv1 (k : Fin 3) : ∀ T ∈ (rotSys k).C, Equiv1 T.1 T.2 := by
  fin_cases k <;> decide

theorem rot1_equiv2 : ∀ T ∈ (rotSys 1).C, Equiv2 T.1 T.2 := by decide

theorem rot2_equiv3 : ∀ T ∈ (rotSys 2).C, Psc.Defect4.Equiv3 T.1 T.2 := by
  decide

theorem rot_aeval (k : Fin 3) (z : ℂ) :
    aeval z (incQ (rotSys k)).charpoly = z ^ 2 * (z - 3) := by
  rw [rot_charpoly]; simp [map_ofNat]; ring

theorem rot_root_iff (k : Fin 3) (z : ℂ) :
    aeval z (incQ (rotSys k)).charpoly = 0 ↔ z = 0 ∨ z = 3 := by
  rw [rot_aeval, mul_eq_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero]

theorem rot_not_irreducible (k : Fin 3) : ¬ Irreducible (incQ (rotSys k)).charpoly := fun h =>
  Psc.Cyclicity.not_isRoot_of_irreducible _ h 0 (by rw [rot_charpoly]; simp)

theorem rot_det (k : Fin 3) : (incQ (rotSys k)).det = 0 := by
  rw [rot_incQ, Matrix.det_fin_three]; simp

/-- `3` is a Pisot root of `χ_M = X²(X − 3)`: `‖3‖ > 1`, and the other root is `0`. -/
theorem rot_pisot (k : Fin 3) : aeval (3 : ℂ) (incQ (rotSys k)).charpoly = 0 ∧ 1 < ‖(3 : ℂ)‖ ∧
    ∀ z : ℂ, aeval z (incQ (rotSys k)).charpoly = 0 → z ≠ 3 → ‖z‖ < 1 := by
  refine ⟨(rot_root_iff k 3).2 (Or.inr rfl), by norm_num, fun z hz hz3 => ?_⟩
  rcases (rot_root_iff k z).1 hz with rfl | rfl
  · simp
  · exact absurd rfl hz3

/-- `ℓ = (1, 1, 1)` is a positive left eigenvector of `J` for `3`. -/
theorem rot_left : (fun _ => (1 : ℝ)) ᵥ* (inc (rotSys 0).s).map (Nat.cast : ℕ → ℝ) =
    (3 : ℝ) • fun _ => (1 : ℝ) := by
  funext c
  show ∑ a, (1 : ℝ) * ((inc rotSubst a c : ℕ) : ℝ) = 3 * 1
  rw [rot_inc]; simp

theorem rot_left' (k : Fin 3) :
    (fun _ => (1 : ℝ)) ᵥ* (inc (rotSys k).s).map (Nat.cast : ℕ → ℝ) =
      (3 : ℝ) • fun _ => (1 : ℝ) :=
  rot_left

theorem rot_sc (k : Fin 3) :
    Psc.PerronCore.StronglyConnected ((rotNorm k).Nrep.map (Nat.cast : ℕ → ℝ)) :=
  Psc.CocycleSpectrum.nrep_stronglyConnected _ ⟨1, le_rfl, fun i j => by
    rw [pow_one, rot_nrep]; exact one_pos⟩

/-- `ρ(S) ≤ 3` on `rotSys k` (`Psc.Degree3Sector.roots_ssign_le` with `ℓ = 1`). -/
theorem rot_bound (k : Fin 3) :
    ∀ μ : ℂ, aeval μ (SsignQ (rotNorm k)).charpoly = 0 → ‖μ‖ ≤ ‖(3 : ℂ)‖ := fun μ hμ => by
  have h := Psc.Degree3Sector.roots_ssign_le (rotNorm k) (fun _ => 1) (fun _ => one_pos) 3
    (rot_left' k) (rot_equiv1 k) μ hμ
  simpa using h

/-- `3` is a root of `χ_S` (`S = J` has the left eigenvector `(1, 1, 1)`): the bound of
`rot_bound` is attained. -/
theorem rot_ssign_root (k : Fin 3) : aeval (3 : ℂ) (SsignQ (rotNorm k)).charpoly = 0 := by
  have h := Psc.ConcentrationAlgebra.isRoot_of_left_eigen
    ((SsignQ (rotNorm k)).map (algebraMap ℚ ℂ)) 3 (fun _ => 1) (fun h => by
      have := congrFun h (⟨(rotW k 0, rotW k 1), by fin_cases k <;> decide⟩ : (rotNorm k).Rep)
      simp at this) (by
      funext j
      simp only [vecMul, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul,
        mul_one, SsignQ, rot_ssign, Int.cast_one, map_one, Finset.sum_const, Finset.card_univ,
        rot_card, nsmul_eq_mul, Nat.cast_ofNat])
  rwa [Matrix.charpoly_map, eval_map_algebraMap] at h

theorem rot0_kw : ∃ j : (rotNorm 0).Rep, Psc.Intertwiner2.kw j.1.1 j.1.2 ≠ 0 :=
  ⟨⟨(rotW 0 0, rotW 0 1), by decide⟩, fun h => by
    have := congrFun h 0
    revert this; decide⟩

/-- `K₃(σ²0, σ²1)_{010} = 2`. -/
theorem rot1_k3 : ∃ j : (rotNorm 1).Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0 :=
  ⟨⟨(rotW 1 0, rotW 1 1), by decide⟩, fun h => by
    have := congrFun (congrFun (congrFun h 0) 1) 0
    have k : Psc.Intertwiner3.K3 (rotW 1 0) (rotW 1 1) 0 1 0 = 2 := by decide
    simp [Lie3.k3Vec, k] at this⟩

/-- `K₄(σ³0, σ³1)_{1211} = 27`. -/
theorem rot2_k4 : ∃ j : (rotNorm 2).Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0 :=
  ⟨⟨(rotW 2 0, rotW 2 1), by decide⟩, fun h => by
    have := congrFun (congrFun (congrFun (congrFun h 1) 2) 1) 1
    have k : Psc.Defect4.K4 (rotW 2 0) (rotW 2 1) 1 2 1 1 = 27 := by decide
    simp [Psc.Defect4Lie.k4Vec, k] at this⟩

/-! ### The plastic tower: an unbalanced normalised system -/

/-- `(a₄, a₅) = (12, 201)`, with `aₙ = σⁿ(0)` for `σ = plasticSubst`. -/
def towA : List (Fin 3) × List (Fin 3) := ([1, 2], [2, 0, 1])
/-- `(a₅, a₆) = (201, 0112)`. -/
def towB : List (Fin 3) × List (Fin 3) := ([2, 0, 1], [0, 1, 1, 2])
/-- `(a₆, a₇) = (0112, 12201)`. -/
def towC : List (Fin 3) × List (Fin 3) := ([0, 1, 1, 2], [1, 2, 2, 0, 1])

theorem tow_tower :
    towA = ((subst plasticSubst)^[4] [0], (subst plasticSubst)^[5] [0]) ∧
      towB = ((subst plasticSubst)^[5] [0], (subst plasticSubst)^[6] [0]) ∧
      towC = ((subst plasticSubst)^[6] [0], (subst plasticSubst)^[7] [0]) := by
  decide

/-- `σ(aₙ) = aₙ₊₁`, `a₇ = a₄ a₅` and `a₈ = a₅ a₆`. -/
def towChildren (T : List (Fin 3) × List (Fin 3)) : List (List (Fin 3) × List (Fin 3)) :=
  if T = towA then [towB] else if T = towB then [towC] else if T = towC then [towA, towB]
  else if T = towA.swap then [towB.swap] else if T = towB.swap then [towC.swap]
  else if T = towC.swap then [towA.swap, towB.swap] else []

def towSys : ChildSystem (Fin 3) where
  s := plasticSubst
  C := {towA, towB, towC, towA.swap, towB.swap, towC.swap}
  children := towChildren
  top := by decide
  bot := by decide
  closed := by decide
  nonempty := by decide

def towNorm : Normalisation towSys where
  R := {towA, towB, towC}
  swap_mem := by decide
  children_swap := by decide
  sub := by decide
  cover := by decide
  not_both := by decide

theorem tow_rep (i : towNorm.Rep) : i.1 = towA ∨ i.1 = towB ∨ i.1 = towC := by
  have := i.2
  simpa [towNorm] using this

def towRepA : towNorm.Rep := ⟨towA, by decide⟩
def towRepB : towNorm.Rep := ⟨towB, by decide⟩
def towRepC : towNorm.Rep := ⟨towC, by decide⟩

/-- The relabelling `towA, towB, towC ↦ 0, 1, 2`. -/
def towIdx (i : towNorm.Rep) : Fin 3 := if i.1 = towA then 0 else if i.1 = towB then 1 else 2

/-- `N_C` is the plastic incidence matrix under `towIdx`. -/
theorem tow_nrep (i j : towNorm.Rep) :
    towNorm.Nrep i j = inc plasticSubst (towIdx i) (towIdx j) := by
  rw [nrep_apply]
  rcases tow_rep i with hi | hi | hi <;> rcases tow_rep j with hj | hj | hj <;>
    simp only [towIdx, hi, hj] <;> decide

theorem tow_not_balanced : ¬ ∀ T ∈ towSys.C, Equiv1 T.1 T.2 := fun h =>
  absurd (h towA (by decide)) (by unfold Equiv1; decide)

theorem tow_top_ne_nil : ∀ T ∈ towSys.C, T.1 ≠ [] := by decide

/-- `N_C` is strongly connected: the cycle `towB → towA → towC → towB` of positive
entries. -/
theorem tow_sc : Psc.PerronCore.StronglyConnected (towNorm.Nrep.map (Nat.cast : ℕ → ℝ)) := by
  refine stronglyConnected_of_three (a := towRepB) (b := towRepA) (c := towRepC) (fun i => ?_)
    ?_ ?_ ?_
  · rcases tow_rep i with h | h | h
    · exact Or.inr (Or.inl (Subtype.ext h))
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Or.inr (Subtype.ext h))
  all_goals exact Nat.cast_pos.2 (by rw [nrep_apply]; decide)

theorem tow_kw : ∃ j : towNorm.Rep, Psc.Intertwiner2.kw j.1.1 j.1.2 ≠ 0 :=
  ⟨towRepA, fun h => by have := congrFun h 2; revert this; decide⟩

theorem tow_k3 : ∃ j : towNorm.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0 :=
  ⟨towRepB, fun h => by
    have := congrFun (congrFun (congrFun h 2) 0) 1
    have k : Psc.Intertwiner3.K3 towB.1 towB.2 2 0 1 = 1 := by decide
    simp [Lie3.k3Vec, towRepB, k] at this⟩

theorem tow_k4 : ∃ j : towNorm.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0 :=
  ⟨towRepC, fun h => by
    have := congrFun (congrFun (congrFun (congrFun h 0) 1) 1) 2
    have k : Psc.Defect4.K4 towC.1 towC.2 0 1 1 2 = 1 := by decide
    simp [Psc.Defect4Lie.k4Vec, towRepC, k] at this⟩

theorem tow_incQ : incQ towSys = Psc.Degree4Floor.plasticQ := rfl

/-! ### The coincident diagonal system: no normalisation -/

/-- The coincident letters `([a], [a])` over `plasticSubst`, with children the letters of
`σ(a)`. -/
def diagSys : ChildSystem (Fin 3) where
  s := plasticSubst
  C := {([0], [0]), ([1], [1]), ([2], [2])}
  children T := (subst plasticSubst T.1).map fun x => ([x], [x])
  top := by decide
  bot := by decide
  closed := by decide
  nonempty := by decide

theorem diag_no_norm : IsEmpty (Normalisation diagSys) :=
  ⟨fun P => P.noncoincident ([0], [0]) (by decide) rfl⟩

theorem diag_balanced : ∀ T ∈ diagSys.C, Equiv1 T.1 T.2 := by
  unfold Equiv1; decide

/-- The raw ordered state matrix of `diagSys` is strongly connected: three of its positive
entries (the pattern of the plastic matrix) form a Hamiltonian cycle. -/
theorem diag_sc : Psc.PerronCore.StronglyConnected
    ((Psc.ParikhIntertwiner.Nc diagSys).map (Nat.cast : ℕ → ℝ)) := by
  refine stronglyConnected_of_three (a := ⟨([1], [1]), by decide⟩)
    (b := ⟨([0], [0]), by decide⟩) (c := ⟨([2], [2]), by decide⟩) (fun i => ?_) ?_ ?_ ?_
  · rcases i with ⟨T, hT⟩
    have : T = ([0], [0]) ∨ T = ([1], [1]) ∨ T = ([2], [2]) := by simpa [diagSys] using hT
    rcases this with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
  all_goals exact Nat.cast_pos.2 (by rw [Psc.ParikhIntertwiner.Nc_apply]; decide)

/-! ### A finite zero-return closure with coincidences over a primitive Pisot substitution -/

/-- `0 ↦ 01`, `1 ↦ 201`, `2 ↦ 0`. -/
def bpaSubst : Fin 3 → List (Fin 3) := ![[0, 1], [2, 0, 1], [0]]

/-- Nine balanced pairs, closed under zero-return children (`bpaSys`), with three
coincidences. -/
def bpaStates : Finset (List (Fin 3) × List (Fin 3)) :=
  {([0], [0]), ([1], [1]), ([2], [2]), ([0, 1], [1, 0]), ([1, 0], [0, 1]),
    ([0, 1, 2], [1, 2, 0]), ([0, 1, 2], [2, 0, 1]), ([1, 2, 0], [0, 1, 2]),
    ([2, 0, 1], [0, 1, 2])}

def bpaSys : ChildSystem (Fin 3) :=
  Psc.Reduction.redSystem bpaSubst (by decide) bpaStates (by decide) (by decide)

theorem bpa_no_norm : IsEmpty (Normalisation bpaSys) :=
  ⟨fun P => P.noncoincident ([0], [0]) (by decide) rfl⟩

theorem bpa_balanced : ∀ T ∈ bpaSys.C, Equiv1 T.1 T.2 := by
  unfold Equiv1; decide

theorem bpa_kw : ∃ T ∈ bpaSys.C, Psc.Intertwiner2.kw T.1 T.2 ≠ 0 :=
  ⟨([0, 1], [1, 0]), by decide, fun h => by have := congrFun h 0; revert this; decide⟩

theorem bpa_inc : inc bpaSubst = Matrix.of ![![1, 1, 1], ![1, 1, 0], ![0, 1, 0]] := by
  decide

/-- `χ_M = X³ − 2X² − 1`, the cubic of `Psc.Degree3Sector.censusSubst`. -/
theorem bpa_charpoly : (incQ bpaSys).charpoly = X ^ 3 - C 2 * X ^ 2 - 1 := by
  have : incQ bpaSys = (inc bpaSubst).map (Nat.cast : ℕ → ℚ) := rfl
  rw [Psc.Cyclicity.charpoly_fin_three, this, bpa_inc]
  simp [Matrix.trace_fin_three, Matrix.det_fin_three, Psc.Cyclicity.wedge2,
    Psc.Cyclicity.pairFst, Psc.Cyclicity.pairSnd]
  rw [map_ofNat]; norm_num

theorem bpa_irreducible : Irreducible (incQ bpaSys).charpoly := by
  have h := Psc.Degree3Sector.census_irreducible
  rw [Psc.Degree3Sector.census_charpoly] at h
  rwa [bpa_charpoly]

theorem bpa_primitive : ∃ k ≥ 1, ∀ a c, 0 < (inc bpaSys.s ^ k) a c :=
  ⟨3, by norm_num, fun a c => by
    show 0 < (inc bpaSubst ^ 3) a c
    rw [bpa_inc]; fin_cases a <;> fin_cases c <;> decide +kernel⟩

/-- `χ_M` is Pisot (`Psc.Degree3Sector.census_other`). -/
theorem bpa_pisot : ∃ b : ℝ, 2 < b ∧ aeval (b : ℂ) (incQ bpaSys).charpoly = 0 ∧
    ∀ z : ℂ, aeval z (incQ bpaSys).charpoly = 0 → z ≠ b → ‖z‖ < 1 := by
  obtain ⟨b, hb2, hb3, hb⟩ := Psc.Degree3Sector.census_real_root
  have hev : ∀ z : ℂ, aeval z (incQ bpaSys).charpoly = z ^ 3 - 2 * z ^ 2 - 1 := by
    intro z; rw [bpa_charpoly]; simp [map_ofNat]
  refine ⟨b, hb2, by rw [hev]; exact_mod_cast hb, fun z hz hzb => ?_⟩
  exact (Psc.Degree3Sector.census_other hb2 hb3 hb (by rw [← hev]; exact hz) hzb).2.2

/-- **`bpaStates` is the zero-return closure of `(01, 10)`**: the set of states reachable from
`(01, 10)` in the full child graph `Psc.Descendants.Child` of `bpaSubst` (children of
coincidence blocks included, as in `Psc.Reduction.redSystem`), hence the least child-closed
set containing `(01, 10)` (`Psc.Descendants.reachable_subset`).  Every state is a block of
`red (σⁿ 01) (σⁿ 10)` for some `n ≤ 4` (`Psc.Descendants.reflTransGen_child_iff`). -/
theorem bpa_reachable :
    Psc.Descendants.Reachable bpaSubst {(([0, 1], [1, 0]) : List (Fin 3) × List (Fin 3))} =
      ↑bpaStates := by
  apply Set.Subset.antisymm
  · refine Psc.Descendants.reachable_subset (fun T hT => ?_) (fun T hT U hU => ?_)
    · rw [Set.mem_singleton_iff] at hT; subst hT; decide
    · exact Finset.mem_coe.2 ((by decide : ∀ T ∈ bpaStates,
        ∀ U ∈ Psc.Reduction.red (subst bpaSubst T.1) (subst bpaSubst T.2), U ∈ bpaStates)
          T (Finset.mem_coe.1 hT) U hU)
  · intro U hU
    refine ⟨([0, 1], [1, 0]), rfl, ?_⟩
    rw [Psc.Descendants.reflTransGen_child_iff bpaSubst
      (Psc.Descendants.seed_isBlock (by decide : (0 : Fin 3) ≠ 1))]
    obtain ⟨n, -, h⟩ := (by decide : ∀ U ∈ bpaStates, ∃ n ∈ Finset.range 5,
      U ∈ Psc.Reduction.red ((subst bpaSubst)^[n] [0, 1]) ((subst bpaSubst)^[n] [1, 0]))
        U (Finset.mem_coe.1 hU)
    exact ⟨n, h⟩

/-! ### The hypotheses, one predicate each -/

namespace Hyp

open Psc.PerronCore Psc.ParikhIntertwiner

/-- Every state is balanced (`∼₁`). -/
abbrev Bal (S : ChildSystem (Fin 3)) : Prop := ∀ T ∈ S.C, Equiv1 T.1 T.2
/-- Every state is `∼₂`. -/
abbrev Bal2 (S : ChildSystem (Fin 3)) : Prop := ∀ T ∈ S.C, Equiv2 T.1 T.2
/-- Every state is `∼₃`. -/
abbrev Bal3 (S : ChildSystem (Fin 3)) : Prop := ∀ T ∈ S.C, Psc.Defect4.Equiv3 T.1 T.2
/-- `χ_M` is irreducible over `ℚ`. -/
abbrev Irr (S : ChildSystem (Fin 3)) : Prop := Irreducible (incQ S).charpoly
/-- `N_C = A + B` on the representatives is strongly connected. -/
abbrev SC {S : ChildSystem (Fin 3)} (P : Normalisation S) : Prop :=
  StronglyConnected (P.Nrep.map (Nat.cast : ℕ → ℝ))
/-- The raw ordered state matrix is strongly connected (normalisation-free form of `SC`). -/
abbrev SCRaw (S : ChildSystem (Fin 3)) : Prop :=
  StronglyConnected ((Nc S).map (Nat.cast : ℕ → ℝ))
/-- A positive left eigenvector of `M`. -/
abbrev PerronVec (S : ChildSystem (Fin 3)) : Prop :=
  ∃ ℓ : Fin 3 → ℝ, (∀ a, 0 < ℓ a) ∧ ∃ β : ℝ, ℓ ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) = β • ℓ
/-- Some representative has `kw ≠ 0`. -/
abbrev KwCol {S : ChildSystem (Fin 3)} (P : Normalisation S) : Prop :=
  ∃ j : P.Rep, Psc.Intertwiner2.kw j.1.1 j.1.2 ≠ 0
/-- Some state has `kw ≠ 0` (normalisation-free form of `KwCol`). -/
abbrev KwState (S : ChildSystem (Fin 3)) : Prop := ∃ T ∈ S.C, Psc.Intertwiner2.kw T.1 T.2 ≠ 0
/-- Some representative has `K₃ ≠ 0`. -/
abbrev K3Col {S : ChildSystem (Fin 3)} (P : Normalisation S) : Prop :=
  ∃ j : P.Rep, Lie3.k3Vec j.1.1 j.1.2 ≠ 0
/-- Some representative has `K₄ ≠ 0`. -/
abbrev K4Col {S : ChildSystem (Fin 3)} (P : Normalisation S) : Prop :=
  ∃ j : P.Rep, Psc.Defect4Lie.k4Vec j.1.1 j.1.2 ≠ 0
/-- `β, α, γ` are complex roots of `χ_M`. -/
abbrev Roots (S : ChildSystem (Fin 3)) (β α γ : ℂ) : Prop :=
  aeval β (incQ S).charpoly = 0 ∧ aeval α (incQ S).charpoly = 0 ∧ aeval γ (incQ S).charpoly = 0
/-- `β, α, γ` are pairwise distinct. -/
abbrev Distinct (β α γ : ℂ) : Prop := β ≠ α ∧ β ≠ γ ∧ α ≠ γ
/-- `‖α‖, ‖γ‖ < 1`. -/
abbrev Moduli (α γ : ℂ) : Prop := ‖α‖ < 1 ∧ ‖γ‖ < 1
/-- Every complex root of `χ_S` has modulus at most `‖β‖`. -/
abbrev RootBound {S : ChildSystem (Fin 3)} (P : Normalisation S) (β : ℂ) : Prop :=
  ∀ μ : ℂ, aeval μ (SsignQ P).charpoly = 0 → ‖μ‖ ≤ ‖β‖
/-- `σ` is primitive. -/
abbrev Prim (S : ChildSystem (Fin 3)) : Prop := ∃ k ≥ 1, ∀ a c, 0 < (inc S.s ^ k) a c
/-- `β` is a root of `χ_M` with `1 < ‖β‖` and every other root of modulus `< 1`. -/
abbrev PisotRoot (S : ChildSystem (Fin 3)) (β : ℂ) : Prop :=
  aeval β (incQ S).charpoly = 0 ∧ 1 < ‖β‖ ∧
    ∀ z : ℂ, aeval z (incQ S).charpoly = 0 → z ≠ β → ‖z‖ < 1

end Hyp

/-! ### The predicates are the hypotheses of the reductio lemmas -/

/-- `Psc.KernelCofactor.simple_perron_root_rep` from the predicates. -/
theorem kernelCofactor_of_hyps {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : Hyp.Bal S) (hC : S.C.Nonempty) (hSC : Hyp.SC P) (hM : Hyp.Irr S)
    (hℓ : Hyp.PerronVec S) :
    ∃ β : ℝ, rootMultiplicity β ((NrepQ P).charpoly.map (algebraMap ℚ ℝ)) = 1 := by
  obtain ⟨ℓ, hℓ, β, hℓN⟩ := hℓ
  exact ⟨β, (Psc.KernelCofactor.simple_perron_root_rep P hM hbal hSC ℓ hℓ β hℓN hC).1⟩

/-- `Psc.Degree2Sector.rank_q2` from the predicates. -/
theorem degree2Sector_of_hyps {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : Hyp.Bal S) (hK : Hyp.KwCol P) (hM : Hyp.Irr S) : (Q2Q P).rank = 3 :=
  rank_q2 P hM hbal hK

/-- `Psc.Degree3Sector.deg23_iii_of_ne` from the predicates. -/
theorem degree3Sector_of_hyps {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : Hyp.Bal2 S) (hK : Hyp.K3Col P) (hM : Hyp.Irr S) {β α γ : ℂ}
    (hR : Hyp.Roots S β α γ) (hD : Hyp.Distinct β α γ) (hMod : Hyp.Moduli α γ)
    (hB : Hyp.RootBound P β) :
    1 ≤ Module.finrank ℚ (LinearMap.range (Psc.SectorBridge.Q3m P hbal)) ∧
      Module.finrank ℚ (LinearMap.range (Psc.SectorBridge.Q3m P hbal)) ≤ 2 ∧
      (SsignQ P).charpoly.IsRoot (incQ S).det :=
  Psc.Degree3Sector.deg23_iii_of_ne P hbal hM hR.1 hR.2.1 hR.2.2 hD.1 hD.2.1 hD.2.2 hMod.1
    hMod.2 hB hK

/-- The clause `|det M| = 1` of `Psc.Degree4Floor.theoremA_of_primitive` from the
predicates. -/
theorem degree4Floor_of_hyps {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hbal : Hyp.Bal3 S) (hK : Hyp.K4Col P) (hM : Hyp.Irr S) (hprim : Hyp.Prim S) {β : ℂ}
    (hβ : Hyp.PisotRoot S β) (hSC : Hyp.SC P) : |(incZ S).det| = 1 :=
  (Psc.Degree4Floor.theoremA_of_primitive P hbal hM hK hprim hβ.1 hβ.2.1 hβ.2.2
    hSC).choose_spec.2.2.2.1

/-! ### Shared facts of the controls -/

section Shared

open Psc.Degree4Floor Psc.Degree3Sector Psc.SignedIntertwiner

theorem plastic_prim : Hyp.Prim plasticEmpty := plastic_matrix_controls.2.1

/-- For primitive `σ`, `PerronVec` holds: `Psc.PerronExistence.exists_pos_left_eigen_inc`,
with the existentials reordered to the shape of `Hyp.PerronVec`. -/
theorem perronVec_of_prim {S : ChildSystem (Fin 3)} (h : Hyp.Prim S) : Hyp.PerronVec S :=
  let ⟨β, _, ℓ, hℓ, hℓN⟩ := Psc.PerronExistence.exists_pos_left_eigen_inc S.s h
  ⟨ℓ, hℓ, β, hℓN⟩

/-- **`Psc.Degree4Floor.ssign_root_bound_of_primitive` with balance weakened to nonempty top
tracks.**  The proof of `ssign_root_bound_of_primitive` goes through `thm:parikh`
(`Psc.SignedCocycle.Normalisation.rep_eigen`), which needs balance; the double-cover route
`Psc.SignedCocycle.Normalisation.cocycle_spectral_bound` needs only `ℓ > 0`, `ℓ M = r ℓ` and
nonempty top tracks (both routes are recorded in the docstring of
`Psc.SignedCocycle.Normalisation.cocycle_spectral_bound_rep`).  With `ℓ` the left Perron
vector of `Psc.PerronExistence.perron_inc` and `r = β` (`Psc.Degree4Floor.perron_eq_pisot`)
it gives the same bound.  The strengthening is this known route, not new mathematics. -/
theorem ssign_root_bound_of_top_ne_nil {S : ChildSystem (Fin 3)} (P : Normalisation S)
    (hprim : Hyp.Prim S) (htop : ∀ T ∈ S.C, T.1 ≠ []) {β : ℂ} (hβ : Hyp.PisotRoot S β) :
    Hyp.RootBound P β := by
  intro μ hμ
  obtain ⟨r, ℓ, u, h, -, -⟩ := Psc.PerronExistence.perron_inc S.s hprim
  have hr := perron_eq_pisot h hβ.1 hβ.2.1 hβ.2.2
  obtain ⟨x, hx0, hx⟩ := Psc.SectorBridge.exists_eigen_of_root_ssign P hμ
  rw [← hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h.pos]
  exact P.cocycle_spectral_bound ℓ h.left_pos htop r h.left x hx0 μ hx

theorem plasticEmpty_isEmpty : IsEmpty plasticEmptyNorm.Rep :=
  ⟨fun i => by simpa [plasticEmptyNorm] using i.2⟩

theorem censusEmpty_isEmpty : IsEmpty censusEmptyNorm.Rep :=
  ⟨fun i => by simpa [censusEmptyNorm] using i.2⟩

/-- Over `plasticSubst`: the plastic number `b > 1` is a Pisot root, and with the other two
roots `α, γ` the triple is pairwise distinct with `‖α‖, ‖γ‖ < 1`. -/
theorem plastic_roots_of (S : ChildSystem (Fin 3)) (hs : S.s = plasticSubst) :
    ∃ b : ℝ, 1 < b ∧ Hyp.PisotRoot S b ∧ ∃ α γ : ℂ, Hyp.Roots S b α γ ∧ Hyp.Distinct b α γ ∧
      Hyp.Moduli α γ := by
  have hq : incQ S = plasticQ := by show (inc S.s).map (Nat.cast : ℕ → ℚ) = _; rw [hs]
  obtain ⟨b, hb1, hb, hbp⟩ := plastic_pisot
  rw [← hq] at hb hbp
  have hM : Irreducible (incQ S).charpoly := hq ▸ plastic_irreducible
  obtain ⟨α, γ, hα, hγ, hβα, hβγ, hαγ, -⟩ := exists_other_roots _ hM hb
  have hb1' : 1 < ‖(b : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hb1
  exact ⟨b, hb1, ⟨hb, hb1', hbp⟩, α, γ, ⟨hb, hα, hγ⟩, ⟨hβα, hβγ, hαγ⟩,
    hbp α hα (Ne.symm hβα), hbp γ hγ (Ne.symm hβγ)⟩

/-- `χ_M = X²(X − 3)` has no three pairwise distinct roots. -/
theorem rot_no_three_roots (k : Fin 3) :
    ¬ ∃ β α γ : ℂ, Hyp.Roots (rotSys k) β α γ ∧ Hyp.Distinct β α γ := by
  rintro ⟨β, α, γ, ⟨hβ, hα, hγ⟩, hβα, hβγ, hαγ⟩
  rcases (rot_root_iff k β).1 hβ with rfl | rfl <;>
    rcases (rot_root_iff k α).1 hα with rfl | rfl <;>
    rcases (rot_root_iff k γ).1 hγ with rfl | rfl <;> simp_all

theorem rot_incZ_det (k : Fin 3) : (incZ (rotSys k)).det = 0 := by
  have : incZ (rotSys k) = Matrix.of fun _ _ => (1 : ℤ) := by
    ext a c; fin_cases a <;> fin_cases c <;> rfl
  rw [this, Matrix.det_fin_three]; simp

/-- On `rotSys k` no two distinct roots `α ≠ γ` of `χ_M = X²(X − 3)` lie in the open unit
disc (both would be `0`): the root hypotheses `hα, hγ, hαγ, hα1, hγ1` of
`Psc.Degree4Floor.sieve4` cannot all hold. -/
theorem rot_no_sieve4_roots (k : Fin 3) :
    ¬ ∃ α γ : ℂ, aeval α (incQ (rotSys k)).charpoly = 0 ∧ aeval γ (incQ (rotSys k)).charpoly = 0 ∧
      α ≠ γ ∧ Hyp.Moduli α γ := by
  rintro ⟨α, γ, hα, hγ, hαγ, hα1, hγ1⟩
  rcases (rot_root_iff k α).1 hα with rfl | rfl <;>
    rcases (rot_root_iff k γ).1 hγ with rfl | rfl
  · exact hαγ rfl
  · norm_num at hγ1
  · norm_num at hα1
  · exact hαγ rfl

/-! #### Child systems over the 3-cycle relabelling `Psc.SectorBridge.cycSubst` -/

section Cyc

open Psc.SectorBridge

theorem incQ_of_cyc {S : ChildSystem (Fin 3)} (hs : S.s = cycSubst) : incQ S = cycM := by
  show (inc S.s).map (Nat.cast : ℕ → ℚ) = _; rw [hs]

/-- Every complex root of `χ_M = X³ − 1` has modulus `1`. -/
theorem cyc_root_norm {S : ChildSystem (Fin 3)} (hs : S.s = cycSubst) {z : ℂ}
    (hz : aeval z (incQ S).charpoly = 0) : ‖z‖ = 1 := by
  rw [incQ_of_cyc hs, cycM_charpoly] at hz
  simp only [map_sub, map_pow, aeval_X, map_one] at hz
  exact Complex.norm_eq_one_of_pow_eq_one (sub_eq_zero.1 hz) (by norm_num)

/-- `χ_M = X³ − 1` has the rational root `1`. -/
theorem cyc_not_irr {S : ChildSystem (Fin 3)} (hs : S.s = cycSubst) : ¬ Hyp.Irr S := fun h =>
  Psc.Cyclicity.not_isRoot_of_irreducible _ h 1 (by rw [incQ_of_cyc hs, cycM_charpoly]; simp)

/-- No root of `χ_M = X³ − 1` lies off the unit circle: no Pisot root. -/
theorem cyc_no_pisot {S : ChildSystem (Fin 3)} (hs : S.s = cycSubst) :
    ¬ ∃ β : ℂ, Hyp.PisotRoot S β := fun ⟨_, hβ, hβ1, _⟩ =>
  lt_irrefl _ ((cyc_root_norm hs hβ) ▸ hβ1)

/-- No root of `χ_M = X³ − 1` lies in the open unit disc: `Moduli` fails for every choice of
roots. -/
theorem cyc_no_moduli {S : ChildSystem (Fin 3)} (hs : S.s = cycSubst) :
    ¬ ∃ β α γ : ℂ, Hyp.Roots S β α γ ∧ Hyp.Moduli α γ := fun ⟨_, _, _, ⟨_, hα, _⟩, hα1, _⟩ =>
  lt_irrefl _ ((cyc_root_norm hs hα) ▸ hα1)

/-- `M` is a permutation matrix with `M³ = 1`, so no power of it is positive. -/
theorem cyc_not_prim {S : ChildSystem (Fin 3)} (hs : S.s = cycSubst) : ¬ Hyp.Prim S := by
  rintro ⟨k, -, hk⟩
  rw [hs] at hk
  have h3 : inc cycSubst ^ 3 = 1 := by decide
  rw [pow_eq_pow_mod k h3] at hk
  obtain h | h | h : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  · rw [h] at hk; exact absurd (hk 0 1) (by decide)
  · rw [h] at hk; exact absurd (hk 0 0) (by decide)
  · rw [h] at hk; exact absurd (hk 0 0) (by decide)

/-- **`RootBound` at `β = 1`** for balanced states over `cycSubst`: `ℓ = (1, 1, 1)` is a
positive left eigenvector of the permutation matrix `M` for `1`, so
`Psc.SectorBridge.ssign_root_bound_of_perron` applies with `L = Lrep ℓ` (the argument of
`Psc.Degree4Floor.w4_controls`). -/
theorem cyc_rootBound {S : ChildSystem (Fin 3)} (hs : S.s = cycSubst) (P : Normalisation S)
    (hbal : Hyp.Bal S) : Hyp.RootBound P 1 := by
  have hℓ : (fun _ => (1 : ℝ)) ᵥ* (inc S.s).map (Nat.cast : ℕ → ℝ) =
      (1 : ℝ) • fun _ => (1 : ℝ) := by
    rw [hs]; funext j
    fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_three, cycSubst, inc]
  intro μ hμ
  have := ssign_root_bound_of_perron P _ (P.lrep_pos _ (fun _ => one_pos) (P.top_ne_nil hbal))
    (P.rep_eigen _ 1 hℓ hbal) μ hμ
  simpa using this

/-- The roots `1, ζ, ζ²` of `χ_M = X³ − 1`, pairwise distinct. -/
theorem cyc_roots {S : ChildSystem (Fin 3)} (hs : S.s = cycSubst) :
    Hyp.Roots S 1 (cycX 1) (cycX 2) ∧ Hyp.Distinct 1 (cycX 1) (cycX 2) := by
  have h0 : cycX 0 = 1 := by simp [cycX]
  have hq := incQ_of_cyc hs
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hq, ← h0]; exact cycX_root 0
  · rw [hq]; exact cycX_root 1
  · rw [hq]; exact cycX_root 2
  · rw [← h0]; exact cycX_injective.ne (by decide)
  · rw [← h0]; exact cycX_injective.ne (by decide)
  · exact cycX_injective.ne (by decide)

end Cyc

end Shared

/-! ### The leave-one-out tables -/

open Psc.Degree4Floor Psc.Degree3Sector Psc.SignedIntertwiner Psc.KernelCofactor in
/-- **The `Psc.KernelCofactor` table.**  Rows, in order: `N` dropped (`diagSys`, with `SC`
in raw form), `Bal` dropped (`towSys`), `C ≠ ∅` dropped (`plasticEmpty`), `Irr` dropped
(`rotSys 0`, primitive; and `wT`, the identity).  `SC` and `PerronVec` have no row (module
docstring). -/
theorem kernelCofactor_leave_one_out :
    (IsEmpty (Normalisation diagSys) ∧ Hyp.Bal diagSys ∧ diagSys.C.Nonempty ∧
        Hyp.SCRaw diagSys ∧ Hyp.Irr diagSys ∧ Hyp.PerronVec diagSys) ∧
      (¬ Hyp.Bal towSys ∧ towSys.C.Nonempty ∧ Hyp.SC towNorm ∧ Hyp.Irr towSys ∧
        Hyp.PerronVec towSys) ∧
      (Hyp.Bal plasticEmpty ∧ ¬ plasticEmpty.C.Nonempty ∧ Hyp.SC plasticEmptyNorm ∧
        Hyp.Irr plasticEmpty ∧ Hyp.PerronVec plasticEmpty) ∧
      (Hyp.Bal (rotSys 0) ∧ (rotSys 0).C.Nonempty ∧ Hyp.SC (rotNorm 0) ∧ ¬ Hyp.Irr (rotSys 0) ∧
        Hyp.PerronVec (rotSys 0) ∧ Hyp.Prim (rotSys 0)) ∧
      (Hyp.Bal wT ∧ wT.C.Nonempty ∧ Hyp.SC wTNorm ∧ ¬ Hyp.Irr wT ∧ Hyp.PerronVec wT) := by
  have : IsEmpty plasticEmptyNorm.Rep := plasticEmpty_isEmpty
  obtain ⟨wb, wC, wsc, ℓ, hℓ, hℓN⟩ := wT_rep_hyps
  refine ⟨⟨diag_no_norm, diag_balanced, ⟨([0], [0]), by decide⟩, diag_sc, plastic_irreducible,
      perronVec_of_prim plastic_prim⟩,
    ⟨tow_not_balanced, ⟨towA, by decide⟩, tow_sc, plastic_irreducible,
      perronVec_of_prim plastic_prim⟩,
    ⟨by simp [plasticEmpty], by simp [plasticEmpty], fun i => isEmptyElim i, plastic_irreducible,
      perronVec_of_prim plastic_prim⟩,
    ⟨rot_equiv1 0, ⟨(rotW 0 0, rotW 0 1), by decide⟩, rot_sc 0, rot_not_irreducible 0,
      ⟨fun _ => 1, fun _ => one_pos, 3, rot_left⟩, rot_primitive⟩,
    ⟨wb, wC, wsc, wT_not_irreducible, ℓ, hℓ, 1, hℓN⟩⟩

open Psc.Degree4Floor Psc.SignedIntertwiner in
/-- **The `Psc.Degree2Sector` table.**  Rows, in order: `N` dropped (`bpaSys`, with the
defect in raw form; `σ` primitive), `Bal` dropped (`towSys`), `KwCol` dropped
(`plasticEmpty`, degenerate), `Irr` dropped (`rotSys 0`, primitive; and `exA`). -/
theorem degree2Sector_leave_one_out :
    (IsEmpty (Normalisation bpaSys) ∧ Hyp.Bal bpaSys ∧ Hyp.KwState bpaSys ∧ Hyp.Irr bpaSys ∧
        Hyp.Prim bpaSys) ∧
      (¬ Hyp.Bal towSys ∧ Hyp.KwCol towNorm ∧ Hyp.Irr towSys) ∧
      (Hyp.Bal plasticEmpty ∧ ¬ Hyp.KwCol plasticEmptyNorm ∧ Hyp.Irr plasticEmpty) ∧
      (Hyp.Bal (rotSys 0) ∧ Hyp.KwCol (rotNorm 0) ∧ ¬ Hyp.Irr (rotSys 0) ∧
        Hyp.Prim (rotSys 0)) ∧
      (Hyp.Bal exA ∧ Hyp.KwCol exANorm ∧ ¬ Hyp.Irr exA) := by
  have : IsEmpty plasticEmptyNorm.Rep := plasticEmpty_isEmpty
  exact ⟨⟨bpa_no_norm, bpa_balanced, bpa_kw, bpa_irreducible, bpa_primitive⟩,
    ⟨tow_not_balanced, tow_kw, plastic_irreducible⟩,
    ⟨by simp [plasticEmpty], fun ⟨j, _⟩ => isEmptyElim j, plastic_irreducible⟩,
    ⟨rot_equiv1 0, rot0_kw, rot_not_irreducible 0, rot_primitive⟩,
    ⟨exA_balanced, exA_sector.2.1, exA_not_irreducible⟩⟩

open Psc.Degree4Floor Psc.Degree3Sector Psc.SectorBridge in
/-- **The `Psc.Degree3Sector.deg23_iii_of_ne` table.**  Rows, in order: `Bal2` dropped
(`towSys`, plastic roots), `K3Col` dropped (`censusEmpty`, degenerate), `Irr` dropped
jointly with `Distinct` (`rotSys 1`: roots `3, 0, 0`, no three distinct roots exist), and
`Irr` dropped jointly with `Moduli` (`cyc3Norm` over `cycSubst`: roots `1, ζ, ζ²`, all of
modulus `1`, with `RootBound` at `β = 1`).  `N`, `Irr` alone, `Roots`, `Distinct`, `Moduli`
alone and `RootBound` have no row (module docstring). -/
theorem degree3Sector_leave_one_out :
    (¬ Hyp.Bal2 towSys ∧ Hyp.K3Col towNorm ∧ Hyp.Irr towSys ∧ ∃ β α γ : ℂ,
        Hyp.Roots towSys β α γ ∧ Hyp.Distinct β α γ ∧ Hyp.Moduli α γ ∧
          Hyp.RootBound towNorm β) ∧
      (Hyp.Bal2 censusEmpty ∧ ¬ Hyp.K3Col censusEmptyNorm ∧ Hyp.Irr censusEmpty ∧
        Hyp.Prim censusEmpty ∧ ∃ β α γ : ℂ, Hyp.Roots censusEmpty β α γ ∧
          Hyp.Distinct β α γ ∧ Hyp.Moduli α γ ∧ Hyp.RootBound censusEmptyNorm β) ∧
      (Hyp.Bal2 (rotSys 1) ∧ Hyp.K3Col (rotNorm 1) ∧ ¬ Hyp.Irr (rotSys 1) ∧
        Hyp.Roots (rotSys 1) 3 0 0 ∧ Hyp.Moduli 0 0 ∧ Hyp.RootBound (rotNorm 1) 3 ∧
        Hyp.Prim (rotSys 1) ∧
        ¬ ∃ β α γ : ℂ, Hyp.Roots (rotSys 1) β α γ ∧ Hyp.Distinct β α γ) ∧
      (Hyp.Bal2 cyc3Sys ∧ Hyp.K3Col cyc3Norm ∧ ¬ Hyp.Irr cyc3Sys ∧
        Hyp.Roots cyc3Sys 1 (cycX 1) (cycX 2) ∧ Hyp.Distinct 1 (cycX 1) (cycX 2) ∧
        Hyp.RootBound cyc3Norm 1 ∧ ¬ Hyp.Prim cyc3Sys ∧
        ¬ ∃ β α γ : ℂ, Hyp.Roots cyc3Sys β α γ ∧ Hyp.Moduli α γ) := by
  have : IsEmpty censusEmptyNorm.Rep := censusEmpty_isEmpty
  refine ⟨⟨fun h => tow_not_balanced fun T hT => (h T hT).1, tow_k3, plastic_irreducible, ?_⟩,
    ⟨censusEmpty_equiv2, fun ⟨j, _⟩ => isEmptyElim j, census_irreducible, censusSubst_primitive,
      ?_⟩,
    ⟨rot1_equiv2, rot1_k3, rot_not_irreducible 1, ⟨(rot_root_iff 1 3).2 (Or.inr rfl),
      (rot_root_iff 1 0).2 (Or.inl rfl), (rot_root_iff 1 0).2 (Or.inl rfl)⟩,
      by norm_num, rot_bound 1, rot_primitive, rot_no_three_roots 1⟩,
    ⟨cyc3_equiv2, cyc3_k3_col_ne, cyc_not_irr rfl, (cyc_roots (S := cyc3Sys) rfl).1,
      (cyc_roots (S := cyc3Sys) rfl).2,
      cyc_rootBound rfl cyc3Norm (fun T hT => (cyc3_equiv2 T hT).1), cyc_not_prim rfl,
      cyc_no_moduli rfl⟩⟩
  · obtain ⟨b, -, hP, α, γ, hR, hD, hMod⟩ := plastic_roots_of towSys rfl
    exact ⟨b, α, γ, hR, hD, hMod, ssign_root_bound_of_top_ne_nil towNorm plastic_prim
      tow_top_ne_nil hP⟩
  · obtain ⟨-, -, ⟨b, -, α, γ, hb, hα, hγ, hbα, hbγ, hαγ, hα1, hγ1, hB⟩, -⟩ :=
      census_empty_control
    exact ⟨b, α, γ, ⟨hb, hα, hγ⟩, ⟨hbα, hbγ, hαγ⟩, ⟨hα1, hγ1⟩, hB⟩

open Psc.Degree4Floor Psc.SectorBridge in
/-- **The `Psc.Degree4Floor.theoremA_of_primitive` table**, which is also the table of
`sieve4_of_primitive` (the same hypotheses without `SC`).  `RootBound` (the hypothesis `hρ`
of `sieve4`) holds on every row.  Rows, in order: `Bal3` dropped (`towSys`), `K4Col`
dropped (`plasticEmpty`, degenerate), `Irr` dropped (`rotSys 2`, non-degenerate, with
`det M = 0`), and `Irr`, `Prim`, `PisotRoot` dropped jointly (`cyc4Norm` over `cycSubst`,
`RootBound` at `β = 1`; `SC` not checked).  **For `sieve4` in its literal three-root form**
the `rotSys 2` row drops `Irr` jointly with the root hypotheses: no two distinct roots
`α ≠ γ` of `χ_M = X²(X − 3)` lie in the unit disc (`rot_no_sieve4_roots`, the last conjunct
of that row).  `cyc4Norm` has three distinct roots `1, ζ, ζ²` and drops `Irr` jointly with
the moduli.  `N`, `Irr` alone for `sieve4`, `Prim`, `PisotRoot` and `SC` have no row (module
docstring). -/
theorem degree4Floor_leave_one_out :
    (¬ Hyp.Bal3 towSys ∧ Hyp.K4Col towNorm ∧ Hyp.Irr towSys ∧ Hyp.Prim towSys ∧
        (∃ β : ℂ, Hyp.PisotRoot towSys β ∧ Hyp.RootBound towNorm β) ∧ Hyp.SC towNorm) ∧
      (Hyp.Bal3 plasticEmpty ∧ ¬ Hyp.K4Col plasticEmptyNorm ∧ Hyp.Irr plasticEmpty ∧
        Hyp.Prim plasticEmpty ∧ (∃ β : ℂ, Hyp.PisotRoot plasticEmpty β ∧
          Hyp.RootBound plasticEmptyNorm β) ∧ Hyp.SC plasticEmptyNorm) ∧
      (Hyp.Bal3 (rotSys 2) ∧ Hyp.K4Col (rotNorm 2) ∧ ¬ Hyp.Irr (rotSys 2) ∧
        Hyp.Prim (rotSys 2) ∧ (Hyp.PisotRoot (rotSys 2) 3 ∧ Hyp.RootBound (rotNorm 2) 3) ∧
        Hyp.SC (rotNorm 2) ∧ (incZ (rotSys 2)).det = 0 ∧
        ¬ ∃ α γ : ℂ, aeval α (incQ (rotSys 2)).charpoly = 0 ∧
          aeval γ (incQ (rotSys 2)).charpoly = 0 ∧ α ≠ γ ∧ Hyp.Moduli α γ) ∧
      (Hyp.Bal3 cyc4Sys ∧ Hyp.K4Col cyc4Norm ∧ ¬ Hyp.Irr cyc4Sys ∧ ¬ Hyp.Prim cyc4Sys ∧
        (¬ ∃ β : ℂ, Hyp.PisotRoot cyc4Sys β) ∧ Hyp.RootBound cyc4Norm 1 ∧
        Hyp.Roots cyc4Sys 1 (cycX 1) (cycX 2) ∧ Hyp.Distinct 1 (cycX 1) (cycX 2) ∧
        ¬ ∃ β α γ : ℂ, Hyp.Roots cyc4Sys β α γ ∧ Hyp.Moduli α γ) := by
  have : IsEmpty plasticEmptyNorm.Rep := plasticEmpty_isEmpty
  obtain ⟨b, -, hP, -⟩ := plastic_roots_of towSys rfl
  obtain ⟨b', -, hP', -⟩ := plastic_roots_of plasticEmpty rfl
  refine ⟨⟨fun h => tow_not_balanced fun T hT => (h T hT).1.1, tow_k4, plastic_irreducible,
      plastic_prim, ⟨b, hP, ssign_root_bound_of_top_ne_nil towNorm plastic_prim tow_top_ne_nil hP⟩,
      tow_sc⟩,
    ⟨by simp [plasticEmpty], fun ⟨j, _⟩ => isEmptyElim j, plastic_irreducible, plastic_prim,
      ⟨b', hP', fun μ hμ => ?_⟩, fun i => isEmptyElim i⟩,
    ⟨rot2_equiv3, rot2_k4, rot_not_irreducible 2, rot_primitive, ⟨rot_pisot 2, rot_bound 2⟩,
      rot_sc 2, rot_incZ_det 2, rot_no_sieve4_roots 2⟩,
    ⟨cyc4_equiv3, cyc4_k4_col_ne, cyc_not_irr rfl, cyc_not_prim rfl, cyc_no_pisot rfl,
      cyc_rootBound rfl cyc4Norm (fun T hT => (cyc4_equiv3 T hT).1.1),
      (cyc_roots (S := cyc4Sys) rfl).1, (cyc_roots (S := cyc4Sys) rfl).2, cyc_no_moduli rfl⟩⟩
  rw [Matrix.charpoly_isEmpty, map_one] at hμ
  exact absurd hμ one_ne_zero

/-! ### Negative controls: irreducibility of `χ_M` is needed -/

/-- On `rotSys 0`, `χ_{Λ²M} = X³` (`Λ²J = 0`) does not divide `χ_S`, which has the root
`3` (`rot_ssign_root`). -/
theorem rot0_wedge2_not_dvd :
    ¬ (Psc.Cyclicity.wedge2 (incQ (rotSys 0))).charpoly ∣ (SsignQ (rotNorm 0)).charpoly := by
  intro h
  have hw : Psc.Cyclicity.wedge2 (incQ (rotSys 0)) = 0 := by
    rw [rot_incQ]; ext I J
    fin_cases I <;> fin_cases J <;> simp [Psc.Cyclicity.wedge2, Psc.Cyclicity.pairFst,
      Psc.Cyclicity.pairSnd]
  rw [hw, Matrix.charpoly_zero, Fintype.card_fin] at h
  have hdeg : (SsignQ (rotNorm 0)).charpoly.natDegree = 3 := by
    rw [Matrix.charpoly_natDegree_eq_dim, rot_card]
  have heq : (SsignQ (rotNorm 0)).charpoly = X ^ 3 :=
    eq_of_monic_of_dvd_of_natDegree_le (monic_X_pow 3) (Matrix.charpoly_monic _) h
      (by rw [hdeg, natDegree_X_pow])
  have h3 := rot_ssign_root 0
  rw [heq] at h3
  norm_num at h3

/-- **`hM` cannot be dropped from `Psc.Degree2Sector.charpoly_wedge2_dvd_ssign`**, even over a
primitive substitution (`rotSys 0`; `Psc.Degree2Sector.irreducible_needed` uses the
non-primitive `exA` for `card_rep_ge_three`). -/
theorem wedge2_dvd_needs_irreducible : ¬ ∀ (S : ChildSystem (Fin 3)) (P : Normalisation S),
    Hyp.Bal S → Hyp.KwCol P →
      (Psc.Cyclicity.wedge2 (incQ S)).charpoly ∣ (SsignQ P).charpoly := fun h =>
  rot0_wedge2_not_dvd (h (rotSys 0) (rotNorm 0) (rot_equiv1 0) rot0_kw)

/-- **`hM` cannot be dropped from `Psc.Degree4Floor.theoremA_of_primitive`** (whose
conclusion includes `|det M| = 1`, as does `sieve4_of_primitive`'s).  `rotSys 2` meets every
other hypothesis (`degree4Floor_leave_one_out`), and `det M = 0`. -/
theorem theoremA_needs_irreducible : ¬ ∀ (S : ChildSystem (Fin 3)) (P : Normalisation S),
    Hyp.Bal3 S → Hyp.K4Col P → Hyp.Prim S → (∃ β : ℂ, Hyp.PisotRoot S β) → Hyp.SC P →
      |(incZ S).det| = 1 := fun h => by
  have := h (rotSys 2) (rotNorm 2) rot2_equiv3 rot2_k4 rot_primitive ⟨3, rot_pisot 2⟩
    (rot_sc 2)
  rw [rot_incZ_det] at this
  norm_num at this

/-! ### A non-degenerate full control of `ssign_root_bound_of_primitive` -/

/-- **Full control of `Psc.Degree4Floor.ssign_root_bound_of_primitive`, non-degenerate**
(`docs/c4-solidify-stop-go-2026-11-07.md` §5, the candidate `012/120/201`).  `rotSys 0` is
primitive and balanced, with the Pisot root `3` of `χ_M = X²(X − 3)` and three
representatives.  The bound is the theorem's own conclusion, and it is attained:
`χ_S(3) = 0`. -/
theorem ssign_root_bound_full_control :
    Hyp.Prim (rotSys 0) ∧ Hyp.Bal (rotSys 0) ∧ Hyp.PisotRoot (rotSys 0) 3 ∧
      (rotSys 0).C.Nonempty ∧ Hyp.RootBound (rotNorm 0) 3 ∧
      aeval (3 : ℂ) (SsignQ (rotNorm 0)).charpoly = 0 :=
  ⟨rot_primitive, rot_equiv1 0, rot_pisot 0, ⟨(rotW 0 0, rotW 0 1), by decide⟩,
    Psc.Degree4Floor.ssign_root_bound_of_primitive (rotNorm 0) rot_primitive (rot_equiv1 0)
      (rot_pisot 0).1 (rot_pisot 0).2.1 (rot_pisot 0).2.2, rot_ssign_root 0⟩

/-- **On `towSys` the conclusion of `ssign_root_bound_of_primitive` holds without balance.**
`towSys` is primitive with a Pisot root `b` and nonempty top tracks, and it is unbalanced, so
`ssign_root_bound_of_top_ne_nil` applies where `ssign_root_bound_of_primitive` does not.
This instance shows that the balance hypothesis is stronger than the conclusion needs; the
general statement is `ssign_root_bound_of_top_ne_nil`, by the known route
`Psc.SignedCocycle.Normalisation.cocycle_spectral_bound`. -/
theorem ssign_root_bound_without_balance : ∃ b : ℝ, Hyp.Prim towSys ∧ ¬ Hyp.Bal towSys ∧
    (∀ T ∈ towSys.C, T.1 ≠ []) ∧ Hyp.PisotRoot towSys b ∧ Hyp.RootBound towNorm b := by
  obtain ⟨b, -, hP, -⟩ := plastic_roots_of towSys rfl
  exact ⟨b, plastic_prim, tow_not_balanced, tow_top_ne_nil, hP,
    ssign_root_bound_of_top_ne_nil towNorm plastic_prim tow_top_ne_nil hP⟩

end Psc.ReductioControls

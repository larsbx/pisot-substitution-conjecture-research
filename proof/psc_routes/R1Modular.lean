import Mathlib
import Lean.Util.CollectAxioms

/-!
R1F modular ancestry certificate. No real embeddings or floating-point
arithmetic. A finite-field left-null witness certifies *unsatisfiability*
of one reduced affine-cycle equation. Matrix reduction and the literal
correction-word/occurrence binding remain independent hypotheses.
-/

namespace PscRoutes.R1Modular

variable (p : ℕ) [Fact p.Prime]

/-- A nonzero finite-field pairing on the right-hand side contradicts
the existence of a solution when the functional annihilates the
matrix's image. Valid for arbitrary finite dimension. -/
theorem no_mod_solution_from_left_null
    {d : ℕ}
    (A : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))
    (left : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (b : Fin d → ZMod p)
    (hnull : left.comp A = 0)
    (hpair : left b ≠ 0) :
    ¬ ∃ x : Fin d → ZMod p, A x = b := by
  rintro ⟨x, hx⟩
  apply hpair
  calc
    left b = left (A x) := by rw [hx]
    _ = (left.comp A) x := rfl
    _ = 0 := by rw [hnull]; rfl

/-- Canonical integral address reduction, coordinatewise, to ZMod p.
This is a *definition* of the bridge, not a proof that an arbitrary
claimed mod-p matrix was reduced from its exact integer parent. -/
def modVec {d : ℕ} (v : Fin d → ℤ) : Fin d → ZMod p :=
  fun i => (v i : ZMod p)

/-- A typed refinement obligation: if an independently supplied
finite-field matrix A_p actually commutes with reduction of a
supplied integer affine-cycle operator, the left-null certificate
rejects every integral solution of that cycle equation. -/
theorem no_integral_solution_from_modular_witness
    {d : ℕ}
    (Aint : (Fin d → ℤ) → (Fin d → ℤ))
    (Amod : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))
    (b : Fin d → ℤ)
    (left : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (hreduction : ∀ x, Amod (modVec p x) = modVec p (Aint x))
    (hnull : left.comp Amod = 0)
    (hpair : left (modVec p b) ≠ 0) :
    ¬ ∃ x : Fin d → ℤ, Aint x = b := by
  rintro ⟨x, hx⟩
  have hmod : Amod (modVec p x) = modVec p b := by
    rw [hreduction x, hx]
  exact (no_mod_solution_from_left_null p Amod left
    (modVec p b) hnull hpair) ⟨modVec p x, hmod⟩

/-- Every *genuinely realized integral* cycle automatically survives all
correctly refined modular equations. Thus a left-null obstruction can
eliminate an abstract **candidate** cycle but can NEVER eliminate a
cycle whose integer state vector has already been witnessed exactly. -/
theorem realized_integer_cycle_cannot_be_modularly_obstructed
    {d : ℕ}
    (Aint : (Fin d → ℤ) → (Fin d → ℤ))
    (Amod : (Fin d → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p))
    (b : Fin d → ℤ)
    (left : (Fin d → ZMod p) →ₗ[ZMod p] ZMod p)
    (hreduction : ∀ x, Amod (modVec p x) = modVec p (Aint x))
    (hnull : left.comp Amod = 0)
    (x : Fin d → ℤ) (hactual : Aint x = b) :
    left (modVec p b) = 0 := by
  by_contra hpair
  exact (no_integral_solution_from_modular_witness p Aint Amod b left
    hreduction hnull hpair) ⟨x, hactual⟩

/-- A tiny deterministic finite-field negative control, not a
substitution-cycle instance. -/
theorem no_mod_two_solution_to_zero_times_x_eq_one :
    ¬ ∃ x : ZMod 2, (0 : ZMod 2) * x = 1 := by
  rintro ⟨x, hx⟩
  norm_num at hx


/-- Explicit integer incidence action for the Tribonacci substitution
0 ↦ 01, 1 ↦ 02, 2 ↦ 0. Its columns are the Parikh vectors
(1,1,0), (1,0,1), (1,0,0), respectively. -/
def tribonacciIncidence (x : Fin 3 → ℤ) : Fin 3 → ℤ :=
  fun i => if i = 0 then x 0 + x 1 + x 2
    else if i = 1 then x 0 else x 1

/-- An e₀ local correction is arithmetically admissible:
the proper one-letter prefix of 01 contributes a single 0.
But it cannot form a period-one *integral* ancestry cycle under
the true Tribonacci incidence. Exact parity provides the obstruction.
This is NOT a claim that a corresponding strict occurrence self-loop
exists or that all possible actual cycles are excluded. -/
theorem tribonacci_e0_forced_period_one_impossible :
    ¬ ∃ x : Fin 3 → ℤ,
        ∀ i : Fin 3,
          x i = tribonacciIncidence x i + (if i = 0 then 1 else 0) := by
  rintro ⟨x, hx⟩
  have h0 := hx 0
  have h2 := hx 2
  simp [tribonacciIncidence] at h0 h2
  omega

/-- The parity obstruction is a concrete ZMod 2 left-null test:
the first and third rows of I-M agree modulo 2, whereas the
e₀ correction pairs nontrivially with their sum. -/
theorem tribonacci_e0_mod_two_left_null
    (x0 x1 x2 : ZMod 2) :
    ¬ ((-x1 - x2 = (1 : ZMod 2)) ∧ (x2 - x1 = 0)) := by
  intro h
  rcases h with ⟨h0, h2⟩
  have hsum : (-x1 - x2) + (x2 - x1) = (0 : ZMod 2) := by
    calc
      (-x1 - x2) + (x2 - x1) = -(2 : ZMod 2) * x1 := by ring
      _ = 0 := by norm_num
  rw [h0, h2] at hsum
  norm_num at hsum


/-- The literal Tribonacci substitution on labels 0,1,2.
This source-word contract pins what the incidence columns mean. -/
def trImage (a : Fin 3) : List (Fin 3) :=
  if a = 0 then [0, 1]
  else if a = 1 then [0, 2]
  else [0]

/-- Exact integer Parikh vector of a finite word. -/
def trParikh (w : List (Fin 3)) : Fin 3 → ℤ :=
  fun i => (w.count i : ℤ)

/-- The incidence operator matches all three **literal** source words.
This is independent of arbitrary normalized pair/swap identification. -/
theorem tribonacci_incidence_matches_literal_images (a : Fin 3) :
    tribonacciIncidence (fun i => if i = a then 1 else 0) =
      trParikh (trImage a) := by
  fin_cases a <;> funext i <;> fin_cases i <;>
    norm_num [tribonacciIncidence, trParikh, trImage]

/-- The one-letter proper prefix of the image of 0 has Parikh
vector e₀, so the blocked period-one correction is **locally**
admissible, not an arbitrary invented forcing digit. An actual
closed ordered occurrence carrying that digit is still unproved. -/
theorem tribonacci_e0_is_actual_proper_prefix :
    trParikh ((trImage 0).take 1) =
      (fun i : Fin 3 => if i = 0 then 1 else 0) := by
  funext i
  fin_cases i <;> norm_num [trParikh, trImage]


/-- Every integral period-one cycle for the **actual** Tribonacci
incidence and a correction along e₀ requires an even first-coordinate
digit. This is the integer lift of the ZMod 2 left-null witness. -/
theorem tribonacci_period_one_e0_digit_even
    (x : Fin 3 → ℤ) (delta : ℤ)
    (hcycle : ∀ i : Fin 3,
      x i = tribonacciIncidence x i +
        (if i = 0 then delta else 0)) :
    ∃ k : ℤ, delta = 2 * k := by
  have h0 := hcycle 0
  have h1 := hcycle 1
  have h2 := hcycle 2
  simp [tribonacciIncidence] at h0 h1 h2
  refine ⟨-(x 0), ?_⟩
  omega

/-- Complete exclusion of nonzero period-one **integral** ancestry
cycles for the locally permitted digit alphabet {−e₀,0,+e₀}.
The digit-alphabet assumption is explicit; a word-level lemma
covering ALL proper local prefixes remains a separate refinement. -/
theorem tribonacci_period_one_small_digit_only_trivial
    (x : Fin 3 → ℤ) (delta : ℤ)
    (hsmall : -1 ≤ delta ∧ delta ≤ 1)
    (hcycle : ∀ i : Fin 3,
      x i = tribonacciIncidence x i +
        (if i = 0 then delta else 0)) :
    x 0 = 0 ∧ x 1 = 0 ∧ x 2 = 0 ∧ delta = 0 := by
  have h0 := hcycle 0
  have h1 := hcycle 1
  have h2 := hcycle 2
  simp [tribonacciIncidence] at h0 h1 h2
  rcases hsmall with ⟨hlo, hhi⟩
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega


/-- Basis defects of the canonical integral Parikh lattice. -/
def trBasis (j : Fin 3) : Fin 3 → ℤ :=
  fun i => if i = j then 1 else 0

/-- Crucial adversarial counter-calibration: the **actual**
Tribonacci incidence has a nonzero period-three integral affine
cycle with *locally admissible* corrections (−e₀,−e₀,0).
It defeats any proposal that bounded proper-prefix correction
alphabets alone exclude every nonzero periodic ancestry.
It does NOT prove the three digit occurrences can be chained as
a closed strict ordered word-level cycle. -/
theorem tribonacci_locally_admissible_nonzero_period_three :
    (fun i => tribonacciIncidence (trBasis 0) i - trBasis 0 i) = trBasis 1 ∧
    (fun i => tribonacciIncidence (trBasis 1) i - trBasis 0 i) = trBasis 2 ∧
    tribonacciIncidence (trBasis 2) = trBasis 0 := by
  refine ⟨?_, ?_, ?_⟩
  all_goals
    funext i
    fin_cases i <;> norm_num [tribonacciIncidence, trBasis]

/-- Both signs of the correction e₀ can arise from two proper
prefix fragments of actual substitution images. It remains an
OPEN word-level question whether these choices concatenate into
a single occurrence-compatible strict component. -/
theorem tribonacci_negative_e0_is_local_prefix_difference :
    (fun i : Fin 3 =>
      trParikh ([] : List (Fin 3)) i -
        trParikh ((trImage 0).take 1) i) =
      (fun i : Fin 3 => if i = 0 then -1 else 0) := by
  funext i
  fin_cases i <;> norm_num [trParikh, trImage]


/-- Every proper prefix of an image of the **literal**
Tribonacci substitution is either empty or the singleton [0]. -/
theorem tribonacci_proper_prefix_cases
    (a : Fin 3) (r : ℕ) (hr : r < (trImage a).length) :
    (trImage a).take r = [] ∨ (trImage a).take r = [0] := by
  fin_cases a
  · have hr' : r < 2 := by simpa [trImage] using hr
    have hcases : r = 0 ∨ r = 1 := by omega
    rcases hcases with h | h <;> subst r <;> simp [trImage]
  · have hr' : r < 2 := by simpa [trImage] using hr
    have hcases : r = 0 ∨ r = 1 := by omega
    rcases hcases with h | h <;> subst r <;> simp [trImage]
  · have hr' : r < 1 := by simpa [trImage] using hr
    have hzero : r = 0 := by omega
    subst r
    simp [trImage]

/-- Complete **local correction alphabet** for two independently
properly addressed images of Tribonacci. The Parikh correction
is (δ,0,0) with δ ∈ {−1,0,+1}. This does not assert
the two source addresses are compatible with any *global* strict
word-level ancestry, only that every proper local prefix produces
one of these three digits. -/
theorem tribonacci_all_proper_prefix_differences
    (a b : Fin 3) (r s : ℕ)
    (hr : r < (trImage a).length) (hs : s < (trImage b).length) :
    ∃ delta : ℤ, -1 ≤ delta ∧ delta ≤ 1 ∧
      (fun i : Fin 3 =>
        trParikh ((trImage a).take r) i -
          trParikh ((trImage b).take s) i) =
      (fun i : Fin 3 => if i = 0 then delta else 0) := by
  rcases tribonacci_proper_prefix_cases a r hr with ha | ha
  · rcases tribonacci_proper_prefix_cases b s hs with hb | hb
    · refine ⟨0, by omega, by omega, ?_⟩
      rw [ha, hb]
      funext i
      fin_cases i <;> norm_num [trParikh]
    · refine ⟨-1, by omega, by omega, ?_⟩
      rw [ha, hb]
      funext i
      fin_cases i <;> norm_num [trParikh]
  · rcases tribonacci_proper_prefix_cases b s hs with hb | hb
    · refine ⟨1, by omega, by omega, ?_⟩
      rw [ha, hb]
      funext i
      fin_cases i <;> norm_num [trParikh]
    · refine ⟨0, by omega, by omega, ?_⟩
      rw [ha, hb]
      funext i
      fin_cases i <;> norm_num [trParikh]


/-- A sharp limitation of prime-field obstruction: the integer
equation 4x=2 has NO solution. -/
theorem prime_field_certificates_are_not_integrally_complete :
    ¬ ∃ x : ℤ, 4 * x = 2 := by
  rintro ⟨x, hx⟩
  omega

/-- Yet the same equation DOES have a solution after reduction
modulo the only prime dividing 4, namely 2. Hence a left-null
F₂ witness cannot reject this nonintegral equation. -/
theorem four_x_eq_two_is_solvable_mod_two :
    ∃ x : ZMod 2, (4 : ZMod 2) * x = 2 := by
  refine ⟨0, ?_⟩
  norm_num

/-- Nor does a prime not dividing the coefficient detect the
integrality failure in this concrete check. -/
theorem four_x_eq_two_is_solvable_mod_three :
    ∃ x : ZMod 3, (4 : ZMod 3) * x = 2 := by
  refine ⟨2, ?_⟩
  norm_num

/-- The missing 2-adic precision *is* detected modulo 4.
Thus universal completeness of an integral cycle obstruction
requires a stronger arithmetic certificate, e.g. Smith
divisibility or prime-power congruences, not prime fields alone. -/
theorem four_x_eq_two_has_no_solution_mod_four :
    ¬ ∃ x : ZMod 4, (4 : ZMod 4) * x = 2 := by
  rintro ⟨x, hx⟩
  norm_num at hx

end PscRoutes.R1Modular

#print axioms PscRoutes.R1Modular.no_mod_solution_from_left_null
#print axioms PscRoutes.R1Modular.no_integral_solution_from_modular_witness
#print axioms PscRoutes.R1Modular.realized_integer_cycle_cannot_be_modularly_obstructed
#print axioms PscRoutes.R1Modular.no_mod_two_solution_to_zero_times_x_eq_one
#print axioms PscRoutes.R1Modular.tribonacci_e0_forced_period_one_impossible
#print axioms PscRoutes.R1Modular.tribonacci_e0_mod_two_left_null
#print axioms PscRoutes.R1Modular.tribonacci_incidence_matches_literal_images
#print axioms PscRoutes.R1Modular.tribonacci_e0_is_actual_proper_prefix
#print axioms PscRoutes.R1Modular.tribonacci_period_one_e0_digit_even
#print axioms PscRoutes.R1Modular.tribonacci_period_one_small_digit_only_trivial
#print axioms PscRoutes.R1Modular.tribonacci_locally_admissible_nonzero_period_three
#print axioms PscRoutes.R1Modular.tribonacci_negative_e0_is_local_prefix_difference
#print axioms PscRoutes.R1Modular.tribonacci_proper_prefix_cases
#print axioms PscRoutes.R1Modular.tribonacci_all_proper_prefix_differences
#print axioms PscRoutes.R1Modular.prime_field_certificates_are_not_integrally_complete
#print axioms PscRoutes.R1Modular.four_x_eq_two_is_solvable_mod_two
#print axioms PscRoutes.R1Modular.four_x_eq_two_is_solvable_mod_three
#print axioms PscRoutes.R1Modular.four_x_eq_two_has_no_solution_mod_four

/- An exact-declaration audit. Every theorem above is included by name;
   no source-level theorem can be accepted by a silent count reduction. -/
open Lean Elab Command in
run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[`PscRoutes.R1Modular.no_mod_solution_from_left_null,
    `PscRoutes.R1Modular.no_integral_solution_from_modular_witness,
    `PscRoutes.R1Modular.realized_integer_cycle_cannot_be_modularly_obstructed,
    `PscRoutes.R1Modular.no_mod_two_solution_to_zero_times_x_eq_one,
    `PscRoutes.R1Modular.tribonacci_e0_forced_period_one_impossible,
    `PscRoutes.R1Modular.tribonacci_e0_mod_two_left_null,
    `PscRoutes.R1Modular.tribonacci_incidence_matches_literal_images,
    `PscRoutes.R1Modular.tribonacci_e0_is_actual_proper_prefix,
    `PscRoutes.R1Modular.tribonacci_period_one_e0_digit_even,
    `PscRoutes.R1Modular.tribonacci_period_one_small_digit_only_trivial,
    `PscRoutes.R1Modular.tribonacci_locally_admissible_nonzero_period_three,
    `PscRoutes.R1Modular.tribonacci_negative_e0_is_local_prefix_difference,
    `PscRoutes.R1Modular.tribonacci_proper_prefix_cases,
    `PscRoutes.R1Modular.tribonacci_all_proper_prefix_differences,
    `PscRoutes.R1Modular.prime_field_certificates_are_not_integrally_complete,
    `PscRoutes.R1Modular.four_x_eq_two_is_solvable_mod_two,
    `PscRoutes.R1Modular.four_x_eq_two_is_solvable_mod_three,
    `PscRoutes.R1Modular.four_x_eq_two_has_no_solution_mod_four] do
    let axioms ← collectAxioms name
    for ax in axioms do
      if !allowed.contains ax then
        throwError "Nonstandard axiom in {name}: {ax}"
    liftIO <| IO.println s!"PSC_R1F_AXIOMS_OK\t{name}"

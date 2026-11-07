/-
# Ree's theorem at degree four; content components and weights of `Lie₃`, `Lie₄`

`docs/c4-concentration-attack-2026-11-06.md` §8;
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`: `thm:defect-intertwiner`
at `r = 3, 4` (the annihilator of the proper shuffles is `Lie_r`, and
`Φ_r = M^{⊗r}|_{Lie_r}`; Ree's theorem); `lem:conc-subst` (iii), which cites
Ree's theorem (as printed, (iii) is false on repeated letters; the erratum and
the corrected relations `R1`, `R2` for `K₄` are in `Psc.Defect4`); `thm:deg23`
(iii) (what its proof uses: the spectrum of `Φ₃`, and the dimension of
`ker (Φ₃ - det M)`); and the proof sketch of `thm:sieve` (the weights of `Φ_r`
are the monomials `β₁^a β₂^b β₃^c`, `a + b + c = r`, with the generalized Witt
multiplicities `m(a, b, c)`; the shapes at `r = 4`).  Part A is the
degree-four analogue of `PscVerif.Lie3`: `dim Lie₄(F³) = (3⁴ - 3²)/4 = 18`.
Part B splits `Lie₃`, `Lie₄` by content and computes the weights.

`Vec4 R = Fin 3 → Fin 3 → Fin 3 → Fin 3 → R` and `Vec3R R` (whose rational
instance is `Psc.Lie3.Vec3`) are the coordinates of `(R³)^{⊗4}` and
`(R³)^{⊗3}` in the word basis.  `ShuffleAnnih4 f` is the conjunction, at every
`a b c d`, of the two families

* `R1`: `f abcd + f bacd + f bcad + f bcda = 0` (`a ⧢ bcd`),
* `R2`: `f abcd + f acbd + f acdb + f cabd + f cadb + f cdab = 0` (`ab ⧢ cd`);

the third family `abc ⧢ d` is `R1` re-indexed (`ShuffleAnnih4.right`).  Unlike
degree three, `R2` is **not** redundant (`r1_not_shuffleAnnih4`).  The content
of a word is its exponent vector
`wordContent w = (|w|₀, |w|₁, |w|₂) : Fin 3 → ℕ`, and
`mono x κ = x₀^{κ₀} x₁^{κ₁} x₂^{κ₂}`.  `Lie_r` *means* the span of the explicit
Lyndon bracket vectors, which is the shuffle annihilator
(`shuffleAnnih4Space_eq_span`, `shuffleAnnih3Space_eq_span`).

## Proved here, in full

Part A, Ree at degree four:

* `shuffleAnnih4Space`: the solutions of `ShuffleAnnih4` as a submodule (any
  commutative ring); `ShuffleAnnih4.right`: the `abc ⧢ d` relations.
* **Every bracketing of every four letters is shuffle-annihilated.**  `word4`
  is the word basis, and `brR`, `brP`, `brXL`, `brRX`, `brL` are the
  word-basis expansions of the five bracketings `[x,[y,[z,w]]]`,
  `[[x,y],[z,w]]`, `[x,[[y,z],w]]`, `[[x,[y,z]],w]`, `[[[x,y],z],w]`.
  `shuffleAnnih4_br`: all five satisfy `ShuffleAnnih4` at all `x y z w`, over
  every commutative ring (a kernel `decide` over `ℤ`, `shuffleAnnih4_br_int`,
  transported along `Int.castRingHom` by `ShuffleAnnih4.map` and `map4_brR`
  etc.).
* `lyndon4 : Fin 18 → Vec4 R`, the standard bracketings of the 18 Lyndon words
  of length four on `0 < 1 < 2` (`0001`, `0002`, `0011`, `0012`, `0021`, `0022`,
  `0102`, `0111`, `0112`, `0121`, `0122`, `0211`, `0212`, `0221`, `0222`,
  `1112`, `1122`, `1222`), e.g. `0001 ↦ [0,[0,[0,1]]]`,
  `0102 ↦ [[0,1],[0,2]]`, `0121 ↦ [[0,[1,2]],1]`; `lyndon4_mem`.
* **Ree at degree four, spanning half** `eq_sum_lyndon4` (a field of
  characteristic zero): a shuffle-annihilated `f` equals
  `Σ_i lyndon4Coeff f i • lyndon4 i`, where `lyndon4Coeff` are explicit integer
  linear forms in the coordinates of `f` at the Lyndon words (the inverse of the
  unitriangular matrix of the brackets at the Lyndon words).  The proof is
  coordinatewise: the 18 Lyndon coordinates are ring identities, the other 63
  are explicit `linear_combination`s of `R1`, `R2` with coefficients in
  `{±1, ±2, ±1/2, 1/4}` (generated and checked in exact rational arithmetic).
* `lyndon4Coeff_sum` (any commutative ring): `lyndon4Coeff` recovers every
  combination of the brackets; hence `linearIndependent_lyndon4` and
  `lyndon4_ne_zero`.
* `shuffleAnnih4_iff_mem_span`, `shuffleAnnih4Space_eq_span`: the shuffle
  annihilator is exactly the span of the 18 brackets;
  `finrank_shuffleAnnih4Space`: its dimension is `18`, and
  `finrank_shuffleAnnih4Space_witt`: `= (3⁴ - 3²)/4`, the Witt dimension of
  `Lie₄(F³)`.
* **Naturality** `shuffleAnnih4_phi4` (any commutative ring, any `3 × 3`
  matrix `M`): `phi4 M = M^{⊗4}` maps the shuffle annihilator into itself
  (each relation at `(a, b, c, d)` is the sum of the relations at all
  `(x, y, z, w)` weighted by `M a x · M b y · M c z · M d w`), and
  `phi4_mem_span`: `Lie₄` is `M^{⊗4}`-invariant.
* Controls: `lyndon4_mem` and `lyndon4_ne_zero` (the hypotheses of
  `eq_sum_lyndon4` and `shuffleAnnih4_phi4` are met by nonzero vectors);
  `r1_not_shuffleAnnih4`: the concatenation square `[0,1]·[0,1] = 0101 - 0110
  - 1001 + 1010` (`sq01`) satisfies every `R1` but violates `R2` at `(0,1,0,1)`,
  so the `a ⧢ bcd` relations alone do not cut out `Lie₄` (their annihilator has
  dimension `81 - 57 = 24`; that number is a computation of the generator, not
  proved here).

Part B, contents and weights:

* **Contents.** `mono_wordContent`: the weight `x_{w₁} ⋯ x_{wₙ}` of a word is
  `mono x (wordContent w)`; `wordContent_mem`: the content of a word of length
  `r` lies in `Finset.Nat.antidiagonalTuple 3 r`.
* **The generalized Witt formula, exactly.**  `wittSum κ =
  Σ_{t ∣ gcd κ} μ(t) (|κ|/t)! / ((κ₀/t)! (κ₁/t)! (κ₂/t)!)` in `ℤ` (Mathlib's
  `μ`), and `wittMult κ = wittSum κ / |κ|` in `ℚ`, `|κ| = κ₀ + κ₁ + κ₂`.
  `mult4_witt`, `mult3_witt`: the exact integer identities
  `r · m(κ) = wittSum κ` at every content `κ` of degree `r = 4`, `3`, where
  `m(κ)` (`mult4`, `mult3`) is the number of Lyndon words of content `κ`;
  hence (`eq_wittMult`) `mult4_eq_wittMult`, `mult3_eq_wittMult`:
  `m(κ) = wittMult κ`.
* **Abstract layer**, proved once and instantiated at both degrees.
  Gradings by projections (`π κ` the identity on `p κ` and zero on every other
  `p κ'`): `iSupIndep_of_proj`, `iSup_inf_eq_of_proj`, `span_inf_eq_of_proj`
  (a component of a span of homogeneous vectors is spanned by those of its
  degree), `finrank_span_inf_eq`.  Eigenbases: `toMatrix_of_eigenbasis`,
  `charpoly_of_eigenbasis`, `finrank_ker_of_eigenbasis` (the `μ`-eigenspace has
  dimension `#{i | wᵢ = μ}`); `exists_eigenbasis_conj` (for a monoid
  homomorphism `ρ` of the `3 × 3` matrices preserving `W = span v`, with
  `ρ D vᵢ = wᵢ vᵢ` and `v` independent, `ρ (Q D Q⁻¹)|_W` has an eigenbasis with
  the same eigenvalues); `toMatrix_restrict_span` (the matrix of `T|_W` in the
  basis `v`, from an explicit coefficient map).
* **(a) The content decomposition** (any commutative ring).  `homog4 κ`
  (vectors supported on the words of content `κ`), `proj4 κ`, `sum_proj4`,
  `iSupIndep_homog4`.  `shuffleAnnih4_proj4`: the shuffle relations are
  content-homogeneous (`wordContent_shuffle4`), so the components
  `comp4 κ = shuffleAnnih4Space ⊓ homog4 κ` satisfy `iSupIndep_comp4` and
  `iSup_comp4`: the shuffle annihilator is the internal direct sum of its
  content components.  At degree three, likewise over any commutative ring:
  `homog3`, `proj3`, `shuffleAnnih3_proj3`, `comp3`, `iSupIndep_comp3`,
  `iSup_comp3`; over `ℚ` these are statements about `Psc.Lie3`
  (`shuffleAnnih3Space_rat`, `comp3_rat`, by `rfl`).
* **(b) Witt multiplicities as dimensions** (a field `F` of characteristic
  zero).  Every bracketing is content-homogeneous (`br_mem_homog4`,
  `br_mem_homog3`: its words are permutations of one word), hence
  `lyndon4_mem_homog4`, `lyndon_mem_homog3`, `lyndon3_mem_homog3`.
  `comp4_eq_span`, `comp3_eq_span` (`comp3_eq_span_rat` on `Psc.Lie3`): each
  component is the span of the Lyndon brackets of its content;
  `finrank_comp4`, `finrank_comp3`: `dim_F comp κ = m(κ)`.  By shape
  (`shapes4`, `shapes3`: every content of degree `r` is a permutation of one of
  them): `finrank_comp4_shapes` gives `(4,0,0) ↦ 0`, `(3,1,0) ↦ 1`,
  `(2,2,0) ↦ 1`, `(2,1,1) ↦ 3` (`comp4_eq_bot`), and `sum_finrank_comp4`:
  `6·1 + 3·1 + 3·3 = 18`; `finrank_comp3_shapes` gives `(3,0,0) ↦ 0`,
  `(2,1,0) ↦ 1`, `(1,1,1) ↦ 2` (`comp3_eq_bot`), and `sum_finrank_comp3`:
  `6·1 + 2 = 8`.
* **(c) Diagonal action** (any commutative ring): `phi4_diagonal_of_mem`,
  `phi3R_diagonal_of_mem` (`lie3_phi3_diagonal_of_mem` for `Psc.Lie3.phi3`):
  `(diag x)^{⊗r}` acts on the content-`κ` subspace as multiplication by `x^κ`;
  so the Lyndon brackets are eigenvectors (`lyndon4_eigen`, `lyndon3_eigen`).
  `flat4_phi4`, `flat3_phi3R`: `M^{⊗r}` is the Kronecker power on flattened
  coordinates, so `phi4_mul`, `phi3R_mul`, and `Phi4`, `Phi3` are monoid
  homomorphisms into the endomorphisms of `(R³)^{⊗r}`.
* **(d) Weights of `Φ_r`** (`F` as in (b); `M = Q (diag x) Q⁻¹` with `det Q` a
  unit).  `phi4Lie M`, `phi3Lie M`: `M^{⊗r}` restricted to `Lie_r` over `F`.
  `exists_eigenbasis_phi4Lie`, `exists_eigenbasis_phi3Lie`: `Φ_r` has an
  eigenbasis with the weights `x^{content(wᵢ)}` of the Lyndon words `wᵢ`;
  `charpoly_phi4Lie_prod`, `charpoly_phi3Lie_prod`; `charpoly_phi4Lie`,
  `charpoly_phi3Lie`: `χ(Φ_r) = ∏_{|κ| = r} (X - x^κ)^{dim_F comp κ}`;
  `charpoly_phi4Lie_witt`, `charpoly_phi3Lie_witt`: the same, with an exponent
  function equal at every `κ` to `wittMult κ` and to `dim_F comp κ`.
* **(e) The input of the proof of `thm:deg23` (iii).**
  `charpoly_phi3Lie_explicit`: `χ(Φ₃) = ∏_{i ≠ j} (X - xᵢ² xⱼ) · (X - det M)²`;
  `finrank_ker_phi3Lie`: `dim ker (Φ₃ - μ)` is the number of Lyndon words of
  weight `μ`; `finrank_ker_phi3Lie_sub_det`: if the `xᵢ` are pairwise distinct
  and nonzero, `dim ker (Φ₃ - det M) = 2`.
* **(f) Base change to the rational `Φ_r`.**  `charpoly_phi4Lie_eq`,
  `charpoly_phi3Lie_eq`: `χ(Φ_r)` is the characteristic polynomial of the
  explicit matrix of Ree coefficients of `M^{⊗r}` on the Lyndon brackets;
  `charpoly_phi4Lie_map`, `charpoly_phi3Lie_map`: it commutes with every field
  homomorphism; `charpoly_phi4Lie_rat`, `charpoly_phi3Lie_rat`: for a rational
  `M` with `M = Q (diag x) Q⁻¹` over `F`, the characteristic polynomial of the
  rational `Φ_r`, mapped to `F`, is `∏_{|κ| = r} (X - x^κ)^{dim_ℚ comp κ}`.
* **Degree three over `F`, reusing `Psc.Lie3`.**  `ShuffleAnnih3`,
  `shuffleAnnih3Space`, `phi3R`, `lyndon3Coeff` are the definitions of
  `Psc.Lie3` over any commutative ring (`shuffleAnnih3_rat`,
  `shuffleAnnih3Space_rat`, `phi3R_rat`, `lyndon3Coeff_rat`: `rfl`); `lyndon3`
  is the image of `Psc.Lie3.lyndon` (`lyndon3_rat`, `map3_lyndon3`).
  `eq_sum_lyndon3` (Ree's spanning half) and `linearIndependent_lyndon3` are
  transported from `Psc.Lie3.eq_sum_lyndon` and
  `Psc.Lie3.linearIndependent_lyndon`: a `ℚ`-linear functional `F → ℚ`,
  applied coordinatewise (`dual3`), maps the shuffle relations to the shuffle
  relations (`ShuffleAnnih3.dual3`) and the Ree coefficients to the Ree
  coefficients (`dual3_lyndon3Coeff`), and these functionals separate the
  points of `F`.  Then `shuffleAnnih3_iff_mem_span`,
  `shuffleAnnih3Space_eq_span`, `shuffleAnnih3_phi3R`, `phi3R_mem_span`.
* Controls: `phi4_diagonal_control` (the nonzero `lyndon4 0` has weight
  `x₀³ x₁`); `conj_control` (the non-diagonal `!![1,1,0; 0,2,0; 0,0,3]` is
  `Q₀ (diag (1,2,3)) Q₀⁻¹`, `det Q₀ = 1`); `charpoly_control`
  (`charpoly_phi3Lie` and `charpoly_phi4Lie` apply to it); `ker_control`
  (`finrank_ker_phi3Lie_sub_det` applies to it); `ker_needs_distinct`
  (negative: for `diag (1,1,2)`, `dim ker (Φ₃ - det M) = 4`, so distinctness
  cannot be dropped); the hypotheses of `wittSum_eq_small` and `eq_wittMult` are
  discharged in `mult4_witt`, `mult3_witt`, `mult4_eq_wittMult`,
  `mult3_eq_wittMult`.

## Not proved here

* `K₄ ∈ Lie₄`.  The relations `R1`, `R2` for `K₄` are
  `Psc.Defect4.k4_shuffle_left` and `Psc.Defect4.k4_shuffle_two` (on `Equiv3`
  pairs, over any alphabet), and `shuffleAnnih4_iff_mem_span` turns them into
  membership in `Lie₄`; the composition is `Psc.Defect4Lie`
  (`k4Vec_mem_span_lyndon4`, `phi4Lie_k4Lie`).
* Ree's theorem in other degrees or on other alphabets, and the identification
  of the span of the brackets with the free Lie algebra as an abstract object.
  Positive characteristic is not treated (the certificates divide by `2`, `3`,
  `4`).
* The generalized Witt formula as a theorem in general: `mult4_witt`,
  `mult3_witt` are finite computations at `r = 4, 3` (kernel `decide`, with `μ`
  on `1, …, 4` from `moebius_le_four`).
* Semisimplicity of `M`: the weights are proved under the hypothesis
  `M = Q (diag x) Q⁻¹` over a field `F` containing the eigenvalues (for a
  rational `M`, through `charpoly_phi4Lie_rat`, `charpoly_phi3Lie_rat`).  The
  passage from a rational `M` with irreducible `χ_M` to such a `Q` is not
  formalized.
* `thm:deg23` (iii) itself.  `im Q₃ ⊆ ker (Φ₃ - det M)` needs the Galois-stable
  rational constituents of the non-scalar part, `Lie₃ ≅ S_{(2,1)}`, the moduli
  of the weights and `thm:defect-intertwiner`; only the spectrum and
  `dim ker (Φ₃ - det M) = 2` (over `F`, for distinct nonzero eigenvalues) are
  proved here, and the kernel dimension is not transported to the rational
  `Φ₃`.
* The case analysis of `thm:sieve`.  The modulus eliminations and the
  Galois-orbit step are `Psc.WeightModulus` (`weight_310`, `weight_220`,
  `weight_211`, `weight_111`) and `Psc.GaloisOrbit` (`orbit_310_excluded`,
  `orbit_211_forces_unit`, `orbit_220_forces_complex_unit`), which take the
  weight list as a hypothesis on the roots of a rational polynomial `q`.  No
  theorem connects `charpoly_phi4Lie_rat` to those hypotheses (for instance,
  that every root of a rational factor of `χ(Φ₄)` is a weight of one of the
  listed shapes).
* `Psc.Lie3` is not generalized (it lies outside this module).  Its
  definitions `ShuffleAnnih`, `shuffleAnnihSpace`, `phi3`, `lyndonCoeff` are
  restated over a commutative ring with `rfl` bridges, and its naturality proof
  `Psc.Lie3.shuffleAnnih_phi3` is restated as `shuffleAnnih3_phi3R` (the
  entries of `M` lie in `F`, so it does not transport from `ℚ`).  Generalizing
  `Psc.Lie3` over a commutative ring would remove these restatements.
-/
import PscVerif.Lie3

namespace Psc.LieWeights

/-- Coordinates of a tensor in `(R³)^{⊗4}` in the word basis. -/
abbrev Vec4 (R : Type*) := Fin 3 → Fin 3 → Fin 3 → Fin 3 → R

section Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The shuffle relations `a ⧢ bcd` and `ab ⧢ cd` at every index. -/
def ShuffleAnnih4 (f : Vec4 R) : Prop :=
  ∀ a b c d, f a b c d + f b a c d + f b c a d + f b c d a = 0 ∧
    f a b c d + f a c b d + f a c d b + f c a b d + f c a d b + f c d a b = 0

/-- The relations `abc ⧢ d` are `a ⧢ bcd` re-indexed (`d ⧢ abc`). -/
theorem ShuffleAnnih4.right {f : Vec4 R} (h : ShuffleAnnih4 f) (a b c d : Fin 3) :
    f a b c d + f a b d c + f a d b c + f d a b c = 0 := by
  linear_combination (h d a b c).1

/-- The shuffle annihilator as a submodule. -/
def shuffleAnnih4Space : Submodule R (Vec4 R) where
  carrier := {f | ShuffleAnnih4 f}
  add_mem' {f g} hf hg a b c d := by
    obtain ⟨hf1, hf2⟩ := hf a b c d
    obtain ⟨hg1, hg2⟩ := hg a b c d
    simp only [Pi.add_apply]
    exact ⟨by linear_combination hf1 + hg1, by linear_combination hf2 + hg2⟩
  zero_mem' _ _ _ _ := by simp
  smul_mem' r f hf a b c d := by
    obtain ⟨h1, h2⟩ := hf a b c d
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨by linear_combination r * h1, by linear_combination r * h2⟩

theorem mem_shuffleAnnih4Space {f : Vec4 R} : f ∈ shuffleAnnih4Space ↔ ShuffleAnnih4 f :=
  Iff.rfl

/-! ### Brackets -/

/-- The word-basis vector of `xyzw` (nested, so that a coordinate is decided
letter by letter). -/
def word4 (x y z w : Fin 3) : Vec4 R := fun a b c d =>
  if a = x then if b = y then if c = z then if d = w then 1 else 0 else 0 else 0 else 0

/-- `[x,[y,[z,w]]]` in the word basis. -/
def brR (x y z w : Fin 3) : Vec4 R :=
  word4 x y z w - word4 x y w z - word4 x z w y + word4 x w z y
    - word4 y z w x + word4 y w z x + word4 z w y x - word4 w z y x

/-- `[[x,y],[z,w]]` in the word basis. -/
def brP (x y z w : Fin 3) : Vec4 R :=
  word4 x y z w - word4 x y w z - word4 y x z w + word4 y x w z
    - word4 z w x y + word4 z w y x + word4 w z x y - word4 w z y x

/-- `[x,[[y,z],w]]` in the word basis. -/
def brXL (x y z w : Fin 3) : Vec4 R :=
  word4 x y z w - word4 x z y w - word4 x w y z + word4 x w z y
    - word4 y z w x + word4 z y w x + word4 w y z x - word4 w z y x

/-- `[[x,[y,z]],w]` in the word basis. -/
def brRX (x y z w : Fin 3) : Vec4 R :=
  word4 x y z w - word4 x z y w - word4 y z x w + word4 z y x w
    - word4 w x y z + word4 w x z y + word4 w y z x - word4 w z y x

/-- `[[[x,y],z],w]` in the word basis. -/
def brL (x y z w : Fin 3) : Vec4 R :=
  word4 x y z w - word4 y x z w - word4 z x y w + word4 z y x w
    - word4 w x y z + word4 w y x z + word4 w z x y - word4 w z y x

/-- Coordinatewise image under a ring homomorphism. -/
def map4 (φ : R →+* S) (f : Vec4 R) : Vec4 S := fun a b c d => φ (f a b c d)

/-- The shuffle relations are preserved by every ring homomorphism. -/
theorem ShuffleAnnih4.map (φ : R →+* S) {f : Vec4 R} (h : ShuffleAnnih4 f) :
    ShuffleAnnih4 (map4 φ f) := fun a b c d => by
  obtain ⟨h1, h2⟩ := h a b c d
  exact ⟨by simpa [map4] using congrArg φ h1,
    by simpa [map4] using congrArg φ h2⟩

@[simp] theorem map4_add (φ : R →+* S) (f g : Vec4 R) :
    map4 φ (f + g) = map4 φ f + map4 φ g := by
  funext a b c d; simp [map4]

@[simp] theorem map4_sub (φ : R →+* S) (f g : Vec4 R) :
    map4 φ (f - g) = map4 φ f - map4 φ g := by
  funext a b c d; simp [map4]

@[simp] theorem map4_word4 (φ : R →+* S) (x y z w : Fin 3) :
    map4 φ (word4 x y z w) = word4 x y z w := by
  funext a b c d; simp only [map4, word4]; split_ifs <;> simp

theorem map4_brR (φ : R →+* S) (x y z w : Fin 3) : map4 φ (brR x y z w) = brR x y z w := by
  simp [brR]

theorem map4_brP (φ : R →+* S) (x y z w : Fin 3) : map4 φ (brP x y z w) = brP x y z w := by
  simp [brP]

theorem map4_brXL (φ : R →+* S) (x y z w : Fin 3) : map4 φ (brXL x y z w) = brXL x y z w := by
  simp [brXL]

theorem map4_brRX (φ : R →+* S) (x y z w : Fin 3) : map4 φ (brRX x y z w) = brRX x y z w := by
  simp [brRX]

theorem map4_brL (φ : R →+* S) (x y z w : Fin 3) : map4 φ (brL x y z w) = brL x y z w := by
  simp [brL]

/-- The five bracketings over `ℤ`: a kernel `decide` over all `3⁴ · 3⁴` index
choices. -/
theorem shuffleAnnih4_br_int (x y z w : Fin 3) :
    ShuffleAnnih4 (brR (R := ℤ) x y z w) ∧ ShuffleAnnih4 (brP (R := ℤ) x y z w) ∧
      ShuffleAnnih4 (brXL (R := ℤ) x y z w) ∧ ShuffleAnnih4 (brRX (R := ℤ) x y z w) ∧
      ShuffleAnnih4 (brL (R := ℤ) x y z w) := by
  revert x y z w
  unfold ShuffleAnnih4 brR brP brXL brRX brL word4
  decide +kernel

/-- **Every bracketing of four letters is shuffle-annihilated**, over every
commutative ring. -/
theorem shuffleAnnih4_br (x y z w : Fin 3) :
    ShuffleAnnih4 (brR (R := R) x y z w) ∧ ShuffleAnnih4 (brP (R := R) x y z w) ∧
      ShuffleAnnih4 (brXL (R := R) x y z w) ∧ ShuffleAnnih4 (brRX (R := R) x y z w) ∧
      ShuffleAnnih4 (brL (R := R) x y z w) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := shuffleAnnih4_br_int x y z w
  rw [← map4_brR (Int.castRingHom R), ← map4_brP (Int.castRingHom R),
    ← map4_brXL (Int.castRingHom R), ← map4_brRX (Int.castRingHom R),
    ← map4_brL (Int.castRingHom R)]
  exact ⟨h1.map _, h2.map _, h3.map _, h4.map _, h5.map _⟩

theorem shuffleAnnih4_brR (x y z w : Fin 3) : ShuffleAnnih4 (brR (R := R) x y z w) :=
  (shuffleAnnih4_br x y z w).1

theorem shuffleAnnih4_brP (x y z w : Fin 3) : ShuffleAnnih4 (brP (R := R) x y z w) :=
  (shuffleAnnih4_br x y z w).2.1

theorem shuffleAnnih4_brXL (x y z w : Fin 3) : ShuffleAnnih4 (brXL (R := R) x y z w) :=
  (shuffleAnnih4_br x y z w).2.2.1

theorem shuffleAnnih4_brRX (x y z w : Fin 3) : ShuffleAnnih4 (brRX (R := R) x y z w) :=
  (shuffleAnnih4_br x y z w).2.2.2.1

theorem shuffleAnnih4_brL (x y z w : Fin 3) : ShuffleAnnih4 (brL (R := R) x y z w) :=
  (shuffleAnnih4_br x y z w).2.2.2.2

/-- The standard bracketings of the 18 Lyndon words of length four on
`0 < 1 < 2`, in lexicographic order:
`0001 ↦ [0,[0,[0,1]]]`, `0002 ↦ [0,[0,[0,2]]]`, `0011 ↦ [0,[[0,1],1]]`,
`0012 ↦ [0,[0,[1,2]]]`, `0021 ↦ [0,[[0,2],1]]`, `0022 ↦ [0,[[0,2],2]]`,
`0102 ↦ [[0,1],[0,2]]`, `0111 ↦ [[[0,1],1],1]`, `0112 ↦ [0,[1,[1,2]]]`,
`0121 ↦ [[0,[1,2]],1]`, `0122 ↦ [0,[[1,2],2]]`, `0211 ↦ [[[0,2],1],1]`,
`0212 ↦ [[0,2],[1,2]]`, `0221 ↦ [[[0,2],2],1]`, `0222 ↦ [[[0,2],2],2]`,
`1112 ↦ [1,[1,[1,2]]]`, `1122 ↦ [1,[[1,2],2]]`, `1222 ↦ [[[1,2],2],2]`. -/
def lyndon4 : Fin 18 → Vec4 R :=
  ![brR 0 0 0 1, brR 0 0 0 2, brXL 0 0 1 1, brR 0 0 1 2, brXL 0 0 2 1, brXL 0 0 2 2, brP 0 1 0 2,
    brL 0 1 1 1, brR 0 1 1 2, brRX 0 1 2 1, brXL 0 1 2 2, brL 0 2 1 1, brP 0 2 1 2, brL 0 2 2 1,
    brL 0 2 2 2, brR 1 1 1 2, brXL 1 1 2 2, brL 1 2 2 2]

theorem lyndon4_mem (i : Fin 18) : lyndon4 (R := R) i ∈ shuffleAnnih4Space := by
  fin_cases i
  exacts [shuffleAnnih4_brR 0 0 0 1, shuffleAnnih4_brR 0 0 0 2, shuffleAnnih4_brXL 0 0 1 1,
    shuffleAnnih4_brR 0 0 1 2, shuffleAnnih4_brXL 0 0 2 1, shuffleAnnih4_brXL 0 0 2 2,
    shuffleAnnih4_brP 0 1 0 2, shuffleAnnih4_brL 0 1 1 1, shuffleAnnih4_brR 0 1 1 2,
    shuffleAnnih4_brRX 0 1 2 1, shuffleAnnih4_brXL 0 1 2 2, shuffleAnnih4_brL 0 2 1 1,
    shuffleAnnih4_brP 0 2 1 2, shuffleAnnih4_brL 0 2 2 1, shuffleAnnih4_brL 0 2 2 2,
    shuffleAnnih4_brR 1 1 1 2, shuffleAnnih4_brXL 1 1 2 2, shuffleAnnih4_brL 1 2 2 2]

/-- The coefficients of a shuffle-annihilated vector on the Lyndon brackets:
back-substitution in the unitriangular matrix of the brackets at the Lyndon
words (each bracket has coordinate `1` at its own word and `0` at the smaller
Lyndon words). -/
def lyndon4Coeff (f : Vec4 R) : Fin 18 → R :=
  ![f 0 0 0 1, f 0 0 0 2, f 0 0 1 1, f 0 0 1 2, f 0 0 1 2 + f 0 0 2 1, f 0 0 2 2,
    f 0 0 1 2 + f 0 0 2 1 + f 0 1 0 2, f 0 1 1 1, f 0 1 1 2, 2 * f 0 1 1 2 + f 0 1 2 1, f 0 1 2 2,
    f 0 1 1 2 + f 0 1 2 1 + f 0 2 1 1, 2 * f 0 1 2 2 + f 0 2 1 2,
    f 0 1 2 2 + f 0 2 1 2 + f 0 2 2 1, f 0 2 2 2, f 1 1 1 2, f 1 1 2 2, f 1 2 2 2]

theorem lyndon4Coeff_zero : lyndon4Coeff (0 : Vec4 R) = 0 := by
  funext i; fin_cases i <;> simp [lyndon4Coeff]

/-- The coefficients `lyndon4Coeff` recover every combination of the Lyndon
brackets exactly. -/
theorem lyndon4Coeff_sum (g : Fin 18 → R) : lyndon4Coeff (∑ i, g i • lyndon4 i) = g := by
  funext i
  simp only [lyndon4Coeff, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ,
    Fin.sum_univ_zero, lyndon4, Matrix.cons_val_zero, Matrix.cons_val_succ, brR, brP, brXL, brRX,
    brL, Pi.add_apply, Pi.sub_apply, word4, Fin.isValue, Fin.reduceEq, ↓reduceIte,
    Fin.succ_zero_eq_one, Fin.reduceSucc]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val] <;> ring1

/-- **The 18 Lyndon brackets are linearly independent** (over every commutative
ring). -/
theorem linearIndependent_lyndon4 : LinearIndependent R (lyndon4 (R := R)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [← congrFun (lyndon4Coeff_sum g) i, hg, lyndon4Coeff_zero, Pi.zero_apply]

theorem lyndon4_ne_zero [Nontrivial R] (i : Fin 18) : lyndon4 (R := R) i ≠ 0 :=
  linearIndependent_lyndon4.ne_zero i

/-! ### `M^{⊗4}` preserves the shuffle annihilator -/

/-- `M^{⊗4}` in word-basis coordinates. -/
def phi4 (M : Matrix (Fin 3) (Fin 3) R) (f : Vec4 R) : Vec4 R :=
  fun a b c d => ∑ x, ∑ y, ∑ z, ∑ w, M a x * M b y * M c z * M d w * f x y z w

/-- The shuffle relations are natural: `M^{⊗4}` maps the shuffle annihilator
into itself.  Each relation of `phi4 M f` at `(a, b, c, d)` is the sum of the
relations of `f` at all `(x, y, z, w)` weighted by `M a x · M b y · M c z · M d w`
(`k₁`, `k₂`, expanded over the 81 indices). -/
theorem shuffleAnnih4_phi4 (M : Matrix (Fin 3) (Fin 3) R) {f : Vec4 R} (hf : ShuffleAnnih4 f) :
    ShuffleAnnih4 (phi4 M f) := by
  intro a b c d
  have k₁ : ∑ x, ∑ y, ∑ z, ∑ w, M a x * M b y * M c z * M d w *
      (f x y z w + f y x z w + f y z x w + f y z w x) = 0 := by
    simp [(hf _ _ _ _).1]
  have k₂ : ∑ x, ∑ y, ∑ z, ∑ w, M a x * M b y * M c z * M d w *
      (f x y z w + f x z y w + f x z w y + f z x y w + f z x w y + f z w x y) = 0 := by
    simp [(hf _ _ _ _).2]
  simp only [phi4, Fin.sum_univ_three] at k₁ k₂ ⊢
  exact ⟨by linear_combination k₁, by linear_combination k₂⟩

end Ring

/-! ### Ree at degree four over a field of characteristic zero -/

section Field

variable {F : Type*} [Field F] [CharZero F]

/-- **Ree at degree four, spanning half**: a shuffle-annihilated vector is the
explicit combination of the 18 Lyndon brackets.  The 18 coordinates at Lyndon
words are ring identities; each of the other 63 is an explicit combination of
the relations `R1` (`h₁`) and `R2` (`h₂`), in lexicographic order of the
coordinate. -/
theorem eq_sum_lyndon4 {f : Vec4 F} (h : ShuffleAnnih4 f) :
    f = ∑ i, lyndon4Coeff f i • lyndon4 i := by
  have h₁ := fun a b c d => (h a b c d).1
  have h₂ := fun a b c d => (h a b c d).2
  funext a b c d
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero,
    lyndon4, lyndon4Coeff, Matrix.cons_val_zero, Matrix.cons_val_succ, brR, brP, brXL, brRX, brL,
    Pi.add_apply, Pi.sub_apply, word4]
  -- decide the letter conditions two letters at a time, pruning the term
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte] <;>
    fin_cases c <;> fin_cases d <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, ↓reduceIte, sub_zero,
      zero_sub, sub_self, add_zero, zero_add, mul_zero, mul_one, mul_neg] <;>
    try ring1
  · linear_combination (1/4 : F) * h₁ 0 0 0 0
  · linear_combination h₁ 0 0 0 1
  · linear_combination h₁ 0 0 0 2
  · linear_combination h₁ 0 0 1 0 - h₂ 0 0 0 1
  · linear_combination (1/2 : F) * h₂ 0 1 0 1
  · linear_combination h₁ 0 0 1 1 - (1/2 : F) * h₂ 0 1 0 1
  · linear_combination h₁ 0 0 1 2
  · linear_combination h₁ 0 0 2 0 - h₂ 0 0 0 2
  · linear_combination h₂ 0 1 0 2
  · linear_combination (1/2 : F) * h₂ 0 2 0 2
  · linear_combination h₁ 0 0 2 1 - h₂ 0 1 0 2
  · linear_combination h₁ 0 0 2 2 - (1/2 : F) * h₂ 0 2 0 2
  · linear_combination h₁ 1 0 0 0 - (1/2 : F) * h₁ 0 0 1 0
  · linear_combination h₁ 1 0 0 1 - (1/2 : F) * h₂ 0 1 0 1
  · linear_combination h₁ 1 0 0 2
  · linear_combination (1/2 : F) * h₂ 0 1 0 1 + h₁ 1 0 1 0 - 2 * h₁ 0 0 1 1
  · linear_combination h₁ 1 0 1 1
  · linear_combination h₁ 1 0 1 2
  · linear_combination h₁ 0 1 0 2 - 2 * h₁ 1 0 0 2
  · linear_combination h₁ 1 0 2 1
  · linear_combination h₁ 1 0 2 2
  · linear_combination h₁ 0 0 1 1 + h₁ 1 1 0 0 - h₂ 0 0 1 1
  · linear_combination h₁ 1 1 0 1 - h₂ 0 1 1 1
  · linear_combination h₁ 1 1 0 2 - h₂ 0 2 1 1
  · linear_combination h₁ 0 1 1 1 - (1/2 : F) * h₁ 1 1 0 1
  · linear_combination (1/4 : F) * h₁ 1 1 1 1
  · linear_combination h₁ 0 1 1 2 + h₁ 1 0 2 1 - h₂ 0 2 1 1
  · linear_combination h₁ 1 1 1 2
  · linear_combination h₁ 0 1 2 0 + h₁ 1 0 0 2 - h₂ 0 0 1 2
  · linear_combination h₁ 1 2 0 1 - h₂ 0 1 2 1
  · linear_combination h₁ 1 2 0 2 - h₂ 0 2 2 1
  · linear_combination h₁ 0 1 2 1 + h₁ 1 0 1 2 - h₂ 0 1 1 2
  · linear_combination h₁ 1 1 2 1 - h₂ 1 1 1 2
  · linear_combination (1/2 : F) * h₂ 1 2 1 2
  · linear_combination h₁ 0 1 2 2 + h₁ 1 0 2 2 - h₂ 0 2 1 2
  · linear_combination h₁ 1 1 2 2 - (1/2 : F) * h₂ 1 2 1 2
  · linear_combination h₁ 2 0 0 0 - (1/2 : F) * h₁ 0 0 2 0
  · linear_combination h₁ 2 0 0 1 - h₂ 0 1 0 2
  · linear_combination h₁ 2 0 0 2 - (1/2 : F) * h₂ 0 2 0 2
  · linear_combination h₁ 0 1 0 2 + h₁ 2 0 1 0 - h₂ 0 2 1 0
  · linear_combination h₁ 2 0 1 1
  · linear_combination h₁ 2 0 1 2
  · linear_combination (1/2 : F) * h₂ 0 2 0 2 + h₁ 2 0 2 0 - 2 * h₁ 0 0 2 2
  · linear_combination h₁ 2 0 2 1
  · linear_combination h₁ 2 0 2 2
  · linear_combination h₁ 0 0 1 2 + h₁ 2 1 0 0 - h₂ 0 0 1 2
  · linear_combination h₁ 2 1 0 1 - h₂ 0 1 1 2
  · linear_combination h₁ 2 1 0 2 - h₂ 0 2 1 2
  · linear_combination h₁ 0 1 1 2 + h₁ 2 1 1 0 - h₂ 1 0 1 2
  · linear_combination h₁ 2 1 1 1 - (1/2 : F) * h₁ 1 1 2 1
  · linear_combination h₁ 2 1 1 2 - (1/2 : F) * h₂ 1 2 1 2
  · linear_combination h₁ 0 2 1 2 + h₁ 2 0 2 1 - h₂ 0 2 2 1
  · linear_combination (1/2 : F) * h₂ 1 2 1 2 + h₁ 2 1 2 1 - 2 * h₁ 1 1 2 2
  · linear_combination h₁ 2 1 2 2
  · linear_combination h₁ 0 0 2 2 + h₁ 2 2 0 0 - h₂ 0 0 2 2
  · linear_combination h₁ 2 2 0 1 - h₂ 0 1 2 2
  · linear_combination h₁ 2 2 0 2 - h₂ 0 2 2 2
  · linear_combination h₁ 0 1 2 2 + h₁ 2 2 1 0 - h₂ 1 0 2 2
  · linear_combination h₁ 1 1 2 2 + h₁ 2 2 1 1 - h₂ 1 1 2 2
  · linear_combination h₁ 2 2 1 2 - h₂ 1 2 2 2
  · linear_combination h₁ 0 2 2 2 - (1/2 : F) * h₁ 2 2 0 2
  · linear_combination h₁ 1 2 2 2 - (1/2 : F) * h₁ 2 2 1 2
  · linear_combination (1/4 : F) * h₁ 2 2 2 2

/-- **Ree at degree four on three letters**: a vector satisfies both shuffle
relations iff it lies in the span of the 18 Lyndon brackets. -/
theorem shuffleAnnih4_iff_mem_span (f : Vec4 F) :
    ShuffleAnnih4 f ↔ f ∈ Submodule.span F (Set.range lyndon4) := by
  constructor
  · intro h
    rw [eq_sum_lyndon4 h]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    have hle : Submodule.span F (Set.range lyndon4) ≤ shuffleAnnih4Space :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr lyndon4_mem)
    exact hle h

theorem shuffleAnnih4Space_eq_span :
    shuffleAnnih4Space = Submodule.span F (Set.range (lyndon4 (R := F))) :=
  Submodule.ext shuffleAnnih4_iff_mem_span

/-- The shuffle annihilator in `(F³)^{⊗4}` has dimension `18`. -/
theorem finrank_shuffleAnnih4Space : Module.finrank F (shuffleAnnih4Space (R := F)) = 18 := by
  rw [shuffleAnnih4Space_eq_span, finrank_span_eq_card linearIndependent_lyndon4]
  simp

/-- The dimension is the Witt dimension `(3⁴ - 3²)/4` of `Lie₄(F³)`. -/
theorem finrank_shuffleAnnih4Space_witt :
    Module.finrank F (shuffleAnnih4Space (R := F)) = (3 ^ 4 - 3 ^ 2) / 4 := by
  rw [finrank_shuffleAnnih4Space]; norm_num

/-- **`Lie₄` is `M^{⊗4}`-invariant**, so `Φ₄ = M^{⊗4}` restricts to it. -/
theorem phi4_mem_span (M : Matrix (Fin 3) (Fin 3) F) {f : Vec4 F}
    (hf : f ∈ Submodule.span F (Set.range lyndon4)) :
    phi4 M f ∈ Submodule.span F (Set.range lyndon4) :=
  (shuffleAnnih4_iff_mem_span _).mp (shuffleAnnih4_phi4 M ((shuffleAnnih4_iff_mem_span f).mpr hf))

end Field

/-! ### Control: `ab ⧢ cd` is not redundant -/

/-- The concatenation square `[0,1]·[0,1] = 0101 - 0110 - 1001 + 1010`. -/
def sq01 : Vec4 ℚ := word4 0 1 0 1 - word4 0 1 1 0 - word4 1 0 0 1 + word4 1 0 1 0

/-- **The relations `a ⧢ bcd` alone do not cut out `Lie₄`**: `sq01` satisfies
every `R1` but violates `R2` at `(0, 1, 0, 1)` (value `2`). -/
theorem r1_not_shuffleAnnih4 :
    (∀ a b c d, sq01 a b c d + sq01 b a c d + sq01 b c a d + sq01 b c d a = 0) ∧
      sq01 0 1 0 1 + sq01 0 0 1 1 + sq01 0 0 1 1 + sq01 0 0 1 1 + sq01 0 0 1 1
        + sq01 0 1 0 1 = 2 ∧
      ¬ ShuffleAnnih4 sq01 := by
  unfold ShuffleAnnih4 sq01 word4
  decide +kernel

/-! ## Part B: contents, components and weights -/

open Polynomial

/-! ### Contents and monomials -/

/-- The content of a word: its letter counts `(|w|₀, |w|₁, |w|₂)`, the exponent
vector of its weight. -/
def wordContent (w : List (Fin 3)) : Fin 3 → ℕ := fun i => w.count i

@[simp] theorem wordContent_nil (i : Fin 3) : wordContent [] i = 0 := rfl

theorem wordContent_cons (a : Fin 3) (w : List (Fin 3)) (i : Fin 3) :
    wordContent (a :: w) i = wordContent w i + if a = i then 1 else 0 := by
  simp [wordContent, List.count_cons]

/-- The content of a word lies in the antidiagonal of its length. -/
theorem wordContent_mem (w : List (Fin 3)) :
    wordContent w ∈ Finset.Nat.antidiagonalTuple 3 w.length := by
  rw [Finset.Nat.mem_antidiagonalTuple]
  induction w with
  | nil => simp [wordContent]
  | cons a w ih => simp [wordContent_cons, Finset.sum_add_distrib, ih]

/-- The monomial `x^κ = x₀^{κ₀} x₁^{κ₁} x₂^{κ₂}`. -/
def mono {M : Type*} [CommMonoid M] (x : Fin 3 → M) (κ : Fin 3 → ℕ) : M := ∏ i, x i ^ κ i

/-- The weight `x_{w₁} ⋯ x_{wₙ}` of a word is the monomial of its content. -/
theorem mono_wordContent {M : Type*} [CommMonoid M] (x : Fin 3 → M) (w : List (Fin 3)) :
    mono x (wordContent w) = (w.map x).prod := by
  induction w with
  | nil => simp [mono, wordContent]
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, ← ih]
    simp only [mono, wordContent_cons, pow_add, Finset.prod_mul_distrib, pow_ite, pow_one,
      pow_zero, Finset.prod_ite_eq, Finset.mem_univ, ite_true]
    exact mul_comm _ _

/-! ### The generalized Witt formula -/

open ArithmeticFunction in
/-- The Möbius sum of the generalized Witt formula,
`Σ_{t ∣ gcd κ} μ(t) (|κ|/t)! / ((κ₀/t)! (κ₁/t)! (κ₂/t)!)` (Mathlib's `μ`). -/
def wittSum (κ : Fin 3 → ℕ) : ℤ :=
  ∑ t ∈ (Nat.gcd (κ 0) (Nat.gcd (κ 1) (κ 2))).divisors,
    moebius t * Nat.multinomial Finset.univ (fun i => κ i / t)

/-- The generalized Witt formula of the proof sketch of `thm:sieve`, exactly:
`m(κ) = wittSum κ / |κ|` in `ℚ`, with `|κ| = κ₀ + κ₁ + κ₂`. -/
def wittMult (κ : Fin 3 → ℕ) : ℚ := wittSum κ / ∑ i, κ i

/-- `wittSum` with `μ` replaced by its values `1, -1, -1, 0` on `1, 2, 3, 4`. -/
def wittSumSmall (κ : Fin 3 → ℕ) : ℤ :=
  ∑ t ∈ (Nat.gcd (κ 0) (Nat.gcd (κ 1) (κ 2))).divisors,
    (if t = 1 then 1 else if t = 4 then 0 else -1 : ℤ) *
      Nat.multinomial Finset.univ (fun i => κ i / t)

open ArithmeticFunction in
/-- `μ` on `1, 2, 3, 4` is `1, -1, -1, 0`. -/
theorem moebius_le_four {t : ℕ} (ht : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) :
    moebius t = if t = 1 then 1 else if t = 4 then 0 else -1 := by
  rcases ht with rfl | rfl | rfl | rfl
  · simp
  · simp [moebius_apply_prime Nat.prime_two]
  · simp [moebius_apply_prime Nat.prime_three]
  · have h : moebius (2 ^ 2) = 0 := by rw [moebius_apply_prime_pow Nat.prime_two two_ne_zero]; simp
    simpa using h

/-- When every divisor of `gcd κ` is at most `4`, `wittSum` is `wittSumSmall`
(which the kernel evaluates quickly; Mathlib's `μ` goes through well-founded
recursion). -/
theorem wittSum_eq_small {κ : Fin 3 → ℕ}
    (h : ∀ t ∈ (Nat.gcd (κ 0) (Nat.gcd (κ 1) (κ 2))).divisors, t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) :
    wittSum κ = wittSumSmall κ := by
  unfold wittSum wittSumSmall
  rw [Finset.sum_congr rfl fun t ht => by rw [moebius_le_four (h t ht)]]

/-- The exact integer identity `r · m = wittSum κ` at a content `κ` of degree
`r ≠ 0` is `m = wittMult κ`. -/
theorem eq_wittMult {r : ℕ} (hr : r ≠ 0) {κ : Fin 3 → ℕ}
    (hκ : κ ∈ Finset.Nat.antidiagonalTuple 3 r) {m : ℕ} (h : (r : ℤ) * m = wittSum κ) :
    (m : ℚ) = wittMult κ := by
  rw [wittMult, Finset.Nat.mem_antidiagonalTuple.mp hκ, ← h]
  push_cast
  field_simp

/-- Regrouping a product along a map into a finite set: each value occurs to
the power of the size of its fibre. -/
theorem prod_regroup {ι κ M : Type*} [Fintype ι] [DecidableEq κ] [CommMonoid M] (c : ι → κ)
    (t : Finset κ) (hc : ∀ i, c i ∈ t) (g : κ → M) :
    ∏ i, g (c i) = ∏ k ∈ t, g k ^ (Finset.univ.filter fun i => c i = k).card := by
  rw [← Finset.prod_fiberwise_of_maps_to' (fun i _ => hc i)]
  simp only [Finset.prod_const]

/-! ### Gradings by projections -/

section Grading

variable {K R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {p : K → Submodule R V}
  {π : K → V →ₗ[R] V}

/-- Subspaces `p κ` with linear maps `π κ`, the identity on `p κ` and zero on
every other `p κ'`, are independent. -/
theorem iSupIndep_of_proj (hself : ∀ κ, ∀ f ∈ p κ, π κ f = f)
    (hother : ∀ κ κ', κ' ≠ κ → ∀ f ∈ p κ', π κ f = 0) : iSupIndep p := by
  refine iSupIndep_def.mpr fun κ => Submodule.disjoint_def.mpr fun f hf hf' => ?_
  have hle : ⨆ (j) (_ : j ≠ κ), p j ≤ LinearMap.ker (π κ) :=
    iSup₂_le fun j hj g hg => LinearMap.mem_ker.mpr (hother κ j hj g hg)
  rw [← hself κ f hf]
  exact LinearMap.mem_ker.mp (hle hf')

/-- If the `π κ`, `κ ∈ s`, sum to the identity and map `W` into `W` and into
`p κ`, then `W` is the supremum of its components `W ⊓ p κ`. -/
theorem iSup_inf_eq_of_proj (W : Submodule R V) (s : Finset K) (hsum : ∀ f, ∑ κ ∈ s, π κ f = f)
    (hW : ∀ κ, ∀ f ∈ W, π κ f ∈ W) (hmem : ∀ κ f, π κ f ∈ p κ) : ⨆ κ, W ⊓ p κ = W := by
  refine le_antisymm (iSup_le fun _ => inf_le_left) fun f hf => ?_
  rw [← hsum f]
  exact Submodule.sum_mem _ fun κ _ =>
    Submodule.mem_iSup_of_mem κ (Submodule.mem_inf.mpr ⟨hW κ f hf, hmem κ f⟩)

/-- If each `v i` lies in `p (c i)`, the component `span (range v) ⊓ p κ` is
spanned by the `v i` with `c i = κ`. -/
theorem span_inf_eq_of_proj {ι : Type*} {v : ι → V} {c : ι → K} (hv : ∀ i, v i ∈ p (c i))
    (hself : ∀ κ, ∀ f ∈ p κ, π κ f = f) (hother : ∀ κ κ', κ' ≠ κ → ∀ f ∈ p κ', π κ f = 0)
    (κ : K) :
    Submodule.span R (Set.range v) ⊓ p κ =
      Submodule.span R (Set.range fun i : {i // c i = κ} => v i.1) := by
  refine le_antisymm (fun f hf => ?_) ?_
  · obtain ⟨hf₁, hf₂⟩ := Submodule.mem_inf.mp hf
    have h := Submodule.mem_map_of_mem (f := π κ) hf₁
    rw [Submodule.map_span, hself κ f hf₂] at h
    refine Submodule.span_le.mpr ?_ h
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    by_cases hi : c i = κ
    · rw [hself κ _ (hi ▸ hv i)]
      exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · rw [hother κ (c i) hi _ (hv i)]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le, Set.range_subset_iff]
    rintro ⟨i, rfl⟩
    exact Submodule.mem_inf.mpr ⟨Submodule.subset_span ⟨i, rfl⟩, hv i⟩

end Grading

/-- With independent `v`, the component has dimension the number of `i` with
`c i = κ`. -/
theorem finrank_span_inf_eq {K F V ι : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Fintype ι] [DecidableEq K] {p : K → Submodule F V} {π : K → V →ₗ[F] V} {v : ι → V}
    {c : ι → K} (hli : LinearIndependent F v) (hv : ∀ i, v i ∈ p (c i))
    (hself : ∀ κ, ∀ f ∈ p κ, π κ f = f) (hother : ∀ κ κ', κ' ≠ κ → ∀ f ∈ p κ', π κ f = 0)
    (κ : K) :
    Module.finrank F ↥(Submodule.span F (Set.range v) ⊓ p κ) =
      (Finset.univ.filter fun i => c i = κ).card := by
  rw [span_inf_eq_of_proj hv hself hother κ]
  exact (finrank_span_eq_card (b := fun i : {i // c i = κ} => v i.1)
    (hli.comp _ Subtype.val_injective)).trans (Fintype.card_subtype _)

/-! ### Eigenbases and restrictions -/

section Eigen

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

/-- In an eigenbasis `T (bᵢ) = wᵢ bᵢ`, `T` has the matrix `diag w`. -/
theorem toMatrix_of_eigenbasis (b : Module.Basis ι F V) {T : Module.End F V} {w : ι → F}
    (hT : ∀ i, T (b i) = w i • b i) : LinearMap.toMatrix b b T = Matrix.diagonal w := by
  ext i j
  rw [LinearMap.toMatrix_apply, hT, map_smul, Module.Basis.repr_self, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

/-- An endomorphism with an eigenbasis has characteristic polynomial `∏ᵢ (X - wᵢ)`. -/
theorem charpoly_of_eigenbasis [FiniteDimensional F V] (b : Module.Basis ι F V)
    {T : Module.End F V} {w : ι → F} (hT : ∀ i, T (b i) = w i • b i) :
    T.charpoly = ∏ i, (X - C (w i)) := by
  rw [← LinearMap.charpoly_toMatrix T b, toMatrix_of_eigenbasis b hT, Matrix.charpoly_diagonal]

/-- In an eigenbasis, the `μ`-eigenspace has dimension the number of `i` with
`wᵢ = μ`. -/
theorem finrank_ker_of_eigenbasis [FiniteDimensional F V] [DecidableEq F]
    (b : Module.Basis ι F V) {T : Module.End F V} {w : ι → F} (hT : ∀ i, T (b i) = w i • b i)
    (μ : F) :
    Module.finrank F (LinearMap.ker (T - μ • 1)) = (Finset.univ.filter fun i => w i = μ).card := by
  have hT' : ∀ i, (T - μ • 1) (b i) = (w i - μ) • b i := fun i => by
    rw [LinearMap.sub_apply, hT, LinearMap.smul_apply, Module.End.one_apply, sub_smul]
  have hrank := Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix b b (T - μ • 1)) b b
  rw [Matrix.toLin_toMatrix, toMatrix_of_eigenbasis b hT', Matrix.rank_diagonal] at hrank
  have hsum := LinearMap.finrank_range_add_finrank_ker (T - μ • 1)
  rw [← hrank, Module.finrank_eq_card_basis b] at hsum
  have hc := Fintype.card_subtype_compl (fun i => w i = μ)
  have hle := Fintype.card_subtype_le (fun i => w i = μ)
  simp only [ne_eq, sub_eq_zero] at hsum
  rw [← Fintype.card_subtype]
  omega

omit [Fintype ι] [DecidableEq ι] in
/-- **Conjugation.**  Let `ρ` be a representation of the `3 × 3` matrices
preserving `W = span (range v)`, with independent eigenvectors
`ρ D (vᵢ) = wᵢ vᵢ`.  Then `ρ (Q D Q⁻¹)|_W` has an eigenbasis (the `ρ Q (vᵢ)`)
with the same eigenvalues. -/
theorem exists_eigenbasis_conj (ρ : Matrix (Fin 3) (Fin 3) F →* Module.End F V) {v : ι → V}
    (hv : LinearIndependent F v)
    (hW : ∀ A, ∀ f ∈ Submodule.span F (Set.range v), ρ A f ∈ Submodule.span F (Set.range v))
    {Q D : Matrix (Fin 3) (Fin 3) F} (hQ : IsUnit Q.det) {w : ι → F}
    (hD : ∀ i, ρ D (v i) = w i • v i) :
    ∃ b : Module.Basis ι F (Submodule.span F (Set.range v)),
      ∀ i, (ρ (Q * D * Q⁻¹)).restrict (hW _) (b i) = w i • b i := by
  have hρ : ∀ A B f, ρ A (ρ B f) = ρ (A * B) f := fun A B f => by
    rw [map_mul, Module.End.mul_apply]
  let e : Submodule.span F (Set.range v) ≃ₗ[F] Submodule.span F (Set.range v) :=
    LinearEquiv.ofLinearMap ((ρ Q).restrict (hW Q)) ((ρ Q⁻¹).restrict (hW Q⁻¹))
      (by ext f; show ρ Q (ρ Q⁻¹ f) = f; rw [hρ, Matrix.mul_nonsing_inv _ hQ, map_one]; rfl)
      (by ext f; show ρ Q⁻¹ (ρ Q f) = f; rw [hρ, Matrix.nonsing_inv_mul _ hQ, map_one]; rfl)
  refine ⟨(Module.Basis.span hv).map e, fun i => Subtype.ext ?_⟩
  have hb : (((Module.Basis.span hv).map e i : Submodule.span F (Set.range v)) : V) =
      ρ Q (v i) := by
    rw [Module.Basis.map_apply]
    show ρ Q _ = _
    rw [Module.Basis.span_apply]
    rfl
  rw [Submodule.coe_smul, LinearMap.coe_restrict_apply, hb, hρ, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hQ, Matrix.mul_one, ← hρ, hD, map_smul]

/-- If every vector of `W = span (range v)` is `Σᵢ coeff f i • vᵢ`, the matrix of
`T|_W` in the basis `v` has the entries `coeff (T vⱼ) i`. -/
theorem toMatrix_restrict_span {v : ι → V} (hv : LinearIndependent F v) (coeff : V → ι → F)
    (hcoeff : ∀ f ∈ Submodule.span F (Set.range v), f = ∑ i, coeff f i • v i)
    (T : Module.End F V)
    (hW : ∀ f ∈ Submodule.span F (Set.range v), T f ∈ Submodule.span F (Set.range v)) :
    LinearMap.toMatrix (Module.Basis.span hv) (Module.Basis.span hv) (T.restrict hW) =
      Matrix.of fun i j => coeff (T (v j)) i := by
  ext i j
  have hj : T.restrict hW (Module.Basis.span hv j) =
      ∑ k, coeff (T (v j)) k • Module.Basis.span hv k := by
    apply Subtype.ext
    simp only [LinearMap.coe_restrict_apply, Module.Basis.span_apply, Submodule.coe_sum,
      Submodule.coe_smul]
    exact hcoeff _ (hW _ (Submodule.subset_span ⟨j, rfl⟩))
  rw [LinearMap.toMatrix_apply, hj, Module.Basis.repr_sum_self, Matrix.of_apply]

end Eigen

/-! ### Degree four: the content components -/

section Content4

variable {R S : Type*} [CommRing R] [CommRing S]

theorem wordContent_mem4 (a b c d : Fin 3) :
    wordContent [a, b, c, d] ∈ Finset.Nat.antidiagonalTuple 3 4 :=
  wordContent_mem _

/-- Vectors of `(R³)^{⊗4}` supported on the words of content `κ`. -/
def homog4 (κ : Fin 3 → ℕ) : Submodule R (Vec4 R) where
  carrier := {f | ∀ a b c d, wordContent [a, b, c, d] ≠ κ → f a b c d = 0}
  add_mem' hf hg a b c d h := by simp [hf a b c d h, hg a b c d h]
  zero_mem' _ _ _ _ _ := rfl
  smul_mem' r f hf a b c d h := by simp [hf a b c d h]

/-- The projection of `(R³)^{⊗4}` onto the words of content `κ`. -/
def proj4 (κ : Fin 3 → ℕ) : Vec4 R →ₗ[R] Vec4 R where
  toFun f a b c d := if wordContent [a, b, c, d] = κ then f a b c d else 0
  map_add' f g := by funext a b c d; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r f := by
    funext a b c d; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem proj4_apply (κ : Fin 3 → ℕ) (f : Vec4 R) (a b c d : Fin 3) :
    proj4 κ f a b c d = if wordContent [a, b, c, d] = κ then f a b c d else 0 := rfl

theorem proj4_mem_homog4 (κ : Fin 3 → ℕ) (f : Vec4 R) : proj4 κ f ∈ homog4 κ :=
  fun _ _ _ _ h => ite_eq_right h

theorem proj4_of_mem (κ : Fin 3 → ℕ) (f : Vec4 R) (hf : f ∈ homog4 κ) : proj4 κ f = f := by
  funext a b c d
  rw [proj4_apply]
  split_ifs with h
  · rfl
  · exact (hf a b c d h).symm

theorem proj4_of_mem_ne (κ κ' : Fin 3 → ℕ) (h : κ' ≠ κ) (f : Vec4 R) (hf : f ∈ homog4 κ') :
    proj4 κ f = 0 := by
  funext a b c d
  rw [proj4_apply]
  split_ifs with hc
  · exact hf a b c d fun e => h (e.symm.trans hc)
  · rfl

/-- The content projections sum to the identity. -/
theorem sum_proj4 (f : Vec4 R) : ∑ κ ∈ Finset.Nat.antidiagonalTuple 3 4, proj4 κ f = f := by
  funext a b c d
  simp only [Finset.sum_apply, proj4_apply, Finset.sum_ite_eq, wordContent_mem4, ite_true]

/-- The words of each shuffle relation at `(a, b, c, d)` have the content of
`abcd`. -/
theorem wordContent_shuffle4 : ∀ a b c d : Fin 3,
    wordContent [b, a, c, d] = wordContent [a, b, c, d] ∧
      wordContent [b, c, a, d] = wordContent [a, b, c, d] ∧
      wordContent [b, c, d, a] = wordContent [a, b, c, d] ∧
      wordContent [a, c, b, d] = wordContent [a, b, c, d] ∧
      wordContent [a, c, d, b] = wordContent [a, b, c, d] ∧
      wordContent [c, a, b, d] = wordContent [a, b, c, d] ∧
      wordContent [c, a, d, b] = wordContent [a, b, c, d] ∧
      wordContent [c, d, a, b] = wordContent [a, b, c, d] := by
  decide

/-- **The shuffle relations are content-homogeneous**: every content projection
maps the shuffle annihilator into itself. -/
theorem shuffleAnnih4_proj4 (κ : Fin 3 → ℕ) {f : Vec4 R} (hf : ShuffleAnnih4 f) :
    ShuffleAnnih4 (proj4 κ f) := by
  intro a b c d
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈⟩ := wordContent_shuffle4 a b c d
  simp only [proj4_apply, e₁, e₂, e₃, e₄, e₅, e₆, e₇, e₈]
  split_ifs
  · exact hf a b c d
  · simp

/-- The content-`κ` component of the shuffle annihilator. -/
def comp4 (κ : Fin 3 → ℕ) : Submodule R (Vec4 R) := shuffleAnnih4Space ⊓ homog4 κ

/-- The content subspaces of `(R³)^{⊗4}` are independent. -/
theorem iSupIndep_homog4 : iSupIndep (homog4 (R := R)) :=
  iSupIndep_of_proj (π := proj4) proj4_of_mem proj4_of_mem_ne

/-- **The shuffle annihilator is the internal direct sum of its content
components**, first half: the components are independent. -/
theorem iSupIndep_comp4 : iSupIndep (comp4 (R := R)) :=
  iSupIndep_homog4.mono fun _ => inf_le_right

/-- Second half: the components span the shuffle annihilator. -/
theorem iSup_comp4 : ⨆ κ, comp4 (R := R) κ = shuffleAnnih4Space :=
  iSup_inf_eq_of_proj _ _ sum_proj4 (fun κ _ hf => shuffleAnnih4_proj4 κ hf) proj4_mem_homog4

theorem word4_mem_homog4 (x y z w : Fin 3) :
    word4 (R := R) x y z w ∈ homog4 (wordContent [x, y, z, w]) := fun a b c d h => by
  unfold word4
  split_ifs <;> first | rfl | (subst_vars; exact (h rfl).elim)

/-- **Every bracketing of `x y z w` lies in the content-`[x, y, z, w]`
subspace**: its eight words are permutations of `xyzw`. -/
theorem br_mem_homog4 (x y z w : Fin 3) :
    brR (R := R) x y z w ∈ homog4 (wordContent [x, y, z, w]) ∧
      brP (R := R) x y z w ∈ homog4 (wordContent [x, y, z, w]) ∧
      brXL (R := R) x y z w ∈ homog4 (wordContent [x, y, z, w]) ∧
      brRX (R := R) x y z w ∈ homog4 (wordContent [x, y, z, w]) ∧
      brL (R := R) x y z w ∈ homog4 (wordContent [x, y, z, w]) := by
  have W (p q r s : Fin 3) (h : wordContent [p, q, r, s] = wordContent [x, y, z, w]) :
      word4 (R := R) p q r s ∈ homog4 (wordContent [x, y, z, w]) := h ▸ word4_mem_homog4 p q r s
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [brR, brP, brXL, brRX, brL] <;>
    repeat' first
      | apply add_mem | apply sub_mem | exact word4_mem_homog4 _ _ _ _
      | (apply W; funext i; simp only [wordContent_cons, wordContent_nil]; ring1)

/-- The 18 Lyndon words of length four, in the order of `lyndon4`. -/
def lyndon4Word : Fin 18 → List (Fin 3) :=
  ![[0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 2, 1], [0, 0, 2, 2],
    [0, 1, 0, 2], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 2, 1], [0, 1, 2, 2], [0, 2, 1, 1],
    [0, 2, 1, 2], [0, 2, 2, 1], [0, 2, 2, 2], [1, 1, 1, 2], [1, 1, 2, 2], [1, 2, 2, 2]]

/-- The content of the `i`-th Lyndon word of length four. -/
def lyndon4Content (i : Fin 18) : Fin 3 → ℕ := wordContent (lyndon4Word i)

theorem lyndon4Content_mem : ∀ i, lyndon4Content i ∈ Finset.Nat.antidiagonalTuple 3 4 := by
  decide

/-- Each Lyndon bracket is homogeneous of the content of its Lyndon word. -/
theorem lyndon4_mem_homog4 (i : Fin 18) : lyndon4 (R := R) i ∈ homog4 (lyndon4Content i) := by
  fin_cases i
  exacts [(br_mem_homog4 0 0 0 1).1, (br_mem_homog4 0 0 0 2).1, (br_mem_homog4 0 0 1 1).2.2.1,
    (br_mem_homog4 0 0 1 2).1, (br_mem_homog4 0 0 2 1).2.2.1, (br_mem_homog4 0 0 2 2).2.2.1,
    (br_mem_homog4 0 1 0 2).2.1, (br_mem_homog4 0 1 1 1).2.2.2.2, (br_mem_homog4 0 1 1 2).1,
    (br_mem_homog4 0 1 2 1).2.2.2.1, (br_mem_homog4 0 1 2 2).2.2.1,
    (br_mem_homog4 0 2 1 1).2.2.2.2, (br_mem_homog4 0 2 1 2).2.1,
    (br_mem_homog4 0 2 2 1).2.2.2.2, (br_mem_homog4 0 2 2 2).2.2.2.2, (br_mem_homog4 1 1 1 2).1,
    (br_mem_homog4 1 1 2 2).2.2.1, (br_mem_homog4 1 2 2 2).2.2.2.2]

/-- `m(κ)`: the number of Lyndon words of length four and content `κ`. -/
def mult4 (κ : Fin 3 → ℕ) : ℕ := (Finset.univ.filter fun i => lyndon4Content i = κ).card

/-- **The generalized Witt formula at degree four, exactly**: `4 · m(κ)` is the
Möbius sum at every content of degree four. -/
theorem mult4_witt :
    ∀ κ ∈ Finset.Nat.antidiagonalTuple 3 4, 4 * (mult4 κ : ℤ) = wittSum κ := by
  have h : ∀ κ ∈ Finset.Nat.antidiagonalTuple 3 4, 4 * (mult4 κ : ℤ) = wittSumSmall κ ∧
      ∀ t ∈ (Nat.gcd (κ 0) (Nat.gcd (κ 1) (κ 2))).divisors, t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
    decide +kernel
  exact fun κ hκ => (h κ hκ).1.trans (wittSum_eq_small (h κ hκ).2).symm

/-- `m(κ) = wittMult κ` at every content of degree four. -/
theorem mult4_eq_wittMult :
    ∀ κ ∈ Finset.Nat.antidiagonalTuple 3 4, (mult4 κ : ℚ) = wittMult κ := fun κ hκ =>
  eq_wittMult four_ne_zero hκ (by exact_mod_cast mult4_witt κ hκ)

/-- The contents of degree four are the permutations of the four shapes
`(4,0,0)`, `(3,1,0)`, `(2,2,0)`, `(2,1,1)`. -/
theorem shapes4 : ∀ κ ∈ Finset.Nat.antidiagonalTuple 3 4, ∃ σ : Equiv.Perm (Fin 3),
    κ = ![4, 0, 0] ∘ σ ∨ κ = ![3, 1, 0] ∘ σ ∨ κ = ![2, 2, 0] ∘ σ ∨ κ = ![2, 1, 1] ∘ σ := by
  decide

/-- The multiplicities by shape: `(4,0,0) ↦ 0`, `(3,1,0) ↦ 1`, `(2,2,0) ↦ 1`,
`(2,1,1) ↦ 3`. -/
theorem mult4_shapes : ∀ σ : Equiv.Perm (Fin 3),
    mult4 (![4, 0, 0] ∘ σ) = 0 ∧ mult4 (![3, 1, 0] ∘ σ) = 1 ∧ mult4 (![2, 2, 0] ∘ σ) = 1 ∧
      mult4 (![2, 1, 1] ∘ σ) = 3 := by
  decide

/-- `6 · 1 + 3 · 1 + 3 · 3 = 18`. -/
theorem sum_mult4 : ∑ κ ∈ Finset.Nat.antidiagonalTuple 3 4, mult4 κ = 18 := by
  decide

end Content4

section Content4Field

variable {F : Type*} [Field F] [CharZero F]

/-- **Each content component is spanned by the Lyndon brackets of that
content.** -/
theorem comp4_eq_span (κ : Fin 3 → ℕ) :
    comp4 (R := F) κ =
      Submodule.span F (Set.range fun i : {i // lyndon4Content i = κ} => lyndon4 (R := F) i.1) := by
  rw [comp4, shuffleAnnih4Space_eq_span]
  exact span_inf_eq_of_proj lyndon4_mem_homog4 proj4_of_mem proj4_of_mem_ne κ

/-- **Generalized Witt multiplicities as dimensions**: the content-`κ` component
of `Lie₄` has dimension `m(κ)`. -/
theorem finrank_comp4 (κ : Fin 3 → ℕ) : Module.finrank F (comp4 (R := F) κ) = mult4 κ := by
  have h := finrank_span_inf_eq (linearIndependent_lyndon4 (R := F)) lyndon4_mem_homog4
    proj4_of_mem proj4_of_mem_ne κ
  rw [comp4, shuffleAnnih4Space_eq_span]
  exact h

/-- The dimensions by shape: `0` for `(4,0,0)`, `1` for `(3,1,0)` and `(2,2,0)`,
`3` for `(2,1,1)`. -/
theorem finrank_comp4_shapes (σ : Equiv.Perm (Fin 3)) :
    Module.finrank F (comp4 (R := F) (![4, 0, 0] ∘ σ)) = 0 ∧
      Module.finrank F (comp4 (R := F) (![3, 1, 0] ∘ σ)) = 1 ∧
      Module.finrank F (comp4 (R := F) (![2, 2, 0] ∘ σ)) = 1 ∧
      Module.finrank F (comp4 (R := F) (![2, 1, 1] ∘ σ)) = 3 := by
  simpa only [finrank_comp4] using mult4_shapes σ

theorem comp4_eq_bot (σ : Equiv.Perm (Fin 3)) : comp4 (R := F) (![4, 0, 0] ∘ σ) = ⊥ :=
  Submodule.finrank_eq_zero.mp (finrank_comp4_shapes σ).1

/-- The dimensions add up: `Σ_κ dim = 6 · 1 + 3 · 1 + 3 · 3 = 18 = dim Lie₄`. -/
theorem sum_finrank_comp4 :
    ∑ κ ∈ Finset.Nat.antidiagonalTuple 3 4, Module.finrank F (comp4 (R := F) κ) = 18 := by
  simpa only [finrank_comp4] using sum_mult4

end Content4Field

/-! ### Degree four: weights -/

section Weights4

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `(diag x)^{⊗4}` multiplies the coordinate at `abcd` by `x_a x_b x_c x_d`. -/
theorem phi4_diagonal (x : Fin 3 → R) (f : Vec4 R) :
    phi4 (Matrix.diagonal x) f = fun a b c d => x a * x b * x c * x d * f a b c d := by
  funext a b c d
  simp [phi4, Matrix.diagonal_apply, ite_mul, mul_ite, Finset.sum_ite_eq]

/-- **Diagonal action**: `(diag x)^{⊗4}` acts on the content-`κ` subspace as
multiplication by `x^κ`. -/
theorem phi4_diagonal_of_mem {κ : Fin 3 → ℕ} {f : Vec4 R} (x : Fin 3 → R) (hf : f ∈ homog4 κ) :
    phi4 (Matrix.diagonal x) f = mono x κ • f := by
  rw [phi4_diagonal]
  funext a b c d
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h : wordContent [a, b, c, d] = κ
  · rw [← h, mono_wordContent]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  · rw [hf a b c d h]; ring

/-- `M^{⊗4}` commutes with every ring homomorphism. -/
theorem phi4_map (φ : R →+* S) (M : Matrix (Fin 3) (Fin 3) R) (f : Vec4 R) :
    phi4 (M.map φ) (map4 φ f) = map4 φ (phi4 M f) := by
  funext a b c d
  simp [phi4, map4, map_sum, map_mul, Matrix.map_apply]

/-- The coordinates of `(R³)^{⊗4}` flattened to `((Fin 3 × Fin 3) × Fin 3) × Fin 3`. -/
def flat4 (f : Vec4 R) : ((Fin 3 × Fin 3) × Fin 3) × Fin 3 → R :=
  fun i => f i.1.1.1 i.1.1.2 i.1.2 i.2

omit [CommRing R] in
theorem flat4_injective : Function.Injective (flat4 (R := R)) := fun f g h => by
  funext a b c d; exact congrFun h (((a, b), c), d)

open scoped Kronecker in
/-- `phi4 M` is the fourfold Kronecker power of `M` on flattened coordinates. -/
theorem flat4_phi4 (M : Matrix (Fin 3) (Fin 3) R) (f : Vec4 R) :
    flat4 (phi4 M f) = Matrix.mulVec (M ⊗ₖ M ⊗ₖ M ⊗ₖ M) (flat4 f) := by
  funext ⟨⟨⟨a, b⟩, c⟩, d⟩
  simp [flat4, phi4, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]

/-- `(AB)^{⊗4} = A^{⊗4} B^{⊗4}`. -/
theorem phi4_mul (A B : Matrix (Fin 3) (Fin 3) R) (f : Vec4 R) :
    phi4 (A * B) f = phi4 A (phi4 B f) := flat4_injective <| by
  simp only [flat4_phi4, Matrix.mulVec_mulVec, Matrix.mul_kronecker_mul]

theorem phi4_one (f : Vec4 R) : phi4 1 f = f := by
  rw [← Matrix.diagonal_one, phi4_diagonal]; simp

/-- `M ↦ M^{⊗4}` as a monoid homomorphism into the endomorphisms of `(R³)^{⊗4}`. -/
def Phi4 : Matrix (Fin 3) (Fin 3) R →* Module.End R (Vec4 R) where
  toFun M :=
    { toFun := phi4 M
      map_add' f g := by funext a b c d; simp [phi4, mul_add, Finset.sum_add_distrib]
      map_smul' r f := by funext a b c d; simp [phi4, Finset.mul_sum, mul_comm, mul_left_comm] }
  map_one' := LinearMap.ext phi4_one
  map_mul' A B := LinearMap.ext (phi4_mul A B)

theorem Phi4_apply (M : Matrix (Fin 3) (Fin 3) R) (f : Vec4 R) : Phi4 M f = phi4 M f := rfl

/-- The Lyndon brackets are eigenvectors of every `(diag x)^{⊗4}`, with weight
`x^κ` for `κ` the content of the Lyndon word. -/
theorem lyndon4_eigen (x : Fin 3 → R) (i : Fin 18) :
    Phi4 (Matrix.diagonal x) (lyndon4 i) = mono x (lyndon4Content i) • lyndon4 (R := R) i :=
  phi4_diagonal_of_mem x (lyndon4_mem_homog4 i)

theorem map4_lyndon4 (φ : R →+* S) (i : Fin 18) : map4 φ (lyndon4 i) = lyndon4 i := by
  fin_cases i <;> simp [lyndon4, map4_brR, map4_brP, map4_brXL, map4_brRX, map4_brL]

theorem lyndon4Coeff_map4 (φ : R →+* S) (f : Vec4 R) (i : Fin 18) :
    lyndon4Coeff (map4 φ f) i = φ (lyndon4Coeff f i) := by
  fin_cases i <;> simp [lyndon4Coeff, map4, map_ofNat]

end Weights4

/-- Non-vacuity of `phi4_diagonal_of_mem`: the nonzero bracket
`lyndon4 0 = [0,[0,[0,1]]]` has content `(3, 1, 0)` and weight `x₀³ x₁`. -/
theorem phi4_diagonal_control (x : Fin 3 → ℚ) :
    lyndon4 (R := ℚ) 0 ≠ 0 ∧
      phi4 (Matrix.diagonal x) (lyndon4 0) = (x 0 ^ 3 * x 1) • lyndon4 0 := by
  refine ⟨lyndon4_ne_zero 0, ?_⟩
  rw [phi4_diagonal_of_mem x (lyndon4_mem_homog4 0)]
  congr 1
  simp [mono, lyndon4Content, lyndon4Word, wordContent, Fin.prod_univ_three]

section Weights4Field

variable {F : Type*} [Field F] [CharZero F]

/-- `Φ₄ = M^{⊗4}` restricted to `Lie₄`, the span of the 18 Lyndon brackets
(`= shuffleAnnih4Space`, `shuffleAnnih4Space_eq_span`). -/
def phi4Lie (M : Matrix (Fin 3) (Fin 3) F) :
    Module.End F (Submodule.span F (Set.range (lyndon4 (R := F)))) :=
  (Phi4 M).restrict fun _ hf => phi4_mem_span M hf

/-- If `M = Q (diag x) Q⁻¹` with `Q` invertible, `Φ₄` has an eigenbasis (the
images of the Lyndon brackets under `Q^{⊗4}`) with the weights
`x^{content(wᵢ)}` of the 18 Lyndon words `wᵢ`. -/
theorem exists_eigenbasis_phi4Lie (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    ∃ b : Module.Basis (Fin 18) F (Submodule.span F (Set.range (lyndon4 (R := F)))),
      ∀ i, phi4Lie M (b i) = mono x (lyndon4Content i) • b i := by
  subst hM
  have hW : ∀ A, ∀ f ∈ Submodule.span F (Set.range (lyndon4 (R := F))),
      Phi4 A f ∈ Submodule.span F (Set.range lyndon4) :=
    fun A _ hf => phi4_mem_span A hf
  have hli := linearIndependent_lyndon4 (R := F)
  have hD := lyndon4_eigen (R := F) x
  have h := exists_eigenbasis_conj (V := Vec4 F) Phi4 hli hW hQ hD
  unfold phi4Lie
  exact h

/-- `χ(Φ₄) = ∏ᵢ (X - x^{content(wᵢ)})` over the 18 Lyndon words `wᵢ`. -/
theorem charpoly_phi4Lie_prod (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    (phi4Lie M).charpoly = ∏ i, (X - C (mono x (lyndon4Content i))) := by
  obtain ⟨b, hb⟩ := exists_eigenbasis_phi4Lie M Q x hQ hM
  exact charpoly_of_eigenbasis b hb

/-- **Weights of `Φ₄`**: if `M = Q (diag x) Q⁻¹` with `Q` invertible, then
`χ(Φ₄) = ∏_κ (X - x^κ)^{m(κ)}`, `m(κ) = dim` of the content-`κ` component. -/
theorem charpoly_phi4Lie (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F) (hQ : IsUnit Q.det)
    (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    (phi4Lie M).charpoly =
      ∏ κ ∈ Finset.Nat.antidiagonalTuple 3 4,
        (X - C (mono x κ)) ^ Module.finrank F (comp4 (R := F) κ) := by
  simp only [finrank_comp4]
  rw [charpoly_phi4Lie_prod M Q x hQ hM]
  exact prod_regroup lyndon4Content _ lyndon4Content_mem fun κ => X - C (mono x κ)

/-- **Weights of `Φ₄` with the Witt multiplicities**, in one statement: the
exponents are the generalized Witt formula and the component dimensions. -/
theorem charpoly_phi4Lie_witt (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    ∃ m : (Fin 3 → ℕ) → ℕ,
      (∀ κ ∈ Finset.Nat.antidiagonalTuple 3 4,
        (m κ : ℚ) = wittMult κ ∧ m κ = Module.finrank F (comp4 (R := F) κ)) ∧
      (phi4Lie M).charpoly = ∏ κ ∈ Finset.Nat.antidiagonalTuple 3 4, (X - C (mono x κ)) ^ m κ :=
  ⟨mult4, fun κ hκ => ⟨mult4_eq_wittMult κ hκ, (finrank_comp4 κ).symm⟩, by
    rw [charpoly_phi4Lie M Q x hQ hM]; simp only [finrank_comp4]⟩

/-- `χ(Φ₄)` is the characteristic polynomial of the explicit `18 × 18` matrix of
Ree coefficients `lyndon4Coeff (M^{⊗4} (lyndon4 j)) i`. -/
theorem charpoly_phi4Lie_eq (M : Matrix (Fin 3) (Fin 3) F) :
    (phi4Lie M).charpoly =
      (Matrix.of fun i j => lyndon4Coeff (phi4 M (lyndon4 j)) i).charpoly := by
  have hW : ∀ f ∈ Submodule.span F (Set.range (lyndon4 (R := F))),
      Phi4 M f ∈ Submodule.span F (Set.range lyndon4) :=
    fun _ hf => phi4_mem_span M hf
  have hcoeff : ∀ f ∈ Submodule.span F (Set.range (lyndon4 (R := F))),
      f = ∑ i, lyndon4Coeff f i • lyndon4 i :=
    fun f hf => eq_sum_lyndon4 ((shuffleAnnih4_iff_mem_span f).mpr hf)
  have hli := linearIndependent_lyndon4 (R := F)
  have h := toMatrix_restrict_span (V := Vec4 F) hli lyndon4Coeff hcoeff (Phi4 M) hW
  unfold phi4Lie
  rw [← LinearMap.charpoly_toMatrix _ (Module.Basis.span hli), h]
  rfl

/-- **Base change**: `χ(Φ₄)` commutes with every field homomorphism. -/
theorem charpoly_phi4Lie_map {K : Type*} [Field K] [CharZero K] (φ : F →+* K)
    (M : Matrix (Fin 3) (Fin 3) F) :
    (phi4Lie (M.map φ)).charpoly = (phi4Lie M).charpoly.map φ := by
  rw [charpoly_phi4Lie_eq, charpoly_phi4Lie_eq, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← map4_lyndon4 φ j, phi4_map,
    lyndon4Coeff_map4]

/-- **Weights of the rational `Φ₄`**: if a rational `M` is `Q (diag x) Q⁻¹` over a
field `F` of characteristic zero, the characteristic polynomial of the rational
`Φ₄`, read in `F`, is `∏_κ (X - x^κ)^{m(κ)}`, `m(κ) = dim_ℚ` of the rational
content-`κ` component. -/
theorem charpoly_phi4Lie_rat (M : Matrix (Fin 3) (Fin 3) ℚ) (Q : Matrix (Fin 3) (Fin 3) F)
    (x : Fin 3 → F) (hQ : IsUnit Q.det)
    (hM : M.map (algebraMap ℚ F) = Q * Matrix.diagonal x * Q⁻¹) :
    (phi4Lie M).charpoly.map (algebraMap ℚ F) =
      ∏ κ ∈ Finset.Nat.antidiagonalTuple 3 4,
        (X - C (mono x κ)) ^ Module.finrank ℚ (comp4 (R := ℚ) κ) := by
  rw [← charpoly_phi4Lie_map, charpoly_phi4Lie _ Q x hQ hM]
  simp only [finrank_comp4]

/-- The conjugating matrix of the control. -/
def Q₀ : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

/-- Non-vacuity of the conjugation hypotheses: the non-diagonal
`!![1, 1, 0; 0, 2, 0; 0, 0, 3]` is `Q₀ (diag (1, 2, 3)) Q₀⁻¹` with `det Q₀ = 1`. -/
theorem conj_control :
    IsUnit Q₀.det ∧ !![1, 1, 0; 0, 2, 0; 0, 0, 3] = Q₀ * Matrix.diagonal ![1, 2, 3] * Q₀⁻¹ := by
  have hdet : Q₀.det = 1 := by simp [Q₀, Matrix.det_fin_three]
  have hinv : Q₀⁻¹ = !![1, -1, 0; 0, 1, 0; 0, 0, 1] := Matrix.inv_eq_left_inv <| by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Q₀, Matrix.mul_apply, Fin.sum_univ_three]
  refine ⟨by rw [hdet]; exact isUnit_one, ?_⟩
  rw [hinv]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> norm_num [Q₀]

end Weights4Field

/-! ### Degree three over any commutative ring -/

/-- Coordinates of a tensor in `(R³)^{⊗3}` in the word basis; `Psc.Lie3.Vec3`
is `Vec3R ℚ`. -/
abbrev Vec3R (R : Type*) := Fin 3 → Fin 3 → Fin 3 → R

section Ring3

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The shuffle relations `a ⧢ bc` and `ab ⧢ c` of `Psc.Lie3.ShuffleAnnih`,
over `R` (`shuffleAnnih3_rat`). -/
def ShuffleAnnih3 (f : Vec3R R) : Prop :=
  ∀ a b c, f a b c + f b a c + f b c a = 0 ∧ f a b c + f a c b + f c a b = 0

theorem shuffleAnnih3_rat : ShuffleAnnih3 (R := ℚ) = Lie3.ShuffleAnnih := rfl

/-- The shuffle annihilator in `(R³)^{⊗3}` (`shuffleAnnih3Space_rat`). -/
def shuffleAnnih3Space : Submodule R (Vec3R R) where
  carrier := {f | ShuffleAnnih3 f}
  add_mem' {f g} hf hg a b c := by
    obtain ⟨hf1, hf2⟩ := hf a b c
    obtain ⟨hg1, hg2⟩ := hg a b c
    simp only [Pi.add_apply]
    exact ⟨by linear_combination hf1 + hg1, by linear_combination hf2 + hg2⟩
  zero_mem' _ _ _ := by simp
  smul_mem' r f hf a b c := by
    obtain ⟨h1, h2⟩ := hf a b c
    simp only [Pi.smul_apply, smul_eq_mul]
    exact ⟨by linear_combination r * h1, by linear_combination r * h2⟩

theorem shuffleAnnih3Space_rat : shuffleAnnih3Space (R := ℚ) = Lie3.shuffleAnnihSpace := rfl

/-- Coordinatewise image under a ring homomorphism. -/
def map3 (φ : R →+* S) (f : Vec3R R) : Vec3R S := fun a b c => φ (f a b c)

theorem ShuffleAnnih3.map (φ : R →+* S) {f : Vec3R R} (h : ShuffleAnnih3 f) :
    ShuffleAnnih3 (map3 φ f) := fun a b c => by
  obtain ⟨h1, h2⟩ := h a b c
  exact ⟨by simpa [map3] using congrArg φ h1, by simpa [map3] using congrArg φ h2⟩

/-- `M^{⊗3}` in word-basis coordinates (`phi3R_rat`). -/
def phi3R (M : Matrix (Fin 3) (Fin 3) R) (f : Vec3R R) : Vec3R R :=
  fun a b c => ∑ x, ∑ y, ∑ z, M a x * M b y * M c z * f x y z

theorem phi3R_rat : phi3R (R := ℚ) = Lie3.phi3 := rfl

/-- The shuffle relations are natural: `M^{⊗3}` maps the shuffle annihilator
into itself (the relations at `(x, y, z)` weighted by `M a x · M b y · M c z`).
`Psc.Lie3.shuffleAnnih_phi3` is the instance `R = ℚ`. -/
theorem shuffleAnnih3_phi3R (M : Matrix (Fin 3) (Fin 3) R) {f : Vec3R R} (hf : ShuffleAnnih3 f) :
    ShuffleAnnih3 (phi3R M f) := by
  intro a b c
  have k₁ : ∑ x, ∑ y, ∑ z, M a x * M b y * M c z * (f x y z + f y x z + f y z x) = 0 := by
    simp [(hf _ _ _).1]
  have k₂ : ∑ x, ∑ y, ∑ z, M a x * M b y * M c z * (f x y z + f x z y + f z x y) = 0 := by
    simp [(hf _ _ _).2]
  simp only [phi3R, Fin.sum_univ_three] at k₁ k₂ ⊢
  exact ⟨by linear_combination k₁, by linear_combination k₂⟩

/-- `M^{⊗3}` commutes with every ring homomorphism. -/
theorem phi3R_map (φ : R →+* S) (M : Matrix (Fin 3) (Fin 3) R) (f : Vec3R R) :
    phi3R (M.map φ) (map3 φ f) = map3 φ (phi3R M f) := by
  funext a b c
  simp [phi3R, map3, map_sum, map_mul, Matrix.map_apply]

/-- The coefficients of `Psc.Lie3.lyndonCoeff`, over `R` (`lyndon3Coeff_rat`). -/
def lyndon3Coeff (f : Vec3R R) : Fin 8 → R :=
  ![f 0 0 1, f 0 0 2, f 0 1 1, f 0 1 2, f 0 1 2 + f 0 2 1, f 0 2 2, f 1 1 2, f 1 2 2]

theorem lyndon3Coeff_rat : lyndon3Coeff (R := ℚ) = Lie3.lyndonCoeff := rfl

theorem lyndon3Coeff_map3 (φ : R →+* S) (f : Vec3R R) (i : Fin 8) :
    lyndon3Coeff (map3 φ f) i = φ (lyndon3Coeff f i) := by
  fin_cases i <;> simp [lyndon3Coeff, map3]

theorem wordContent_mem3 (a b c : Fin 3) :
    wordContent [a, b, c] ∈ Finset.Nat.antidiagonalTuple 3 3 :=
  wordContent_mem _

/-- Vectors of `(R³)^{⊗3}` supported on the words of content `κ`. -/
def homog3 (κ : Fin 3 → ℕ) : Submodule R (Vec3R R) where
  carrier := {f | ∀ a b c, wordContent [a, b, c] ≠ κ → f a b c = 0}
  add_mem' hf hg a b c h := by simp [hf a b c h, hg a b c h]
  zero_mem' _ _ _ _ := rfl
  smul_mem' r f hf a b c h := by simp [hf a b c h]

/-- The projection of `(R³)^{⊗3}` onto the words of content `κ`. -/
def proj3 (κ : Fin 3 → ℕ) : Vec3R R →ₗ[R] Vec3R R where
  toFun f a b c := if wordContent [a, b, c] = κ then f a b c else 0
  map_add' f g := by funext a b c; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' r f := by
    funext a b c; simp only [Pi.smul_apply, RingHom.id_apply]; split_ifs <;> simp

theorem proj3_apply (κ : Fin 3 → ℕ) (f : Vec3R R) (a b c : Fin 3) :
    proj3 κ f a b c = if wordContent [a, b, c] = κ then f a b c else 0 := rfl

theorem proj3_mem_homog3 (κ : Fin 3 → ℕ) (f : Vec3R R) : proj3 κ f ∈ homog3 κ :=
  fun _ _ _ h => ite_eq_right h

theorem proj3_of_mem (κ : Fin 3 → ℕ) (f : Vec3R R) (hf : f ∈ homog3 κ) : proj3 κ f = f := by
  funext a b c
  rw [proj3_apply]
  split_ifs with h
  · rfl
  · exact (hf a b c h).symm

theorem proj3_of_mem_ne (κ κ' : Fin 3 → ℕ) (h : κ' ≠ κ) (f : Vec3R R) (hf : f ∈ homog3 κ') :
    proj3 κ f = 0 := by
  funext a b c
  rw [proj3_apply]
  split_ifs with hc
  · exact hf a b c fun e => h (e.symm.trans hc)
  · rfl

/-- The content projections sum to the identity. -/
theorem sum_proj3 (f : Vec3R R) : ∑ κ ∈ Finset.Nat.antidiagonalTuple 3 3, proj3 κ f = f := by
  funext a b c
  simp only [Finset.sum_apply, proj3_apply, Finset.sum_ite_eq, wordContent_mem3, ite_true]

theorem map3_mem_homog3 (φ : R →+* S) {κ : Fin 3 → ℕ} {f : Vec3R R} (hf : f ∈ homog3 κ) :
    map3 φ f ∈ homog3 κ := fun a b c h => by simp [map3, hf a b c h]

/-- The words of each shuffle relation at `(a, b, c)` have the content of
`abc`. -/
theorem wordContent_shuffle3 : ∀ a b c : Fin 3,
    wordContent [b, a, c] = wordContent [a, b, c] ∧ wordContent [b, c, a] = wordContent [a, b, c] ∧
      wordContent [a, c, b] = wordContent [a, b, c] ∧
      wordContent [c, a, b] = wordContent [a, b, c] := by
  decide

/-- **The shuffle relations at degree three are content-homogeneous.** -/
theorem shuffleAnnih3_proj3 (κ : Fin 3 → ℕ) {f : Vec3R R} (hf : ShuffleAnnih3 f) :
    ShuffleAnnih3 (proj3 κ f) := by
  intro a b c
  obtain ⟨e₁, e₂, e₃, e₄⟩ := wordContent_shuffle3 a b c
  simp only [proj3_apply, e₁, e₂, e₃, e₄]
  split_ifs
  · exact hf a b c
  · simp

/-- The content-`κ` component of `Lie₃`; over `ℚ` it is the component of
`Psc.Lie3.shuffleAnnihSpace` (`comp3_rat`). -/
def comp3 (κ : Fin 3 → ℕ) : Submodule R (Vec3R R) := shuffleAnnih3Space ⊓ homog3 κ

theorem comp3_rat (κ : Fin 3 → ℕ) : comp3 (R := ℚ) κ = Lie3.shuffleAnnihSpace ⊓ homog3 κ := rfl

/-- The content subspaces of `(R³)^{⊗3}` are independent. -/
theorem iSupIndep_homog3 : iSupIndep (homog3 (R := R)) :=
  iSupIndep_of_proj (π := proj3) proj3_of_mem proj3_of_mem_ne

/-- **`Lie₃` is the internal direct sum of its content components**, first half:
independence. -/
theorem iSupIndep_comp3 : iSupIndep (comp3 (R := R)) :=
  iSupIndep_homog3.mono fun _ => inf_le_right

/-- Second half: the components span `Lie₃`; over `ℚ`, `⨆ κ, comp3 κ` is
`Psc.Lie3.shuffleAnnihSpace` (`shuffleAnnih3Space_rat`). -/
theorem iSup_comp3 : ⨆ κ, comp3 (R := R) κ = shuffleAnnih3Space :=
  iSup_inf_eq_of_proj _ _ sum_proj3 (fun κ _ hf => shuffleAnnih3_proj3 κ hf) proj3_mem_homog3

/-- `(diag x)^{⊗3}` multiplies the coordinate at `abc` by `x_a x_b x_c`. -/
theorem phi3R_diagonal (x : Fin 3 → R) (f : Vec3R R) :
    phi3R (Matrix.diagonal x) f = fun a b c => x a * x b * x c * f a b c := by
  funext a b c
  simp [phi3R, Matrix.diagonal_apply, ite_mul, mul_ite, Finset.sum_ite_eq]

/-- **Diagonal action**: `(diag x)^{⊗3}` acts on the content-`κ` subspace as
multiplication by `x^κ`. -/
theorem phi3R_diagonal_of_mem {κ : Fin 3 → ℕ} {f : Vec3R R} (x : Fin 3 → R) (hf : f ∈ homog3 κ) :
    phi3R (Matrix.diagonal x) f = mono x κ • f := by
  rw [phi3R_diagonal]
  funext a b c
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h : wordContent [a, b, c] = κ
  · rw [← h, mono_wordContent]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
    ring
  · rw [hf a b c h]; ring

/-- The coordinates of `(R³)^{⊗3}` flattened to `(Fin 3 × Fin 3) × Fin 3`. -/
def flat3 (f : Vec3R R) : (Fin 3 × Fin 3) × Fin 3 → R := fun i => f i.1.1 i.1.2 i.2

omit [CommRing R] in
theorem flat3_injective : Function.Injective (flat3 (R := R)) := fun f g h => by
  funext a b c; exact congrFun h ((a, b), c)

open scoped Kronecker in
/-- `phi3R M` is the threefold Kronecker power of `M` on flattened coordinates. -/
theorem flat3_phi3R (M : Matrix (Fin 3) (Fin 3) R) (f : Vec3R R) :
    flat3 (phi3R M f) = Matrix.mulVec (M ⊗ₖ M ⊗ₖ M) (flat3 f) := by
  funext ⟨⟨a, b⟩, c⟩
  simp [flat3, phi3R, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply]

/-- `(AB)^{⊗3} = A^{⊗3} B^{⊗3}`. -/
theorem phi3R_mul (A B : Matrix (Fin 3) (Fin 3) R) (f : Vec3R R) :
    phi3R (A * B) f = phi3R A (phi3R B f) := flat3_injective <| by
  simp only [flat3_phi3R, Matrix.mulVec_mulVec, Matrix.mul_kronecker_mul]

theorem phi3R_one (f : Vec3R R) : phi3R 1 f = f := by
  rw [← Matrix.diagonal_one, phi3R_diagonal]; simp

/-- `M ↦ M^{⊗3}` as a monoid homomorphism into the endomorphisms of `(R³)^{⊗3}`. -/
def Phi3 : Matrix (Fin 3) (Fin 3) R →* Module.End R (Vec3R R) where
  toFun M :=
    { toFun := phi3R M
      map_add' f g := by funext a b c; simp [phi3R, mul_add, Finset.sum_add_distrib]
      map_smul' r f := by funext a b c; simp [phi3R, Finset.mul_sum, mul_comm, mul_left_comm] }
  map_one' := LinearMap.ext phi3R_one
  map_mul' A B := LinearMap.ext (phi3R_mul A B)

theorem Phi3_apply (M : Matrix (Fin 3) (Fin 3) R) (f : Vec3R R) : Phi3 M f = phi3R M f := rfl

end Ring3

/-! ### Degree three: the Lyndon brackets of `Psc.Lie3` by content -/

section Lie3Rat

/-- The eight Lyndon words of length three, in the order of `Psc.Lie3.lyndon`. -/
def lyndon3Word : Fin 8 → List (Fin 3) :=
  ![[0, 0, 1], [0, 0, 2], [0, 1, 1], [0, 1, 2], [0, 2, 1], [0, 2, 2], [1, 1, 2], [1, 2, 2]]

/-- The content of the `i`-th Lyndon word of length three. -/
def lyndon3Content (i : Fin 8) : Fin 3 → ℕ := wordContent (lyndon3Word i)

theorem lyndon3Content_mem : ∀ i, lyndon3Content i ∈ Finset.Nat.antidiagonalTuple 3 3 := by
  decide

theorem word_mem_homog3 (x y z : Fin 3) : Lie3.word x y z ∈ homog3 (wordContent [x, y, z]) :=
  fun a b c h => by
    unfold Lie3.word
    split_ifs with h' <;> first | rfl | (obtain ⟨rfl, rfl, rfl⟩ := h'; exact (h rfl).elim)

/-- Each bracket `[[x,y],z]` lies in the content-`[x, y, z]` subspace. -/
theorem br_mem_homog3 (x y z : Fin 3) : Lie3.br x y z ∈ homog3 (wordContent [x, y, z]) := by
  have W (p q r : Fin 3) (h : wordContent [p, q, r] = wordContent [x, y, z]) :
      Lie3.word p q r ∈ homog3 (wordContent [x, y, z]) := h ▸ word_mem_homog3 p q r
  unfold Lie3.br
  repeat' first
    | apply add_mem | apply sub_mem | exact word_mem_homog3 _ _ _
    | (apply W; funext i; simp only [wordContent_cons, wordContent_nil]; ring1)

/-- Each Lyndon bracket of `Psc.Lie3` is homogeneous of the content of its
Lyndon word. -/
theorem lyndon_mem_homog3 (i : Fin 8) : Lie3.lyndon i ∈ homog3 (lyndon3Content i) := by
  have H (x y z : Fin 3) (j : Fin 8) (h : wordContent [x, y, z] = lyndon3Content j) :
      Lie3.br x y z ∈ homog3 (lyndon3Content j) := h ▸ br_mem_homog3 x y z
  fin_cases i
  exacts [neg_mem (H 0 1 0 _ (by decide)), neg_mem (H 0 2 0 _ (by decide)), H 0 1 1 _ (by decide),
    neg_mem (H 1 2 0 _ (by decide)), H 0 2 1 _ (by decide), H 0 2 2 _ (by decide),
    neg_mem (H 1 2 1 _ (by decide)), H 1 2 2 _ (by decide)]

/-- **Diagonal action on `Psc.Lie3`**: `Psc.Lie3.phi3 (diag x)` acts on the
content-`κ` subspace as multiplication by `x^κ`. -/
theorem lie3_phi3_diagonal_of_mem {κ : Fin 3 → ℕ} {f : Lie3.Vec3} (x : Fin 3 → ℚ)
    (hf : f ∈ homog3 κ) : Lie3.phi3 (Matrix.diagonal x) f = mono x κ • f :=
  phi3R_diagonal_of_mem x hf

/-- `m(κ)`: the number of Lyndon words of length three and content `κ`. -/
def mult3 (κ : Fin 3 → ℕ) : ℕ := (Finset.univ.filter fun i => lyndon3Content i = κ).card

/-- **The generalized Witt formula at degree three, exactly**: `3 · m(κ)` is the
Möbius sum at every content of degree three. -/
theorem mult3_witt :
    ∀ κ ∈ Finset.Nat.antidiagonalTuple 3 3, 3 * (mult3 κ : ℤ) = wittSum κ := by
  have h : ∀ κ ∈ Finset.Nat.antidiagonalTuple 3 3, 3 * (mult3 κ : ℤ) = wittSumSmall κ ∧
      ∀ t ∈ (Nat.gcd (κ 0) (Nat.gcd (κ 1) (κ 2))).divisors, t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 := by
    decide +kernel
  exact fun κ hκ => (h κ hκ).1.trans (wittSum_eq_small (h κ hκ).2).symm

/-- `m(κ) = wittMult κ` at every content of degree three. -/
theorem mult3_eq_wittMult :
    ∀ κ ∈ Finset.Nat.antidiagonalTuple 3 3, (mult3 κ : ℚ) = wittMult κ := fun κ hκ =>
  eq_wittMult three_ne_zero hκ (by exact_mod_cast mult3_witt κ hκ)

/-- The contents of degree three are the permutations of `(3,0,0)`, `(2,1,0)`,
`(1,1,1)`. -/
theorem shapes3 : ∀ κ ∈ Finset.Nat.antidiagonalTuple 3 3, ∃ σ : Equiv.Perm (Fin 3),
    κ = ![3, 0, 0] ∘ σ ∨ κ = ![2, 1, 0] ∘ σ ∨ κ = ![1, 1, 1] ∘ σ := by
  decide

/-- The multiplicities by shape: `(3,0,0) ↦ 0`, `(2,1,0) ↦ 1`, `(1,1,1) ↦ 2`. -/
theorem mult3_shapes : ∀ σ : Equiv.Perm (Fin 3),
    mult3 (![3, 0, 0] ∘ σ) = 0 ∧ mult3 (![2, 1, 0] ∘ σ) = 1 ∧ mult3 (![1, 1, 1] ∘ σ) = 2 := by
  decide

/-- `6 · 1 + 2 = 8`. -/
theorem sum_mult3 : ∑ κ ∈ Finset.Nat.antidiagonalTuple 3 3, mult3 κ = 8 := by
  decide

end Lie3Rat

/-! ### Degree three over a field of characteristic zero

`Psc.Lie3` is stated over `ℚ`.  Over `F`, the Lyndon brackets are their images
(`lyndon3`), and Ree's theorem and linear independence are transported from
`Psc.Lie3.eq_sum_lyndon` and `Psc.Lie3.linearIndependent_lyndon` through the
`ℚ`-linear functionals `F → ℚ`, which separate the points of `F` (`dual3`). -/

section Lie3Field

variable {F : Type*} [Field F] [CharZero F]

/-- The eight Lyndon brackets `Psc.Lie3.lyndon`, read over `F`. -/
def lyndon3 (i : Fin 8) : Vec3R F := map3 (Rat.castHom F) (Lie3.lyndon i)

theorem lyndon3_rat : lyndon3 (F := ℚ) = Lie3.lyndon := by
  funext i a b c; simp [lyndon3, map3]

theorem map3_lyndon3 {K : Type*} [Field K] [CharZero K] (φ : F →+* K) (i : Fin 8) :
    map3 φ (lyndon3 i) = lyndon3 i := by
  funext a b c; simp [lyndon3, map3]

theorem lyndon3_mem (i : Fin 8) : lyndon3 (F := F) i ∈ shuffleAnnih3Space :=
  ShuffleAnnih3.map _ (Lie3.lyndon_mem i)

theorem lyndon3_mem_homog3 (i : Fin 8) : lyndon3 (F := F) i ∈ homog3 (lyndon3Content i) :=
  map3_mem_homog3 _ (lyndon_mem_homog3 i)

/-- The Lyndon brackets are eigenvectors of every `(diag x)^{⊗3}`. -/
theorem lyndon3_eigen (x : Fin 3 → F) (i : Fin 8) :
    Phi3 (Matrix.diagonal x) (lyndon3 i) = mono x (lyndon3Content i) • lyndon3 i :=
  phi3R_diagonal_of_mem x (lyndon3_mem_homog3 i)

/-- A `ℚ`-linear functional on `F`, applied coordinatewise. -/
def dual3 (φ : Module.Dual ℚ F) (f : Vec3R F) : Lie3.Vec3 := fun a b c => φ (f a b c)

theorem dual_mul_ratCast (φ : Module.Dual ℚ F) (y : F) (q : ℚ) : φ (y * q) = φ y * q := by
  rw [mul_comm, ← Rat.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem ShuffleAnnih3.dual3 (φ : Module.Dual ℚ F) {f : Vec3R F} (h : ShuffleAnnih3 f) :
    Lie3.ShuffleAnnih (dual3 φ f) := fun a b c => by
  obtain ⟨h1, h2⟩ := h a b c
  exact ⟨by simpa [LieWeights.dual3] using congrArg φ h1,
    by simpa [LieWeights.dual3] using congrArg φ h2⟩

theorem dual3_lyndon3Coeff (φ : Module.Dual ℚ F) (f : Vec3R F) (i : Fin 8) :
    φ (lyndon3Coeff f i) = Lie3.lyndonCoeff (dual3 φ f) i := by
  fin_cases i <;> simp [lyndon3Coeff, Lie3.lyndonCoeff, dual3]

/-- **Ree at degree three over `F`**, from `Psc.Lie3.eq_sum_lyndon`: both sides
agree under every `ℚ`-linear functional `F → ℚ`. -/
theorem eq_sum_lyndon3 {f : Vec3R F} (h : ShuffleAnnih3 f) :
    f = ∑ i, lyndon3Coeff f i • lyndon3 i := by
  funext a b c
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro φ
  have := congrFun (congrFun (congrFun (Lie3.eq_sum_lyndon (h.dual3 φ)) a) b) c
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_sum, lyndon3, map3,
    Rat.coe_castHom, dual_mul_ratCast, dual3_lyndon3Coeff]
  exact sub_eq_zero.mpr this

/-- **The eight Lyndon brackets are linearly independent over `F`**, from
`Psc.Lie3.linearIndependent_lyndon`. -/
theorem linearIndependent_lyndon3 : LinearIndependent F (lyndon3 (F := F)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  rw [← Module.forall_dual_apply_eq_zero_iff ℚ]
  intro φ
  refine Fintype.linearIndependent_iff.mp Lie3.linearIndependent_lyndon (fun j => φ (g j)) ?_ i
  funext a b c
  have := congrArg φ (congrFun (congrFun (congrFun hg a) b) c)
  simpa [Finset.sum_apply, lyndon3, map3, dual_mul_ratCast, map_sum] using this

/-- **Ree at degree three over `F`**: the shuffle annihilator is the span of the
eight Lyndon brackets. -/
theorem shuffleAnnih3_iff_mem_span (f : Vec3R F) :
    ShuffleAnnih3 f ↔ f ∈ Submodule.span F (Set.range lyndon3) := by
  constructor
  · intro h
    rw [eq_sum_lyndon3 h]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h
    have hle : Submodule.span F (Set.range lyndon3) ≤ shuffleAnnih3Space :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr lyndon3_mem)
    exact hle h

theorem shuffleAnnih3Space_eq_span :
    shuffleAnnih3Space = Submodule.span F (Set.range (lyndon3 (F := F))) :=
  Submodule.ext shuffleAnnih3_iff_mem_span

/-- **Each content component of `Lie₃` is spanned by the Lyndon brackets of that
content.** -/
theorem comp3_eq_span (κ : Fin 3 → ℕ) :
    comp3 (R := F) κ =
      Submodule.span F (Set.range fun i : {i // lyndon3Content i = κ} => lyndon3 (F := F) i.1) := by
  rw [comp3, shuffleAnnih3Space_eq_span]
  exact span_inf_eq_of_proj lyndon3_mem_homog3 proj3_of_mem proj3_of_mem_ne κ

/-- `comp3_eq_span` on `Psc.Lie3` itself. -/
theorem comp3_eq_span_rat (κ : Fin 3 → ℕ) :
    comp3 (R := ℚ) κ =
      Submodule.span ℚ (Set.range fun i : {i // lyndon3Content i = κ} => Lie3.lyndon i.1) := by
  rw [comp3_eq_span, lyndon3_rat]

/-- **Generalized Witt multiplicities as dimensions**: the content-`κ` component
of `Lie₃` has dimension `m(κ)`. -/
theorem finrank_comp3 (κ : Fin 3 → ℕ) : Module.finrank F (comp3 (R := F) κ) = mult3 κ := by
  have h := finrank_span_inf_eq (linearIndependent_lyndon3 (F := F)) lyndon3_mem_homog3
    proj3_of_mem proj3_of_mem_ne κ
  rw [comp3, shuffleAnnih3Space_eq_span]
  exact h

/-- The dimensions by shape: `0` for `(3,0,0)`, `1` for `(2,1,0)`, `2` for
`(1,1,1)`. -/
theorem finrank_comp3_shapes (σ : Equiv.Perm (Fin 3)) :
    Module.finrank F (comp3 (R := F) (![3, 0, 0] ∘ σ)) = 0 ∧
      Module.finrank F (comp3 (R := F) (![2, 1, 0] ∘ σ)) = 1 ∧
      Module.finrank F (comp3 (R := F) (![1, 1, 1] ∘ σ)) = 2 := by
  simpa only [finrank_comp3] using mult3_shapes σ

theorem comp3_eq_bot (σ : Equiv.Perm (Fin 3)) : comp3 (R := F) (![3, 0, 0] ∘ σ) = ⊥ :=
  Submodule.finrank_eq_zero.mp (finrank_comp3_shapes σ).1

/-- The dimensions add up: `6 · 1 + 2 = 8 = dim Lie₃`. -/
theorem sum_finrank_comp3 :
    ∑ κ ∈ Finset.Nat.antidiagonalTuple 3 3, Module.finrank F (comp3 (R := F) κ) = 8 := by
  simpa only [finrank_comp3] using sum_mult3

/-- **`Lie₃` over `F` is `M^{⊗3}`-invariant.** -/
theorem phi3R_mem_span (M : Matrix (Fin 3) (Fin 3) F) {f : Vec3R F}
    (hf : f ∈ Submodule.span F (Set.range lyndon3)) :
    phi3R M f ∈ Submodule.span F (Set.range lyndon3) :=
  (shuffleAnnih3_iff_mem_span _).mp (shuffleAnnih3_phi3R M ((shuffleAnnih3_iff_mem_span f).mpr hf))

/-- `Φ₃ = M^{⊗3}` restricted to `Lie₃`, the span of the eight Lyndon brackets
over `F` (`= shuffleAnnih3Space`, `shuffleAnnih3Space_eq_span`). -/
def phi3Lie (M : Matrix (Fin 3) (Fin 3) F) :
    Module.End F (Submodule.span F (Set.range (lyndon3 (F := F)))) :=
  (Phi3 M).restrict fun _ hf => phi3R_mem_span M hf

/-- If `M = Q (diag x) Q⁻¹` with `Q` invertible, `Φ₃` has an eigenbasis with
the weights `x^{content(wᵢ)}` of the eight Lyndon words `wᵢ`. -/
theorem exists_eigenbasis_phi3Lie (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    ∃ b : Module.Basis (Fin 8) F (Submodule.span F (Set.range (lyndon3 (F := F)))),
      ∀ i, phi3Lie M (b i) = mono x (lyndon3Content i) • b i := by
  subst hM
  have hW : ∀ A, ∀ f ∈ Submodule.span F (Set.range (lyndon3 (F := F))),
      Phi3 A f ∈ Submodule.span F (Set.range lyndon3) :=
    fun A _ hf => phi3R_mem_span A hf
  have hli := linearIndependent_lyndon3 (F := F)
  have hD := lyndon3_eigen (F := F) x
  have h := exists_eigenbasis_conj (V := Vec3R F) Phi3 hli hW hQ hD
  unfold phi3Lie
  exact h

/-- `χ(Φ₃) = ∏ᵢ (X - x^{content(wᵢ)})` over the eight Lyndon words. -/
theorem charpoly_phi3Lie_prod (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    (phi3Lie M).charpoly = ∏ i, (X - C (mono x (lyndon3Content i))) := by
  obtain ⟨b, hb⟩ := exists_eigenbasis_phi3Lie M Q x hQ hM
  exact charpoly_of_eigenbasis b hb

/-- **Weights of `Φ₃`**: `χ(Φ₃) = ∏_κ (X - x^κ)^{m(κ)}`, `m(κ) = dim` of the
content-`κ` component. -/
theorem charpoly_phi3Lie (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    (phi3Lie M).charpoly =
      ∏ κ ∈ Finset.Nat.antidiagonalTuple 3 3,
        (X - C (mono x κ)) ^ Module.finrank F (comp3 (R := F) κ) := by
  simp only [finrank_comp3]
  rw [charpoly_phi3Lie_prod M Q x hQ hM]
  exact prod_regroup lyndon3Content _ lyndon3Content_mem fun κ => X - C (mono x κ)

/-- **Weights of `Φ₃` with the Witt multiplicities**, in one statement. -/
theorem charpoly_phi3Lie_witt (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    ∃ m : (Fin 3 → ℕ) → ℕ,
      (∀ κ ∈ Finset.Nat.antidiagonalTuple 3 3,
        (m κ : ℚ) = wittMult κ ∧ m κ = Module.finrank F (comp3 (R := F) κ)) ∧
      (phi3Lie M).charpoly = ∏ κ ∈ Finset.Nat.antidiagonalTuple 3 3, (X - C (mono x κ)) ^ m κ :=
  ⟨mult3, fun κ hκ => ⟨mult3_eq_wittMult κ hκ, (finrank_comp3 κ).symm⟩, by
    rw [charpoly_phi3Lie M Q x hQ hM]; simp only [finrank_comp3]⟩

/-- **The spectral input of the proof of `thm:deg23` (iii)**: the weights of
`Φ₃` are `xᵢ² xⱼ` (`i ≠ j`) and `det M` with algebraic multiplicity two. -/
theorem charpoly_phi3Lie_explicit (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) :
    (phi3Lie M).charpoly =
      (X - C (x 0 ^ 2 * x 1)) * (X - C (x 0 ^ 2 * x 2)) * (X - C (x 0 * x 1 ^ 2)) *
        (X - C (x 0 * x 2 ^ 2)) * (X - C (x 1 ^ 2 * x 2)) * (X - C (x 1 * x 2 ^ 2)) *
        (X - C M.det) ^ 2 := by
  have hdet : M.det = x 0 * x 1 * x 2 := by
    rw [hM, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det Q).mpr hQ), Matrix.det_diagonal,
      Fin.prod_univ_three]
  rw [charpoly_phi3Lie_prod M Q x hQ hM, hdet, Fin.prod_univ_eight]
  simp only [lyndon3Content, lyndon3Word, mono, wordContent, Fin.prod_univ_three]
  simp [map_mul, map_pow]
  ring

/-- The `μ`-eigenspace of `Φ₃` has dimension the number of Lyndon words of
weight `μ`. -/
theorem finrank_ker_phi3Lie [DecidableEq F] (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) (μ : F) :
    Module.finrank F (LinearMap.ker (phi3Lie M - μ • 1)) =
      (Finset.univ.filter fun i => mono x (lyndon3Content i) = μ).card := by
  obtain ⟨b, hb⟩ := exists_eigenbasis_phi3Lie M Q x hQ hM
  exact finrank_ker_of_eigenbasis b hb μ

/-- **`ker (Φ₃ - det M)` is two-dimensional** (the clause "a two-dimensional
space" of `thm:deg23` (iii)) when the eigenvalues `xᵢ` are pairwise distinct
and nonzero: the weight `det M = x₀ x₁ x₂` is then carried by exactly the two
Lyndon words `012`, `021`. -/
theorem finrank_ker_phi3Lie_sub_det (M Q : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F)
    (hQ : IsUnit Q.det) (hM : M = Q * Matrix.diagonal x * Q⁻¹) (hx : Function.Injective x)
    (hx0 : ∀ i, x i ≠ 0) :
    Module.finrank F (LinearMap.ker (phi3Lie M - M.det • 1)) = 2 := by
  classical
  have hdet : M.det = x 0 * x 1 * x 2 := by
    rw [hM, Matrix.det_conj ((Matrix.isUnit_iff_isUnit_det Q).mpr hQ), Matrix.det_diagonal,
      Fin.prod_univ_three]
  have key {i j k : Fin 3} (hik : i ≠ k) : x i ^ 2 * x j ≠ x i * x j * x k := fun h =>
    hik (hx (mul_left_cancel₀ (mul_ne_zero (hx0 i) (hx0 j)) (by linear_combination h)))
  have hfilter : (Finset.univ.filter fun i : Fin 8 => mono x (lyndon3Content i) = x 0 * x 1 * x 2)
      = {3, 4} := by
    ext i
    fin_cases i <;>
      simp [lyndon3Content, lyndon3Word, mono, wordContent, Fin.prod_univ_three,
        -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;>
      first
        | exact fun h => key (i := 0) (j := 1) (k := 2) (by decide) (by linear_combination h)
        | exact fun h => key (i := 0) (j := 2) (k := 1) (by decide) (by linear_combination h)
        | exact fun h => key (i := 1) (j := 0) (k := 2) (by decide) (by linear_combination h)
        | exact fun h => key (i := 1) (j := 2) (k := 0) (by decide) (by linear_combination h)
        | exact fun h => key (i := 2) (j := 0) (k := 1) (by decide) (by linear_combination h)
        | exact fun h => key (i := 2) (j := 1) (k := 0) (by decide) (by linear_combination h)
  rw [finrank_ker_phi3Lie M Q x hQ hM, hdet, hfilter]
  rfl

/-- `χ(Φ₃)` is the characteristic polynomial of the explicit `8 × 8` matrix of
Ree coefficients `lyndon3Coeff (M^{⊗3} (lyndon3 j)) i`. -/
theorem charpoly_phi3Lie_eq (M : Matrix (Fin 3) (Fin 3) F) :
    (phi3Lie M).charpoly =
      (Matrix.of fun i j => lyndon3Coeff (phi3R M (lyndon3 j)) i).charpoly := by
  have hW : ∀ f ∈ Submodule.span F (Set.range (lyndon3 (F := F))),
      Phi3 M f ∈ Submodule.span F (Set.range lyndon3) :=
    fun _ hf => phi3R_mem_span M hf
  have hcoeff : ∀ f ∈ Submodule.span F (Set.range (lyndon3 (F := F))),
      f = ∑ i, lyndon3Coeff f i • lyndon3 i :=
    fun f hf => eq_sum_lyndon3 ((shuffleAnnih3_iff_mem_span f).mpr hf)
  have hli := linearIndependent_lyndon3 (F := F)
  have h := toMatrix_restrict_span (V := Vec3R F) hli lyndon3Coeff hcoeff (Phi3 M) hW
  unfold phi3Lie
  rw [← LinearMap.charpoly_toMatrix _ (Module.Basis.span hli), h]
  rfl

/-- **Base change**: `χ(Φ₃)` commutes with every field homomorphism. -/
theorem charpoly_phi3Lie_map {K : Type*} [Field K] [CharZero K] (φ : F →+* K)
    (M : Matrix (Fin 3) (Fin 3) F) :
    (phi3Lie (M.map φ)).charpoly = (phi3Lie M).charpoly.map φ := by
  rw [charpoly_phi3Lie_eq, charpoly_phi3Lie_eq, ← Matrix.charpoly_map]
  congr 1
  ext i j
  rw [Matrix.map_apply, Matrix.of_apply, Matrix.of_apply, ← map3_lyndon3 φ j, phi3R_map,
    lyndon3Coeff_map3]

/-- **Weights of the rational `Φ₃`** (on `Psc.Lie3`: over `ℚ`, `phi3R = Psc.Lie3.phi3`
and `lyndon3 = Psc.Lie3.lyndon`): if a rational `M` is `Q (diag x) Q⁻¹` over a
field `F` of characteristic zero, `χ(Φ₃)`, read in `F`, is
`∏_κ (X - x^κ)^{m(κ)}`, `m(κ) = dim_ℚ` of the rational content-`κ` component. -/
theorem charpoly_phi3Lie_rat (M : Matrix (Fin 3) (Fin 3) ℚ) (Q : Matrix (Fin 3) (Fin 3) F)
    (x : Fin 3 → F) (hQ : IsUnit Q.det)
    (hM : M.map (algebraMap ℚ F) = Q * Matrix.diagonal x * Q⁻¹) :
    (phi3Lie M).charpoly.map (algebraMap ℚ F) =
      ∏ κ ∈ Finset.Nat.antidiagonalTuple 3 3,
        (X - C (mono x κ)) ^ Module.finrank ℚ (comp3 (R := ℚ) κ) := by
  rw [← charpoly_phi3Lie_map, charpoly_phi3Lie _ Q x hQ hM]
  simp only [finrank_comp3]

end Lie3Field

/-! ### Controls -/

/-- Non-vacuity of `charpoly_phi3Lie` and `charpoly_phi4Lie`: both apply to the
non-diagonal `!![1, 1, 0; 0, 2, 0; 0, 0, 3] = Q₀ (diag (1, 2, 3)) Q₀⁻¹`. -/
theorem charpoly_control :
    (phi3Lie (!![1, 1, 0; 0, 2, 0; 0, 0, 3] : Matrix (Fin 3) (Fin 3) ℚ)).charpoly =
        ∏ κ ∈ Finset.Nat.antidiagonalTuple 3 3,
          (X - C (mono ![1, 2, 3] κ)) ^ Module.finrank ℚ (comp3 (R := ℚ) κ) ∧
      (phi4Lie (!![1, 1, 0; 0, 2, 0; 0, 0, 3] : Matrix (Fin 3) (Fin 3) ℚ)).charpoly =
        ∏ κ ∈ Finset.Nat.antidiagonalTuple 3 4,
          (X - C (mono ![1, 2, 3] κ)) ^ Module.finrank ℚ (comp4 (R := ℚ) κ) :=
  ⟨charpoly_phi3Lie _ Q₀ _ conj_control.1 conj_control.2,
    charpoly_phi4Lie _ Q₀ _ conj_control.1 conj_control.2⟩

/-- Non-vacuity of `finrank_ker_phi3Lie_sub_det`: the eigenvalues `1, 2, 3` of the
non-diagonal control are distinct and nonzero. -/
theorem ker_control :
    Module.finrank ℚ (LinearMap.ker
      (phi3Lie (!![1, 1, 0; 0, 2, 0; 0, 0, 3] : Matrix (Fin 3) (Fin 3) ℚ)
        - Matrix.det (!![1, 1, 0; 0, 2, 0; 0, 0, 3] : Matrix (Fin 3) (Fin 3) ℚ) • 1)) = 2 :=
  finrank_ker_phi3Lie_sub_det _ Q₀ ![1, 2, 3] conj_control.1 conj_control.2 (by decide)
    (by decide)

/-- Negative control: distinctness cannot be dropped from
`finrank_ker_phi3Lie_sub_det`.  For `diag (1, 1, 2)` (`det = 2`), the weight `2`
is carried by the four Lyndon words `002`, `012`, `021`, `112`. -/
theorem ker_needs_distinct :
    Module.finrank ℚ (LinearMap.ker (phi3Lie (Matrix.diagonal ![(1 : ℚ), 1, 2])
      - (Matrix.diagonal ![(1 : ℚ), 1, 2]).det • 1)) = 4 := by
  have hM : Matrix.diagonal ![(1 : ℚ), 1, 2] = 1 * Matrix.diagonal ![1, 1, 2] * 1⁻¹ := by simp
  have hdet : (Matrix.diagonal ![(1 : ℚ), 1, 2]).det = 2 := by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]
  have hfilter : (Finset.univ.filter fun i : Fin 8 =>
      mono ![(1 : ℚ), 1, 2] (lyndon3Content i) = 2) = {1, 3, 4, 6} := by
    ext i
    fin_cases i <;> simp [lyndon3Content, lyndon3Word, mono, wordContent, Fin.prod_univ_three] <;>
      norm_num
  rw [finrank_ker_phi3Lie _ 1 ![1, 1, 2] (by simp) hM, hdet, hfilter]
  rfl

end Psc.LieWeights

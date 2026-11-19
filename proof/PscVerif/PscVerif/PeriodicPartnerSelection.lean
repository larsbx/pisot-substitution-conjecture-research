/-
# Witness selection under (NM_V): the branch reduction (Theorem S)

This module checks the deductions of Theorem S in
`docs/c4-witness-selection-2026-11-19.md`.  Start from any same-fibre triple whose two
leaves are distinct and right-asymptotic.  The named BDS input and finite-fibre lifting
give a periodic translate (Lemma P).  Its branch then falls into exactly one of two
cases:

* **(A)** the branch is at the origin, the two-step endpoint test passes, both leaves
  end a tile at the origin, and all three points lie in the distinguished fibre;
* **(B)** the branch is strictly right of the origin, the two branch letters are
  identified by one application of the endpoint map, and neither leaf has a vertex at
  the origin.

(NM_V) enters only to exclude a vertex-type leaf from case (B).  When the endpoint map
has two periodic letters, case (B) uses the unique collapsed pair of that map.  Case
(B) itself is not excluded, its fibre is not identified, and no rank-two contradiction
is asserted.

Inputs are explicit: `RightBranchLaws`, `VertexLaws` and `BranchExistence` are local
contracts; `BDSPeriodicization`, `R4ZeroFibre`, `AsymptoticSameFibre` (E1) and `NMVRight`
are named hypotheses, not axioms.  The left orientation follows by the reflection of
`PscVerif.PeriodicPartnerReflection`; it is not restated here.
-/
import PscVerif.PeriodicPartnerDynamics

namespace Psc.PeriodicPartnerSelection

open Function Psc.PeriodicPartnerDynamics

/-! ## Three letters: the collapsed pair -/

/-- On three letters every periodic point satisfies `g^[6] p = p`. -/
theorem six_of_mem_periodicPts {g : Fin 3 → Fin 3} {p : Fin 3}
    (hp : p ∈ periodicPts g) : g^[6] p = p := by
  obtain ⟨n, hn, hpn⟩ := hp
  obtain ⟨k, hk⟩ : ∃ k, 2 * n = k + 2 := ⟨2 * n - 2, by omega⟩
  have hret : g^[2] (g^[k] p) = p := by
    rw [← iterate_add_apply, Nat.add_comm, ← hk]
    exact (hpn.const_mul 2).eq
  calc g^[6] p = g^[6] (g^[2] (g^[k] p)) := by rw [hret]
    _ = g^[2] (g^[k] p) := Psc.PeriodicPartner.endpoint_period_six g _
    _ = p := hret

theorem mem_periodicPts_iff_six (g : Fin 3 → Fin 3) (p : Fin 3) :
    p ∈ periodicPts g ↔ g^[6] p = p :=
  ⟨six_of_mem_periodicPts, fun h => ⟨6, by norm_num, h⟩⟩

/-- The census domain: at least two periodic letters for the endpoint map. -/
def TwoPeriodicLetters (g : Fin 3 → Fin 3) : Prop :=
  ∃ p q, p ≠ q ∧ g^[6] p = p ∧ g^[6] q = q

/-- With two periodic letters, a two-step merge is already a one-step merge. -/
theorem collapse_at_first_step :
    ∀ (g : Fin 3 → Fin 3) (p q b c : Fin 3), p ≠ q → g^[6] p = p → g^[6] q = q →
      b ≠ c → g^[2] b = g^[2] c → g b = g c := by
  decide

/-- With two periodic letters there is at most one collapsed unordered pair. -/
theorem collapsed_pair_unique :
    ∀ (g : Fin 3 → Fin 3) (p q b c d e : Fin 3), p ≠ q → g^[6] p = p → g^[6] q = q →
      b ≠ c → d ≠ e → g b = g c → g d = g e →
        (b = d ∧ c = e) ∨ (b = e ∧ c = d) := by
  decide

theorem TwoPeriodicLetters.collapse {g : Fin 3 → Fin 3} (hg : TwoPeriodicLetters g)
    {b c : Fin 3} (hbc : b ≠ c) (hmerge : g^[2] b = g^[2] c) : g b = g c := by
  obtain ⟨p, q, hpq, hp, hq⟩ := hg
  exact collapse_at_first_step g p q b c hpq hp hq hbc hmerge

/-- Without two periodic letters every pair merges: the hypothesis is not decorative. -/
theorem constant_map_merges_all : ∀ b c : Fin 3, (fun _ : Fin 3 => (0 : Fin 3))^[2] b =
    (fun _ : Fin 3 => (0 : Fin 3))^[2] c := by
  decide

/-- The domain hypothesis does not force a non-identified two-step merge to be absent:
`g = (0,1,1)` has two periodic letters and collapses exactly `{1,2}`. -/
theorem collapsed_pair_example :
    TwoPeriodicLetters ![0, 1, 1] ∧ (![0, 1, 1] : Fin 3 → Fin 3) 1 = ![0, 1, 1] 2 := by
  refine ⟨⟨0, 1, by decide, by decide, by decide⟩, by decide⟩

/-! ## Local geometry of vertices -/

section Geometry

variable {X Y α : Type*} {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : α → α}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt StartsAt : X → ℝ → α → Prop}

/-- A vertex at the physical origin. -/
def VertexAtOrigin (EndsAt : X → ℝ → α → Prop) (S : X) : Prop := ∃ b, EndsAt S 0 b

/-- Local laws for the vertex argument.  `periodic_ray` is the statement that two
periodic tilings starting with the same tile at the origin share the substituted ray
of that tile; it is primitive local geometry of inflation-fixed tiles. -/
structure VertexLaws (f : X → X) (AgreeRight : X → X → ℝ → Prop)
    (EndsAt StartsAt : X → ℝ → α → Prop) : Prop where
  agree_symm : ∀ {S U y}, AgreeRight S U y → AgreeRight U S y
  start_of_end : ∀ {S y b}, EndsAt S y b → ∃ a, StartsAt S y a
  periodic_ray : ∀ {S U a}, S ∈ periodicPts f → U ∈ periodicPts f →
    StartsAt S 0 a → StartsAt U 0 a → AgreeRight S U 0

/-- A first branch point exists for distinct asymptotic tilings (the infimum of the
agreement locations, round-4 Lemma A).  Local contract. -/
def BranchExistence (AgreeRight : X → X → ℝ → Prop) (EndsAt : X → ℝ → α → Prop) : Prop :=
  ∀ {S U}, S ≠ U → RightAsymptotic AgreeRight S U → ∃ y b c, BranchAt AgreeRight EndsAt S U y b c

/-- (E1): asymptotic tilings lie in one fibre.  Named written input. -/
def AsymptoticSameFibre (h : X → Y) (AgreeRight : X → X → ℝ → Prop) : Prop :=
  ∀ {S U}, RightAsymptotic AgreeRight S U → h S = h U

/-- (NM_V), right side: a member of the distinguished fibre right-asymptotic to a
vertex-type member is vertex-type with the same right letter.  Named hypothesis. -/
def NMVRight (h : X → Y) (q₀ : Y) (AgreeRight : X → X → ℝ → Prop)
    (EndsAt StartsAt : X → ℝ → α → Prop) : Prop :=
  ∀ {S U}, h S = q₀ → h U = q₀ → RightAsymptotic AgreeRight U S → VertexAtOrigin EndsAt S →
    VertexAtOrigin EndsAt U ∧ ∀ a, StartsAt S 0 a → StartsAt U 0 a

theorem pairPeriodic_swap {S U : X} (hp : PairPeriodic f S U) : PairPeriodic f U S := by
  obtain ⟨n, hn, hS, hU⟩ := hp
  exact ⟨n, hn, hU, hS⟩

theorem branch_swap (V : VertexLaws f AgreeRight EndsAt StartsAt) {S U : X} {y : ℝ}
    {b c : α} (hb : BranchAt AgreeRight EndsAt S U y b c) :
    BranchAt AgreeRight EndsAt U S y c b :=
  ⟨V.agree_symm hb.1, hb.2.2.1, hb.2.1, hb.2.2.2.symm⟩

/-- Round-4 Lemma A, location part: the branch of a periodic pair is not left of the
inflation centre. -/
theorem branch_nonneg_of_pairPeriodic
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    {S U : X} {y : ℝ} {b c : α} (hp : PairPeriodic f S U)
    (hb : BranchAt AgreeRight EndsAt S U y b c) : 0 ≤ y := by
  obtain ⟨n, hn, hSn, hUn⟩ := hp
  by_contra hnonneg
  have hneg : y < 0 := not_le.mp hnonneg
  have hagree := laws.agree_iterate n hb.1
  rw [hSn, hUn] at hagree
  have hpow : 1 < β ^ n := one_lt_pow₀ hβ (Nat.ne_of_gt hn)
  have hlt : β ^ n * y < y := by simpa using mul_lt_mul_of_neg_right hpow hneg
  exact hb.2.2.2 (laws.agree_endpoint hagree hlt hb.2.1 hb.2.2.1)

/-- Persistent branch letters put the branch of a periodic pair at the origin. -/
theorem branch_eq_zero_of_persistent
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt) (hβ : 1 < β)
    {S U : X} {y : ℝ} {b c : α} (hp : PairPeriodic f S U)
    (hb : BranchAt AgreeRight EndsAt S U y b c) (hpersist : ∀ n : ℕ, g^[n] b ≠ g^[n] c) :
    y = 0 := by
  obtain ⟨n, hn, hSn, hUn⟩ := hp
  have hit := laws.branch_iterate n hb (hpersist n)
  rw [hSn, hUn] at hit
  exact expanding_fixed_location_eq_zero hβ hn (laws.branch_unique hb hit)

/-- **Vertex leaves branch at the origin.**  Under R4, E1 and (NM_V), a periodic
asymptotic pair with a vertex-type leaf has its branch at the origin. -/
theorem branch_eq_zero_of_vertex_leaf
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    (V : VertexLaws f AgreeRight EndsAt StartsAt) (hβ : 1 < β)
    {h : X → Y} {q₀ : Y} (hR4 : R4ZeroFibre f h q₀ EndsAt)
    (hE1 : AsymptoticSameFibre h AgreeRight) (hNMV : NMVRight h q₀ AgreeRight EndsAt StartsAt)
    {S U : X} {y : ℝ} {b c : α} (hp : PairPeriodic f S U)
    (hb : BranchAt AgreeRight EndsAt S U y b c) (hv : VertexAtOrigin EndsAt S) : y = 0 := by
  have hy := branch_nonneg_of_pairPeriodic laws hβ hp hb
  obtain ⟨d, hd⟩ := hv
  have hS : h S = q₀ := hR4 hp.mem_left hd
  have hU : h U = q₀ := (hE1 ⟨y, hb.1⟩).symm.trans hS
  obtain ⟨-, hstart⟩ := hNMV hS hU ⟨y, V.agree_symm hb.1⟩ ⟨d, hd⟩
  obtain ⟨a, ha⟩ := V.start_of_end hd
  have hray := V.periodic_ray hp.mem_left hp.mem_right ha (hstart a ha)
  rcases hy.lt_or_eq with hpos | hzero
  · exact (hb.2.2.2 (laws.agree_endpoint hray hpos hb.2.1 hb.2.2.1)).elim
  · exact hzero.symm

/-- **Merging leaves are interior.**  If the branch letters of a periodic pair merge at
some level, its branch is strictly right of the origin and, under (NM_V), neither leaf
has a vertex at the origin. -/
theorem interior_leaves_of_merge
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    (V : VertexLaws f AgreeRight EndsAt StartsAt) (hβ : 1 < β)
    {h : X → Y} {q₀ : Y} (hR4 : R4ZeroFibre f h q₀ EndsAt)
    (hE1 : AsymptoticSameFibre h AgreeRight) (hNMV : NMVRight h q₀ AgreeRight EndsAt StartsAt)
    {S U : X} {y : ℝ} {b c : α} (hp : PairPeriodic f S U)
    (hb : BranchAt AgreeRight EndsAt S U y b c) (hmerge : ∃ n : ℕ, g^[n] b = g^[n] c) :
    0 < y ∧ ¬ VertexAtOrigin EndsAt S ∧ ¬ VertexAtOrigin EndsAt U := by
  have hne : y ≠ 0 := by
    rintro rfl
    obtain ⟨n, hn⟩ := hmerge
    exact endpoint_persistent_of_pairPeriodic laws hb hp n hn
  refine ⟨lt_of_le_of_ne (branch_nonneg_of_pairPeriodic laws hβ hp hb) (Ne.symm hne), ?_, ?_⟩
  · exact fun hv => hne (branch_eq_zero_of_vertex_leaf laws V hβ hR4 hE1 hNMV hp hb hv)
  · have hE1' : AsymptoticSameFibre h AgreeRight := hE1
    exact fun hv => hne (branch_eq_zero_of_vertex_leaf laws V hβ hR4 hE1' hNMV
      (pairPeriodic_swap hp) (branch_swap V hb) hv)

end Geometry

/-! ## Theorem S -/

section TheoremS

variable {X Y : Type*} {f : X → X} {translate : ℝ → X → X} {β : ℝ} {g : Fin 3 → Fin 3}
    {AgreeRight : X → X → ℝ → Prop} {EndsAt StartsAt : X → ℝ → Fin 3 → Prop}

/-- **Theorem S.**  Every same-fibre triple with distinct right-asymptotic leaves has a
common translate that is periodic, keeps both links, and falls into exactly one of:

* (A) branch at the origin, two-step test passed, all three in the distinguished
  fibre, both leaves ending a tile at the origin;
* (B) branch strictly right of the origin, branch letters identified by `g` itself (the
  collapsed pair), neither leaf with a vertex at the origin.

The two cases are exclusive by the two-step test.  Case (B) is not excluded here. -/
theorem selection_dichotomy
    (laws : RightBranchLaws f translate β g AgreeRight EndsAt)
    (V : VertexLaws f AgreeRight EndsAt StartsAt) (hβ : 1 < β)
    (hBranch : BranchExistence AgreeRight EndsAt)
    (hBDS : BDSPeriodicization f translate (RightAsymptotic AgreeRight))
    (A : Y → Y) (h : X → Y) (q₀ : Y) (Z : X → X → Prop)
    (hf : Injective f) (hsem : Semiconj h f A)
    (hfinite : ∀ q, {x | h x = q}.Finite)
    (htranslate : ∀ t, Injective (translate t))
    (hZtranslate : ∀ t {x y}, Z x y → Z (translate t x) (translate t y))
    (hZfibre : ∀ {x y}, Z x y → h x = h y) (hZne : ∀ {x y}, Z x y → x ≠ y)
    (hR4 : R4ZeroFibre f h q₀ EndsAt) (hE1 : AsymptoticSameFibre h AgreeRight)
    (hNMV : NMVRight h q₀ AgreeRight EndsAt StartsAt) (hTwo : TwoPeriodicLetters g)
    {T S U : X} (hTS : Z T S) (hTU : Z T U) (hSU : S ≠ U)
    (hAsym : RightAsymptotic AgreeRight S U) :
    ∃ t n, 0 < n ∧
      Z (translate t T) (translate t S) ∧ Z (translate t T) (translate t U) ∧
      f^[n] (translate t T) = translate t T ∧ f^[n] (translate t S) = translate t S ∧
      f^[n] (translate t U) = translate t U ∧
      ∃ y b c, BranchAt AgreeRight EndsAt (translate t S) (translate t U) y b c ∧
        ((y = 0 ∧ g^[2] b ≠ g^[2] c ∧ h (translate t T) = q₀ ∧
            h (translate t S) = q₀ ∧ h (translate t U) = q₀) ∨
         (0 < y ∧ g^[2] b = g^[2] c ∧ g b = g c ∧
            ¬ VertexAtOrigin EndsAt (translate t S) ∧
            ¬ VertexAtOrigin EndsAt (translate t U))) := by
  have hAsymT : ∀ t {x y}, RightAsymptotic AgreeRight x y →
      RightAsymptotic AgreeRight (translate t x) (translate t y) := by
    rintro t x y ⟨r, hr⟩
    exact ⟨r - t, laws.agree_translate t hr⟩
  obtain ⟨t, n, q, hn, hTS', hTU', hTn, hSn, hUn, -, -, -, -, -, -, hSU', hAsym'⟩ :=
    periodic_triple_of_asymptotic_partners f A h translate Z (RightAsymptotic AgreeRight)
      hf hsem hfinite htranslate hZtranslate hAsymT hZfibre hZne hBDS hTS hTU hSU hAsym
  have hp : PairPeriodic f (translate t S) (translate t U) := ⟨n, hn, hSn, hUn⟩
  obtain ⟨y, b, c, hb⟩ := hBranch hSU' hAsym'
  refine ⟨t, n, hn, hTS', hTU', hTn, hSn, hUn, y, b, c, hb, ?_⟩
  by_cases hmerge : g^[2] b = g^[2] c
  · obtain ⟨hy, hS, hU⟩ :=
      interior_leaves_of_merge laws V hβ hR4 hE1 hNMV hp hb ⟨2, hmerge⟩
    exact Or.inr ⟨hy, hmerge, hTwo.collapse hb.2.2.2 hmerge, hS, hU⟩
  · have hpersist : ∀ k : ℕ, g^[k] b ≠ g^[k] c :=
      (Psc.PeriodicPartner.endpoint_persistent_iff g b c).mpr hmerge
    have hy := branch_eq_zero_of_persistent laws hβ hp hb hpersist
    subst hy
    have hS : h (translate t S) = q₀ := hR4 hp.mem_left hb.2.1
    have hU : h (translate t U) = q₀ := hR4 hp.mem_right hb.2.2.1
    exact Or.inl ⟨rfl, hmerge, (hZfibre hTS').trans hS, hS, hU⟩

end TheoremS

end Psc.PeriodicPartnerSelection

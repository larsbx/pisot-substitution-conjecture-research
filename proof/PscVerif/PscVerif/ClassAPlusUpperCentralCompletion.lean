/-
# Literal central-source completion in the upper plus-Class-A chamber

A full integral central packet supplies an actual central RUN orbit. The
finite integer-pair recurrence yields an alternating tail; reconstruction
is used at depth N+1 before the signed literal cycle exits are applied.
The resulting ordered path preserves both original tracks and all offset
coordinates. General strict-source completion concatenates the entry path
at its identical full central endpoint, keeping the entry and central
length bounds separate. This result has only the documented upper chamber
scope and is not a universal BH theorem.
-/
import PscVerif.ClassAPlusUpperCentralOrbit
import PscVerif.ClassAPlusUpperCentralBound
import PscVerif.ClassAPlusUpperEntryBound
import PscVerif.ClassAPlusUpperCycleCompletion

namespace Psc.ClassAPlusUpperCentralCompletion

open Psc.Binomial Psc.Incidence Psc.OccurrenceNewborn Psc.OccurrenceTransport
open Psc.ClassAZeroDefectEscape Psc.ClassAMinusPrefixAssembly
open Psc.ClassAPlusUpperCycles Psc.ClassAPlusUpperCycleCompletion
open Psc.ClassAPlusUpperRecurrence Psc.ClassAPlusUpperLiteralEntry
open Psc.ClassAPlusUpperEntryTransport Psc.ClassAPlusUpperEntryBound
open Psc.ClassAPlusUpperCentralOrbit Psc.ClassAPlusUpperCentralBound Matrix

/-- The central bound depends on the actual first two scalar coordinates.
The next first coordinate is independent of the selected RUN gap. -/
def centralBound (n : ℕ) (source : Packet) : ℕ :=
  pairCount n (-source.delta 0)
    (2*(-source.delta 0)+(-source.delta 1)+(-source.delta 2)) + 2*n - 1

/-- The recurrence amplitude lies within the already checked literal exit
range. This uses the strict root bracket and n>=7 before rounding to integers. -/
theorem amplitude_exit_range {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (H : ℤ) (hH : 0 ≤ H) (hamp : V n β*(H : ℝ) < 1/2) :
    J*H.toNat ≤ n-1 := by
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hp.n_lower
  have hden : 0 < β+1 := by linarith [hp.beta_pos]
  rw [hp.reserve_identity, div_mul_eq_mul_div] at hamp
  have hm := (div_lt_iff₀ hden).1 hamp
  have hprod : (J : ℝ)*(H : ℝ) < n := by nlinarith [hp.root_upper]
  have hHreal : (H.toNat : ℝ)=(H : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hH
  have hcast : ((J*H.toNat : ℕ) : ℝ) < (n : ℝ) := by
    simpa only [Nat.cast_mul, hHreal] using hprod
  have hnat : J*H.toNat < n := by exact_mod_cast hcast
  omega

/-- A full signed W-packet, not only its first coordinate, is identified
with the exact existing cycle-exit source. -/
theorem signed_packet_of_abs (h : ℤ) (H : ℕ) (ha : |h|=(H : ℤ)) :
    ∃ reversed : Bool, packet 2 2 h (3*h) (-6*h)=signedSource reversed H := by
  by_cases hh : 0 ≤ h
  · have he : h=(H : ℤ) := by simpa only [abs_of_nonneg hh] using ha
    exact ⟨false, by simp [signedSource, cyclePacket, he]⟩
  · have he : h=-(H : ℤ) := by rw [abs_of_neg (lt_of_not_ge hh)] at ha; omega
    refine ⟨true, ?_⟩
    simp [signedSource, cyclePacket, ClassAMinusConstantRecurrence.packet_swap, he]

/-- Both complete original marked prefixes realize typed zero. -/
def ZeroOriginalTraces (s : Fin 3 → Word) (source : Packet)
    (xs : List (ℕ × ℕ)) : Prop :=
  ∃ (top : Mark ((subst s)^[xs.length] [source.top]))
    (bottom : Mark ((subst s)^[xs.length] [source.bottom])),
    MarkTrace s source.top (xs.map Prod.fst) top.before top.letter top.after ∧
    MarkTrace s source.bottom (xs.map Prod.snd) bottom.before bottom.letter bottom.after ∧
    top.letter=2 ∧ bottom.letter=2 ∧
    incidenceZ s^xs.length *ᵥ (-source.delta)=parikhZ top.before-parikhZ bottom.before

def Completion (s : Fin 3 → Word) (ℓ : Fin 3 → ℝ)
    (source : Packet) (xs : List (ℕ × ℕ)) : Prop :=
  OrderedInteriorPath s ℓ source xs zeroPacket ∧
  OriginalTraces s source xs zeroPacket ∧ ZeroOriginalTraces s source xs

theorem completion_of_interior {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {source : Packet} {xs : List (ℕ × ℕ)}
    (hpath : OrderedInteriorPath s ℓ source xs zeroPacket) : Completion s ℓ source xs := by
  refine ⟨hpath, original_traces_of_ordered hpath.orderedPath, ?_⟩
  have hz : zeroPacket.delta=0 := by funext a; fin_cases a <;> rfl
  exact ordered_path_traced_zero_original_prefixes hpath.orderedPath hz

/-- Strict concatenation requires the identical complete middle packet. -/
theorem interior_path_trans {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {source middle target : Packet} {xs ys : List (ℕ × ℕ)}
    (hx : OrderedInteriorPath s ℓ source xs middle)
    (hy : OrderedInteriorPath s ℓ middle ys target) :
    OrderedInteriorPath s ℓ source (xs++ys) target := by
  induction hy with
  | nil => simpa using hx
  | snoc _ i j he hi ih =>
    simpa only [List.append_assoc] using OrderedInteriorPath.snoc ih i j he hi

theorem completion_concat {s : Fin 3 → Word} {ℓ : Fin 3 → ℝ}
    {source middle : Packet} {entry suffix : List (ℕ × ℕ)}
    (he : OrderedInteriorPath s ℓ source entry middle)
    (hc : Completion s ℓ middle suffix) : Completion s ℓ source (entry++suffix) :=
  completion_of_interior (interior_path_trans he hc.1)

/-- Reconstruction happens at depth N+1. Only after that full-packet
identity is established is the existing signed literal cycle path appended. -/
theorem completion_from_tail {n J : ℕ} {β : ℝ} (hp : Family n J β)
    {source : Packet} (orbit : CentralOrbit n J β source) (N : ℕ) (H : ℤ)
    (hH : 0 ≤ H) (hamp : V n β*(H : ℝ) < 1/2)
    (habs : ∀ m, |orbit.u (N+m)|=H)
    (halt : ∀ m, orbit.u (N+m+1) = -orbit.u (N+m)) :
    ∃ reversed : Bool,
      orbit.w (N+1)=signedSource reversed H.toNat ∧ J*H.toNat ≤ n-1 ∧
      Completion (upperSigma n J) (lengths n β) source
        (prefixIndices orbit (N+1) ++ allSignedIndices reversed n J H.toNat) := by
  have hshape : orbit.w (N+1)=
      packet 2 2 (orbit.u (N+1)) (3*orbit.u (N+1)) (-6*orbit.u (N+1)) := by
    simpa only [Nat.add_zero] using reconstruction_delay orbit.u orbit.w N
      orbit.reconstruction halt 0
  have habs' : |orbit.u (N+1)|=(H.toNat : ℤ) := by
    rw [Int.toNat_of_nonneg hH]
    exact habs 1
  obtain ⟨reversed, hsigned⟩ := signed_packet_of_abs (orbit.u (N+1)) H.toNat habs'
  have hfull := hshape.trans hsigned
  have hrange := amplitude_exit_range hp H hH hamp
  have hprefix : OrderedPath (upperSigma n J) source (prefixIndices orbit (N+1))
      (signedSource reversed H.toNat) := by
    simpa only [hfull] using orbit_prefix_path orbit (N+1)
  have hcycle := all_signed_ordered_paths n J H.toNat hp.n_lower hp.J_lower hp.J_upper
    hrange reversed
  have hpath := hprefix.trans hcycle
  refine ⟨reversed, hfull, hrange, completion_of_interior ?_⟩
  exact ordered_path_indexed_interior _ _ β (lengths_pos hp) hp.beta_pos
    (literal_scaling hp) hpath (zero_packet_interior (lengths n β) (lengths_pos hp) 2 2)

/-- Every literal central source reaches typed zero. The bound comes from
the finite pair carrier plus the actual signed cycle-exit transcript. -/
theorem central_completion {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hc : Central n β source) :
    ∃ xs : List (ℕ × ℕ), xs.length ≤ centralBound n source ∧
      Completion (upperSigma n J) (lengths n β) source xs := by
  let orbit := central_orbit hp source hc
  obtain ⟨N, H, hN, hH, hamp, habs, halt⟩ := bounded_alternating_tail n J β hp orbit.u
    orbit.recurrence
  obtain ⟨reversed, _, hrange, hcompletion⟩ := completion_from_tail hp orbit N H hH hamp habs halt
  refine ⟨prefixIndices orbit (N+1) ++ allSignedIndices reversed n J H.toNat, ?_, hcompletion⟩
  have hlen := signed_indices_length_le reversed n J H.toNat
  have hHnat : H.toNat ≤ n-1 := by
    have hm := Nat.mul_le_mul_right H.toNat hp.J_lower
    simp only [one_mul] at hm
    omega
  have hu0 : orbit.u 0 = -source.delta 0 := by
    rw [orbit.coordinate, orbit.initial]
  have hu1 : orbit.u 1 = 2*(-source.delta 0)+(-source.delta 1)+(-source.delta 2) := by
    simpa only [orbit.initial] using orbit.next_coordinate 0
  rw [List.length_append, prefixIndices_length]
  rw [hu0, hu1] at hN
  unfold centralBound
  have hn := hp.n_lower
  omega

/-- Integral cubic offsets exclude both boundary values of the closed
half-unit central interval, so the written closed formulation has the
same literal completion and bound. -/
theorem central_completion_closed {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (ht : source.top=2) (hb : source.bottom=2)
    (hc : |shift n β source| ≤ 1/2) :
    ∃ xs : List (ℕ × ℕ), xs.length ≤ centralBound n source ∧
      Completion (upperSigma n J) (lengths n β) source xs := by
  have hne : |shift n β source| ≠ 1/2 := by
    intro he
    by_cases hsign : 0 ≤ shift n β source
    · have hh := shift_no_half hp source 0
      norm_num only [Int.cast_zero, zero_add] at hh
      exact hh (by simpa only [abs_of_nonneg hsign] using he)
    · have hh := shift_no_half hp source (-1)
      norm_num only [Int.cast_neg, Int.cast_one] at hh
      rw [abs_of_neg (lt_of_not_ge hsign)] at he
      apply hh
      linarith
  exact central_completion hp source ⟨ht, hb, lt_of_le_of_ne hc hne⟩

/-- Typed zero may stop immediately; no substitution or frame operation is
required to justify its empty completion transcript. -/
theorem zero_empty_completion {n J : ℕ} {β : ℝ} (hp : Family n J β) :
    Completion (upperSigma n J) (lengths n β) zeroPacket [] :=
  completion_of_interior (.nil zeroPacket
    (zero_packet_interior (lengths n β) (lengths_pos hp) 2 2))

/-- Entry and central completion keep their separate budgets and meet at
one identical full integral packet. Full original prefixes are recomposed
for the concatenation, not borrowed from the central suffix. -/
theorem all_source_completion {n J : ℕ} {β : ℝ} (hp : Family n J β)
    (source : Packet) (hi : source.Interior (lengths n β)) :
    ∃ (entry : List (ℕ × ℕ)) (middle : Packet) (suffix : List (ℕ × ℕ)),
      entry.length ≤ leastEntryPower hp source hi + 1 ∧ Central n β middle ∧
      OrderedInteriorPath (upperSigma n J) (lengths n β) source entry middle ∧
      OriginalTraces (upperSigma n J) source entry middle ∧
      suffix.length ≤ centralBound n middle ∧
      Completion (upperSigma n J) (lengths n β) middle suffix ∧
      Completion (upperSigma n J) (lengths n β) source (entry++suffix) := by
  obtain ⟨entry, middle, hlen, hc, he, ht⟩ := all_source_entry hp source hi
  obtain ⟨suffix, hslen, hs⟩ := central_completion hp middle hc
  exact ⟨entry, middle, suffix, hlen, hc, he, ht, hslen, hs, completion_concat he hs⟩

/-- Literal n,d endpoint with a proved least-power entry bound and a
separate finite-carrier central bound. -/
theorem all_source_completion_nd (n d : ℕ) (β : ℝ) (hn : 7 ≤ n)
    (hdlo : n+5 ≤ d) (hdhi : d ≤ 2*n+11)
    (hlo : (n : ℝ)+4 < β) (hhi : β < (n : ℝ)+6)
    (hroot : β^3-((n : ℝ)+4)*β^2+((n : ℝ)+5-(d : ℝ))*β-2=0)
    (source : Packet) (hi : source.Interior (lengths n β)) :
    ∃ (k : ℕ) (entry : List (ℕ × ℕ)) (middle : Packet) (suffix : List (ℕ × ℕ)),
      4 ≤ β^k*sourceMargin n β source ∧
      (∀ j < k, β^j*sourceMargin n β source < 4) ∧
      entry.length ≤ k+1 ∧ Central n β middle ∧
      OrderedInteriorPath (plusSigma n d) (lengths n β) source entry middle ∧
      OriginalTraces (plusSigma n d) source entry middle ∧
      suffix.length ≤ centralBound n middle ∧
      Completion (plusSigma n d) (lengths n β) middle suffix ∧
      Completion (plusSigma n d) (lengths n β) source (entry++suffix) := by
  have hp := family_of_nd n d β hn hdlo hdhi hlo hhi hroot
  obtain ⟨hk, hmin⟩ := least_entry_power_spec hp source hi
  obtain ⟨entry, middle, suffix, he, hc, hep, het, hs, hsc, hall⟩ := all_source_completion hp source hi
  refine ⟨leastEntryPower hp source hi, entry, middle, suffix, hk, hmin, he, hc, ?_, ?_, hs, ?_, ?_⟩
  · simpa only [upper_sigma_original n d (by omega)] using hep
  · simpa only [upper_sigma_original n d (by omega)] using het
  · simpa only [upper_sigma_original n d (by omega)] using hsc
  · simpa only [upper_sigma_original n d (by omega)] using hall

/-- Every upper-chamber parameter pair admits positive literal eigenlengths
and complete strict-source coincidence paths. No external root-existence,
finite-carrier, terminal-height or zero-hit hypothesis is supplied. -/
theorem exists_root_all_source_completion (n d : ℕ) (hn : 7 ≤ n)
    (hdlo : n+5 ≤ d) (hdhi : d ≤ 2*n+11) :
    ∃ β : ℝ, (n : ℝ)+4 < β ∧ β < (n : ℝ)+6 ∧
      β^3-((n : ℝ)+4)*β^2+((n : ℝ)+5-(d : ℝ))*β-2=0 ∧
      (∀ a, 0 < lengths n β a) ∧
      (∀ a, physicalLength (lengths n β) (plusSigma n d a)=β*lengths n β a) ∧
      ∀ source : Packet, source.Interior (lengths n β) →
        ∃ (k : ℕ) (entry : List (ℕ × ℕ)) (middle : Packet) (suffix : List (ℕ × ℕ)),
          4 ≤ β^k*sourceMargin n β source ∧
          (∀ j < k, β^j*sourceMargin n β source < 4) ∧
          entry.length ≤ k+1 ∧ Central n β middle ∧
          OrderedInteriorPath (plusSigma n d) (lengths n β) source entry middle ∧
          OriginalTraces (plusSigma n d) source entry middle ∧
          suffix.length ≤ centralBound n middle ∧
          Completion (plusSigma n d) (lengths n β) middle suffix ∧
          Completion (plusSigma n d) (lengths n β) source (entry++suffix) := by
  obtain ⟨β, hp⟩ := ClassAPlusUpperNoHalfTies.family_root_exists n (2*n+12-d) hn (by omega) (by omega)
  have hroot : β^3-((n : ℝ)+4)*β^2+((n : ℝ)+5-(d : ℝ))*β-2=0 := by
    have hh := hp.root_eq
    rw [Nat.cast_sub (show d ≤ 2*n+12 by omega)] at hh
    push_cast at hh
    nlinarith [hh]
  refine ⟨β, hp.root_lower, hp.root_upper, hroot, lengths_pos hp, ?_, ?_⟩
  · intro a
    simpa only [upper_sigma_original n d (by omega)] using literal_scaling hp a
  · intro source hi
    exact all_source_completion_nd n d β hn hdlo hdhi hp.root_lower hp.root_upper hroot source hi

end Psc.ClassAPlusUpperCentralCompletion

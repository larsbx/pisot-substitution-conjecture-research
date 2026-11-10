/-
# Controls of the packet square

The controls of the packet square (roadmap immediate-sequence item 2;
`docs/packet-square-stop-go-2026-11-10.md`; `README.llm.txt`, 2026-11-09 addendum "P0 OCCURRENCE
REFINEMENT"), stated on the four committed `packet-square-v1` tables
`PscVerif.PacketSquareData.{Tribonacci, RealSecondary, NonPisot, GfActual}` (emitted by
`kernel/psc/packet_square_export.mojo`; each data module carries its own receipt
`accepted : table.check = true`) and read through the composite of `Psc.PacketSquare`.  Every
refusal of a concrete table below evaluates, by one `decide +kernel`, the clause vector
`Table.clauses` of a mutated copy of a committed table (or of a committed table extended by
synthetic rows), so the refusing clause is part of the statement, and derives
`Table.check = false` from it (`Table.check_eq_clauses`).  The refusals of every table of a
kind (`gf_template_refused`, `gf_template_states_refused`, the `∀ ko` conjuncts of
`np_side_swapped`, `np_duplicate_isolated` and `fib_side_swapped_collision`, the `∀ b`
conjunct of `rs_forged_refused`) are proved from the definitions of the clauses through the
generic helpers below.  Every statement about absolute occurrences is assembled from results
of `Psc.PacketSquare` (the square on the declared universe, its readings, its path lifting),
`Psc.PacketCertificate` and `Psc.OccurrenceRealisation`; the row facts it needs, and the
absolute steps and anchors replayed by `trib_lineage` (`absStep` and the `Anchor` fields over
the iterates of `(01, 10)`), are evaluated by `decide +kernel`.

## Layers

A control is filed under the first layer at which it stops being evidence for the tempting
conclusion.  The exporter's layers (input validation, the recorded PIP field, the caps of the
balanced-pair closure) are not read here.  **L3** the literal ordered factorisation
(`factorsOK`); **L4** the carried row fields (`packetOK`); **L5** the full child star
(`starOK`); **L6** identity and reachability (`keysOK`, `rootsOK`, `birthOK`); **L7** the hub
bits (`hubsOK`); **L8** graph logic (what a transfer gives and what it does not); **L9**
premises outside the square (the Pisot hypothesis; strict child-closed support).

## The controls

1. **Tribonacci `01/02/0`** (positive control; `Tribonacci.accepted`).  `trib_shape`: 6
   states, 12 factor rows, 132 rows, 37 root rows, 185 listed edges, 194 split entries; target
   `none`; no row has its `success` bit; 38 rows over a noncoincident state and 9 rows over a
   coincidence state have no child entry.  `trib_universe_no_success` (success-target transfer,
   `packet_square_readings_for`): for every noncoincident listed state, no element of its
   universe is productive for the packet-success target.  `trib_inevitable_ne_inevMax`,
   `trib_universe_inevitable_ne_inevMax` (L8): row 6 is a noncoincident dead end of `t.graph`,
   row 37 a coincidence that is a dead end of `t.graphSuccess`; at each, and at every element
   of a universe whose packet it is (`deadEnd_up` along `packet_square`), (A) holds vacuously
   and (A⁺) fails, so the two readings differ for both targets.  `trib_lineage` (positive
   control for ρ and the composite): the absolute lineage `(0,0,0) → (1,1,1) → (2,2,2)` of the
   seed `(01, 10)`, replayed by `absStep` and `occStep`, is retained, lies in the declared
   universe and has the packets `0 → 38 → 57`, ending at a coincidence born as a first child
   (boundary, not strictly interior); the root element is productive for the coincidence target
   and not for the success target, and so is its packet.
2. **The packet cycle `209 -(0,0)-> 429 -(0,2)-> 209` of `1/02/202`** (`RealSecondary.accepted`,
   `rs_shape`).  `rs_cycle_rows`, `rs_cycle_literal`: the two rows decode to the calibration
   pairs `x209`, `x429` of `Psc.OccurrenceGraph`, form a 2-cycle of the packet graph and of
   `occGraph rsSubst`, and their stars, addresses, letters and residuals are the literal ones
   (`Table.check_sound`), with the values of `rs_rows_stars` and `rs_rows_fields`.
   `rs_cycle_packets`, `rs_cycle_realised` (L8): the packet of `rsU3` (the element over
   `(3, 4, 4)` in the iterates of the seed `(01, 10)`, `rs_cycle_lineage`) is row 209; at every
   element of every universe whose packet is row 209 the cycle lifts to an infinite path of the
   universe graph whose level rises by one per step (`packet_path_lift`), and no cycle of the
   universe graph passes there (`universe_acyclic`): the cycle is realised by an infinite
   absolute lineage and never by an absolute cycle.  `rs_support_not_strict` (L9): the
   balanced-pair states 7 and 8, and `rsState8.swap` (the orientation row 209 reads), lie in
   no strict closed set of `bpaGraph rsSubst` (state 8 has the coincidence child `(2, 2)` in
   both orientations, and state 7 has the child `rsState8.swap`).
3. **Non-Pisot `1/012/1`** (`NonPisot.accepted`).  `np_incidence_eigen` (L9): the incidence
   matrix has the integer eigenvectors `(1,2,1)`, `(1,-1,1)`, `(1,0,-1)` with eigenvalues
   `2`, `-1`, `0`, so its characteristic polynomial `x³ - x² - 2x` is reducible and has the root
   `-1` of modulus one.  `np_rows`, `np_square_blind`: the headline square applies with no
   further hypothesis; the root element of the universe of `(02, 20)` at `(1, 1)` has packet row
   7, which reaches the only success row 21, and it is productive for the success target and
   for the coincidence target (`packet_square_readings_for`, `packet_square_readings`).  The
   square does not read the spectrum; this specimen is rejected only at the Pisot hypothesis.
4. **The strong G/F template of `1/2/021`** (L3).  `gf_actual_shape`: the actual closure
   (`GfActual.accepted`).  `gf_template_literal`: the three template states `(021, 120)`,
   `(10122, 20121)`, `(011202221, 201221102)` are irreducible blocks in normalised orientation,
   and the literal ordered factorisations of their images have `1`, `2`, `5` blocks (the
   template proposes `1`, `1`, `3` children), the first with the block `(10212, 20211)` (the
   template names `(10122, 20121)`), the third with the diagonal block `(2, 2)`.
   `gf_template_refused`: every table over `1/2/021` that lists the second (third) template
   state with a number of factor rows other than `2` (`5`) is refused by `factorsOK`
   (`factorsOK_eq_false_of_length`).  `gfTemplate`, the committed table extended by the
   template states and the template's factor rows: `gf_template_states_refused`, each template
   state alone makes `factorsOK` refuse (`factorsOK_eq_false_of_ne`; the first on content, the
   other two on count); `gf_template_table_refused`, its clause vector: the factor clause, and
   the root clause because no root row was written for the template states.  A concrete table
   that lists the template states with root rows, and keeps the template's factor rows as their
   only factor rows, cannot pass the star clause (see `gf_template_table_refused`), so the
   isolated L3 refusal is the general `gf_template_refused` / `gf_template_states_refused`.
5. **The seed `(01, 10)` of `1/02/202` at depth two** (L4).  `rs_seed_rows`,
   `rs_depth_one_no_success`: no retained child of a level-0 element of the universe of the seed
   is a packet success (success-target transfer along `packet_square`).
   `rs_depth_two_success`: the root element at `(1, 0)` has packet row 2, the packet path
   `2 -(1,1)-> 124 -(0,2)-> 346` ends at a success, and the root element is productive for the
   success target.  `rs_matching_letters_refused`: row 154 carries the matching letters `(2, 2)`
   at the residual `(-1, 1, 0)` and is not a success; with its `success` bit set the table is
   refused by the row clause only.
6. **Mutation controls replayed on exported tables**, each with its full clause vector.  Each
   replays the recipe of a Fibonacci control of `Psc.PacketCertificate` (named in its docstring) on
   a table emitted by the Mojo exporter over the three-letter alphabet, where `fibTable` is a
   hand-written `Fin 2` table.  They add that the refusing clauses are the same on exporter output,
   and, for the side swap, the duplicate and the forged row, that the refusal holds for every key
   order or every birth record.  On `1/012/1`: `np_dropped_split` (a dropped split entry: the star
   clause only, L5; `fib_dropped_split`), `np_side_swapped` (L4, L5, L6; `fib_side_swapped`): the
   swapped row gets the key of row 30, which no key order repairs, the row clause refuses its
   letters only, and the star equation fails at rows 0, 12, 22 and 30; `np_hub_coerced` (a coerced
   undefined hub bit: the hub clause only, L7; `fib_hub_coerced`), `np_duplicate_isolated`,
   `np_duplicate_not_injective` (a duplicated row refused by the key clause alone, L6, without which
   `occAt` is not injective; `fib_duplicate_isolated`, `fib_duplicate_not_injective`),
   `np_wrong_global` (a wrong global position: the row clause only, L4; `fib_wrong_global`).  On
   `1/02/202`: `rs_forged_outside`, `rs_forged_not_reached`, `rs_forged_refused` (L6;
   `fibExtra_forged_outside`, `fibExtra_forged_not_reached`, `fibExtra_forged_unreachable`): the
   mirror of the success row 147 decodes to a valid coincidence pair born as ordinal 1 of the
   swapped seed `(21, 12)`, an orientation that no row of the table reads; the pair is the
   occurrence pair of no row, so it is reachable from no root (`Table.range_eq_reach`); with literal
   fields, its literal (empty) star and a correct key order the row is refused by the birth clause
   alone, for every birth record.  `fib_side_swapped_collision`: the side-swapped row of
   `fib_side_swapped` likewise gets the key of row 12 of `fibTable`.
7. **A letter-pair quotient cycle with no packet cycle over it** (Tribonacci; L5).
   `trib_letterpair_cycle`, `trib_letterpair_cycle_unrealised`: the labelled 2-cycle
   `(0,1) -(1,0)-> (1,0) -(0,1)-> (0,1)` of the naive letter-pair quotient (vertices: pairs of
   distinct letters; edges `(a,b) -(d,e)-> (σ(a)[d], σ(b)[e])`) has no packet walk of length 4
   over it (`lpWalk` is empty there, by `decide +kernel`; `lpWalk_mem`), hence no infinite
   packet walk and no packet cycle over it.  The full child stars keep the digits and the
   splits that the letter-pair quotient forgets.

## Controls proved elsewhere and not repeated here

* The order hypothesis: `Psc.PacketCertificate.weird_accepted`, `weird_rows_collide`,
  `weird_not_injective`, `weirdFin_refused`, and `Psc.PacketSquare.weird_square_fails` (with an
  empty `<` an accepted table may list two rows over one occurrence pair, and the square fails).
* The Fibonacci counterparts of the replays of item 6: `fib_dropped_split`,
  `fib_side_swapped`, `fib_hub_coerced`, `fib_duplicate_isolated`,
  `fib_duplicate_not_injective`, `fib_wrong_global`, `fibExtra_forged_outside`,
  `fibExtra_forged_not_reached`, `fibExtra_forged_unreachable`.  `fib_duplicate_key` (a copied
  row that no star names: key and birth clauses) is the non-isolated variant of the duplicate
  and is not replayed.
* Listed states beyond the seed closure: `fibExtra_accepted`; a birth that is not the first
  incoming edge: `fibExtra_birth_not_first`.
* The other hub rows: `fib_hub_undefined`, `fib_hub_state_oob`, `fib_hub_coincident`,
  `fib_hub_duplicate`; the other Fibonacci mutations of `Psc.PacketCertificate`
  (`fib_dropped_child`, `fib_wrong_split`, `fib_bad_destination`, `fib_truncated`,
  `fib_wrong_residual`, `fib_wrong_interior`, `fib_wrong_stop`, `fib_wrong_ordinal`,
  `fib_no_seed`).
* A quotient cycle need not be realised by a cycle: `Psc.GraphRefinement.unroll_cycle`,
  `tail_not_cyclic`; the actual graphs have no cycle: `Psc.OccurrenceRealisation.anchored_no_cycle`,
  `Psc.PacketSquare.universe_acyclic`, `covered_acyclic`.
* The block projection and a reading through the square on Fibonacci:
  `Psc.OccurrenceRealisation.fib_block_readings`, `Psc.PacketSquare.fib_dead_packet`; the
  absolute lineage of the archived cycle: `Psc.OccurrenceRealisation.rs_cycle_lineage`,
  `rs_infinite_lineage`.

## Hypotheses

Every specific statement is about one of the four committed `Fin 3` tables (or a mutation of
one), elaborated with the default instances, so the `[LinearOrder α]` theorems of
`Psc.PacketSquare` apply (`fin3_occAt_injective`); the one exception is
`fib_side_swapped_collision`, about the `Fin 2` table of `fib_side_swapped`.  The generic
helpers: `deadEnd_inevitable_not_inevMax` (any child graph), `graph_deadEnd`,
`graphSuccess_deadEnd`, `increasing_spec`, `keysOK_eq_false_of_keyCode_eq`,
`factorsOK_eq_false_of_ne` and `factorsOK_eq_false_of_length` (any table, no order hypothesis),
`exists_universe_over`, `universe_deadEnd`, `universe_deadEnd_for` (an accepted table over a
linearly ordered alphabet).  No hypothesis is placed on any substitution.

## Not proved here

That the Mojo exporter is correct, or that any table other than the four committed ones is
accepted (each data module decides its own table).  The counts of the `*_shape` theorems are
finite facts about the committed tables, not statements about the substitutions beyond those
tables; the number of productive root rows of Tribonacci is not computed.  The letter-pair
control concerns one labelled 2-cycle and packet walks only; no absolute statement along it is
made.  `rs_support_not_strict` says only that the states 7 and 8 (and the orientation
`rsState8.swap`) lie in no strict closed set of the balanced-pair automaton; nothing here is
evidence for or against C4.  The forged pair of `rs_forged_outside` is shown unreachable from
the root pairs of the listed states only (`Table.range_eq_reach`); nothing is said about other
frames.  `np_incidence_eigen` gives eigenvectors only; no Pisot predicate is evaluated.  The
algebraic
and endpoint layers of the G/F template are not re-run.  No legal context, hull point or
desubstitution history is produced by any lineage here.  Nothing here advances, proves or
closes C4, G1, #84, #138, #139 or the Pisot substitution conjecture.
-/
import PscVerif.PacketSquare
import PscVerif.PacketSquareData.Tribonacci
import PscVerif.PacketSquareData.RealSecondary
import PscVerif.PacketSquareData.NonPisot
import PscVerif.PacketSquareData.GfActual

namespace Psc.PacketSquareControls

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.Incidence
open Psc.QuantifierInterface Psc.QuantifierBinding
open Psc.OccurrenceAddress Psc.OccurrenceGraph Psc.OccurrenceRealisation Psc.GraphRefinement
open Psc.PacketCertificate Psc.PacketSquare
open PscVerif.PacketSquareData

/-! ### Generic helpers -/

section Generic

universe u

variable {S : Type u} {G : ChildGraph S} {x : S}

/-- **A dead end satisfies (A) vacuously and fails (A⁺)**: no admissible infinite path leaves
it, and it is neither a target nor has a child. -/
theorem deadEnd_inevitable_not_inevMax (h : G.DeadEnd x) : G.Inevitable x ∧ ¬ G.InevMax x := by
  refine ⟨fun p hp0 hp => absurd (hp0 ▸ hp 0) (h.2 (p 1)), fun hm => ?_⟩
  cases hm with
  | here ht => exact h.1 ht
  | step hch _ =>
    obtain ⟨t, ht⟩ := hch
    exact h.2 t ht

end Generic

variable {α : Type} [DecidableEq α]

/-- A star entry that names a destination row. -/
def isChildEntry : StarRow → Bool
  | .child .. => true
  | .split .. => false

/-- The number of child entries (listed edges) of a table. -/
def edgeCount (t : Table α) : ℕ := (t.stars.map fun st => (st.filter isChildEntry).length).sum

/-- The number of split entries of a table. -/
def splitCount (t : Table α) : ℕ :=
  (t.stars.map fun st => (st.filter fun r => !isChildEntry r).length).sum

/-- The number of root rows of a table. -/
def rootCount (t : Table α) : ℕ := (t.packets.filter fun p => p.factor.isNone).length

/-- Row `i` has no child entry in its star. -/
def noChild (t : Table α) (i : ℕ) : Bool := (t.stars.getD i []).all fun r => !isChildEntry r

/-- Row `i` lies over a noncoincident listed state. -/
def ncRow (t : Table α) (i : ℕ) : Bool :=
  match t.packets[i]? >>= fun p => t.states[p.state]? with
  | some T => !decide (T.1 = T.2)
  | none => false

omit [DecidableEq α] in
/-- `occAt` from a computed `decodeAt`. -/
theorem occAt_of_decodeAt {t : Table α} {i : Fin t.packets.length} {x : Occ α}
    (h : t.decodeAt i.val = some x) : t.occAt i = x := by
  unfold Table.occAt
  rw [h]
  rfl

/-- A row over a noncoincident state with no child entry is a dead end of the packet graph
(coincidence target). -/
theorem graph_deadEnd (t : Table α) (i : Fin t.packets.length) (hnc : ncRow t i.val = true)
    (hno : noChild t i.val = true) : t.graph.DeadEnd i := by
  refine ⟨fun ht => ?_, fun j ⟨d, e, hm⟩ => ?_⟩
  · unfold ncRow at hnc
    have hp : t.packets[i.val]? = some t.packets[i] := List.getElem?_eq_getElem i.2
    rw [hp] at hnc
    simp only [Option.bind_eq_bind, Option.bind_some] at hnc
    cases hT : t.states[(t.packets[i]).state]? with
    | none => rw [hT] at hnc; exact absurd hnc (by simp)
    | some T =>
      rw [hT] at hnc
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnc
      exact hnc (ht T hT)
  · have := List.all_eq_true.1 hno _ hm
    simp [isChildEntry] at this

omit [DecidableEq α] in
/-- A row whose `success` bit is `false` and with no child entry is a dead end of the packet
graph with the success target. -/
theorem graphSuccess_deadEnd (t : Table α) (i : Fin t.packets.length)
    (hs : (t.packets[i]).success = false) (hno : noChild t i.val = true) :
    t.graphSuccess.DeadEnd i := by
  refine ⟨fun ht => ?_, fun j ⟨d, e, hm⟩ => ?_⟩
  · change (t.packets[i]).success = true at ht
    rw [hs] at ht
    exact absurd ht (by simp)
  · have := List.all_eq_true.1 hno _ hm
    simp [isChildEntry] at this

/-- The star equation at row `i` (`false` beyond the last row): the per-row form of the star
clause. -/
def starOKAt (t : Table α) (i : ℕ) : Bool :=
  match t.packets[i]? with
  | some p => t.starOK p (t.stars.getD i [])
  | none => false

/-- The row clause at row `i` (`false` beyond the last row). -/
def packetOKAt [Fintype α] (t : Table α) (i : ℕ) : Bool :=
  match t.packets[i]? with
  | some p => t.packetOK p
  | none => false

/-- A list passing `increasing` has only defined entries, strictly increasing. -/
theorem increasing_spec : ∀ l : List (Option ℕ), increasing l = true →
    List.IsChain (· < ·) (l.map (·.getD 0)) ∧ ∀ x ∈ l, x.isSome = true
  | [], _ => by simp
  | [some a], _ => by simp
  | [none], h => by simp [increasing] at h
  | none :: _ :: _, h => by simp [increasing] at h
  | some _ :: none :: _, h => by simp [increasing] at h
  | some a :: some b :: rest, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := increasing_spec (some b :: rest) h.2
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, Option.getD_some] at h1 ⊢
      exact List.IsChain.cons_cons h.1 h1
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact h2 x hx

omit [DecidableEq α] in
/-- **Two distinct rows with one key code: no key order passes the key clause.**  A key order
passing `keysOK` lists every row exactly once with strictly increasing codes, so two rows
with one code cannot both be listed. -/
theorem keysOK_eq_false_of_keyCode_eq (t : Table α) {i j : ℕ} (hij : i ≠ j)
    (hi : i < t.packets.length) (hj : j < t.packets.length)
    (hk : t.packets[i]?.map t.keyCode = t.packets[j]?.map t.keyCode) : t.keysOK = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [Table.keysOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hlen, hinc⟩ := h
  obtain ⟨hch, hsome⟩ := increasing_spec _ hinc
  set g : ℕ → ℕ := fun k => (t.packets[k]?.map t.keyCode).getD 0 with hg
  have hnd : (t.keyOrder.map g).Nodup := by
    have hpw := (List.isChain_iff_pairwise.1 hch).imp (fun h => ne_of_lt h)
    rw [List.map_map] at hpw
    exact hpw
  have hko : t.keyOrder.Nodup := List.Nodup.of_map _ hnd
  have hrange : ∀ k ∈ t.keyOrder, k < t.packets.length := by
    intro k hk
    have := hsome _ (List.mem_map_of_mem hk)
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at this
    exact absurd this (by simp)
  have hfin : t.keyOrder.toFinset = Finset.range t.packets.length := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      exact Finset.mem_range.2 (hrange k (List.mem_toFinset.1 hk))
    · rw [List.toFinset_card_of_nodup hko, hlen, Finset.card_range]
  have hi' : i ∈ t.keyOrder := by
    rw [← List.mem_toFinset, hfin]
    exact Finset.mem_range.2 hi
  have hj' : j ∈ t.keyOrder := by
    rw [← List.mem_toFinset, hfin]
    exact Finset.mem_range.2 hj
  exact hij (List.inj_on_of_nodup_map hnd hi' hj' (by simp only [hg, hk]))

section Linear

variable [Fintype α] [LinearOrder α]

/-- **Every row is the packet of an element of a universe** (`row_realised`, then
`universePacket_eq_iff`). -/
theorem exists_universe_over (t : Table α) (h : t.check = true) (i : Fin t.packets.length) :
    ∃ T₀, ∃ hT₀ : T₀ ∈ t.states, ∃ hnc : T₀.1 ≠ T₀.2, ∃ a : Universe t.s T₀,
      universePacket t h hT₀ hnc a = i := by
  obtain ⟨T, hT, hnc, a, ha, hra⟩ := row_realised t h i
  exact ⟨T, hT, hnc, ⟨a, ha⟩, (universePacket_eq_iff t h hT hnc ⟨a, ha⟩ i).2 hra.symm⟩

/-- **A packet dead end is a dead end of the universe at every element over it**
(`deadEnd_up` along `packet_square`, coincidence target), so (A) holds there vacuously and (A⁺)
fails. -/
theorem universe_deadEnd (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀)
    {i : Fin t.packets.length}
    (ha : universePacket t h hT₀ hnc a = i) (hd : t.graph.DeadEnd i) :
    (universeGraph t.s T₀).DeadEnd a ∧ (universeGraph t.s T₀).Inevitable a ∧
      ¬ (universeGraph t.s T₀).InevMax a := by
  have hR := (packet_square t h hT₀ hnc).1
  have hd' : (universeGraph t.s T₀).DeadEnd a := deadEnd_up hR.complete hR.targetDown (ha ▸ hd)
  exact ⟨hd', deadEnd_inevitable_not_inevMax hd'⟩

/-- The same for the success target (`deadEnd_up` along `packet_square`, success target). -/
theorem universe_deadEnd_for (t : Table α) (h : t.check = true) {T₀ : List α × List α}
    (hT₀ : T₀ ∈ t.states) (hnc : T₀.1 ≠ T₀.2) (a : Universe t.s T₀)
    {i : Fin t.packets.length}
    (ha : universePacket t h hT₀ hnc a = i) (hd : t.graphSuccess.DeadEnd i) :
    (universeGraphFor t.s T₀ t.target).DeadEnd a ∧
      (universeGraphFor t.s T₀ t.target).Inevitable a ∧
      ¬ (universeGraphFor t.s T₀ t.target).InevMax a := by
  have hR := (packet_square t h hT₀ hnc).2
  have hd' : (universeGraphFor t.s T₀ t.target).DeadEnd a :=
    deadEnd_up hR.complete hR.targetDown (ha ▸ hd)
  exact ⟨hd', deadEnd_inevitable_not_inevMax hd'⟩

end Linear

/-- The factor rows of state `i`, in the form the factor clause compares with
`literalFactors`: (listed child state, sign, ordinal, start, stop, total length). -/
def factorTuples (t : Table α) (i : ℕ) :
    List (Option (List α × List α) × Bool × ℕ × ℕ × ℕ × ℕ) :=
  (t.factors.filter fun f => f.parent = i).map fun f =>
    (t.states[f.child]?, f.sign, f.ordinal, f.start, f.stop, f.total)

/-- **One state refuses the factor clause.**  If the factor rows of a noncoincident listed
state are not the literal ordered factorisation of its image, `factorsOK` refuses the table,
whatever the other states say. -/
theorem factorsOK_eq_false_of_ne [LT α] [DecidableLT α] (t : Table α) {i : ℕ}
    {T : List α × List α} (hT : t.states[i]? = some T) (hnc : T.1 ≠ T.2)
    (hne : factorTuples t i ≠ literalFactors t.s T) : t.factorsOK = false := by
  rw [Bool.eq_false_iff]
  intro h
  simp only [Table.factorsOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hi : i < t.states.length := by
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at hT
    exact absurd hT (by simp)
  have h2 := h.2 i hi
  rw [hT] at h2
  simp only [hnc, ite_false, decide_eq_true_eq] at h2
  exact hne h2

/-- **A short count refusal of the factor clause.**  If a noncoincident listed state has a
number of factor rows different from the number of blocks of the literal ordered factorisation
of its image, `factorsOK` refuses the table, whatever the rows say. -/
theorem factorsOK_eq_false_of_length [LT α] [DecidableLT α] (t : Table α) {i : ℕ}
    {T : List α × List α} (hT : t.states[i]? = some T) (hnc : T.1 ≠ T.2)
    (hlen : (t.factors.filter fun f => f.parent = i).length ≠ (literalFactors t.s T).length) :
    t.factorsOK = false := by
  refine factorsOK_eq_false_of_ne t hT hnc fun he => hlen ?_
  have := congrArg List.length he
  simpa [factorTuples] using this

/-! ### 1. Tribonacci `01/02/0`: accepted, no success, (A) and (A⁺) differ -/

/-- The shape of the exported Tribonacci table: 6 states, 12 factor rows, 132 rows, 37 root
rows, 185 listed edges (child entries), 194 split entries; no row has its `success` bit set;
38 rows over a noncoincident state and 9 rows over a coincidence state have no child entry. -/
theorem trib_shape :
    Tribonacci.table.states.length = 6 ∧ Tribonacci.table.factors.length = 12 ∧
      Tribonacci.table.packets.length = 132 ∧ rootCount Tribonacci.table = 37 ∧
      edgeCount Tribonacci.table = 185 ∧ splitCount Tribonacci.table = 194 ∧
      Tribonacci.table.target = none ∧
      Tribonacci.table.packets.all (fun p => !p.success) = true ∧
      ((List.range 132).filter fun i =>
        noChild Tribonacci.table i && ncRow Tribonacci.table i).length = 38 ∧
      ((List.range 132).filter fun i =>
        noChild Tribonacci.table i && !ncRow Tribonacci.table i).length = 9 := by
  decide +kernel

/-- No row of the Tribonacci table is a success target. -/
theorem trib_no_success (i : Fin Tribonacci.table.packets.length) :
    ¬ Tribonacci.table.graphSuccess.target i := by
  intro hi
  change (Tribonacci.table.packets[i]).success = true at hi
  have h := List.all_eq_true.1 trib_shape.2.2.2.2.2.2.2.1 _ (List.getElem_mem i.2)
  simp only [Fin.getElem_fin] at hi
  rw [hi] at h
  exact absurd h (by decide)

/-- **The default target has no success, at the absolute level** (success-target transfer
`packet_square_readings_for`): for every noncoincident listed state `T₀` of the Tribonacci
table, no element of `Universe σ T₀` is productive for the packet-success target, i.e. no
retained absolute lineage of the iterates of `T₀` reaches a strictly interior coincidence. -/
theorem trib_universe_no_success {T₀ : List (Fin 3) × List (Fin 3)}
    (hT₀ : T₀ ∈ Tribonacci.table.states) (hnc : T₀.1 ≠ T₀.2)
    (a : Universe Tribonacci.table.s T₀) :
    ¬ (universeGraphFor Tribonacci.table.s T₀ Tribonacci.table.target).Productive a := by
  rw [(packet_square_readings_for Tribonacci.table Tribonacci.accepted hT₀ hnc a).1]
  rintro ⟨j, -, hj⟩
  exact trib_no_success j hj

/-- Row 6 of the Tribonacci table. -/
def tribRow6 : Fin Tribonacci.table.packets.length := ⟨6, by decide +kernel⟩

/-- Row 37 of the Tribonacci table. -/
def tribRow37 : Fin Tribonacci.table.packets.length := ⟨37, by decide +kernel⟩

/-- Row 6 lies over a noncoincident state and has no child entry; row 37 lies over a
coincidence state (`(0, 0)`, see `trib_inevitable_ne_inevMax`), has the empty star (so no child
entry) and `success = false`. -/
theorem trib_rows_6_37 :
    ncRow Tribonacci.table 6 = true ∧ noChild Tribonacci.table 6 = true ∧
      ncRow Tribonacci.table 37 = false ∧ noChild Tribonacci.table 37 = true ∧
      (Tribonacci.table.packets[37]?.map (·.success)) = some false ∧
      Tribonacci.table.stars.getD 37 [] = [] := by
  decide +kernel

/-- **(A) and (A⁺) differ on the Tribonacci packet graph, for both targets.**  Row 6 is a
noncoincident dead end of `t.graph`: (A) holds there vacuously and (A⁺) fails.  Row 37 is a
target of `t.graph` (a coincidence) and a dead end of `t.graphSuccess` (not a success, no
child): (A) holds there vacuously and (A⁺) fails for the success target. -/
theorem trib_inevitable_ne_inevMax :
    Tribonacci.table.graph.DeadEnd tribRow6 ∧ Tribonacci.table.graph.Inevitable tribRow6 ∧
      ¬ Tribonacci.table.graph.InevMax tribRow6 ∧
      Tribonacci.table.graph.target tribRow37 ∧
      Tribonacci.table.graphSuccess.DeadEnd tribRow37 ∧
      Tribonacci.table.graphSuccess.Inevitable tribRow37 ∧
      ¬ Tribonacci.table.graphSuccess.InevMax tribRow37 := by
  obtain ⟨h6a, h6b, h37a, h37b, h37c, -⟩ := trib_rows_6_37
  have hd6 := graph_deadEnd Tribonacci.table tribRow6 h6a h6b
  have hs37 : (Tribonacci.table.packets[tribRow37]).success = false := by
    have : Tribonacci.table.packets[37]? = some (Tribonacci.table.packets[tribRow37]) :=
      List.getElem?_eq_getElem tribRow37.2
    rw [this] at h37c
    simpa using h37c
  have hd37 := graphSuccess_deadEnd Tribonacci.table tribRow37 hs37 h37b
  have ht37 : Tribonacci.table.graph.target tribRow37 := by
    intro T hT
    have hst : Tribonacci.table.states[(Tribonacci.table.packets[tribRow37]).state]? =
        some ([0], [0]) := by decide +kernel
    rw [hst] at hT
    cases hT
    rfl
  exact ⟨hd6, (deadEnd_inevitable_not_inevMax hd6).1, (deadEnd_inevitable_not_inevMax hd6).2,
    ht37, hd37, (deadEnd_inevitable_not_inevMax hd37).1, (deadEnd_inevitable_not_inevMax hd37).2⟩

/-- **(A) and (A⁺) differ at the absolute level** (dead-end transfer along `packet_square`):
row 6 is the packet of an element of the universe of some noncoincident listed state, and at
every element of every such universe whose packet is row 6, (A) holds and (A⁺) fails in
`universeGraph`; likewise row 37 for the success target in `universeGraphFor`. -/
theorem trib_universe_inevitable_ne_inevMax :
    (∃ T₀, ∃ hT₀ : T₀ ∈ Tribonacci.table.states, ∃ hnc : T₀.1 ≠ T₀.2,
      ∃ a : Universe Tribonacci.table.s T₀,
        universePacket Tribonacci.table Tribonacci.accepted hT₀ hnc a = tribRow6) ∧
    (∀ {T₀} (hT₀ : T₀ ∈ Tribonacci.table.states) (hnc : T₀.1 ≠ T₀.2)
      (a : Universe Tribonacci.table.s T₀),
      universePacket Tribonacci.table Tribonacci.accepted hT₀ hnc a = tribRow6 →
        (universeGraph Tribonacci.table.s T₀).Inevitable a ∧
          ¬ (universeGraph Tribonacci.table.s T₀).InevMax a) ∧
    (∃ T₀, ∃ hT₀ : T₀ ∈ Tribonacci.table.states, ∃ hnc : T₀.1 ≠ T₀.2,
      ∃ a : Universe Tribonacci.table.s T₀,
        universePacket Tribonacci.table Tribonacci.accepted hT₀ hnc a = tribRow37) ∧
    (∀ {T₀} (hT₀ : T₀ ∈ Tribonacci.table.states) (hnc : T₀.1 ≠ T₀.2)
      (a : Universe Tribonacci.table.s T₀),
      universePacket Tribonacci.table Tribonacci.accepted hT₀ hnc a = tribRow37 →
        (universeGraphFor Tribonacci.table.s T₀ Tribonacci.table.target).Inevitable a ∧
          ¬ (universeGraphFor Tribonacci.table.s T₀ Tribonacci.table.target).InevMax a) := by
  obtain ⟨hd6, -, -, -, hd37, -, -⟩ := trib_inevitable_ne_inevMax
  refine ⟨exists_universe_over _ Tribonacci.accepted tribRow6, fun hT₀ hnc a ha => ?_,
    exists_universe_over _ Tribonacci.accepted tribRow37, fun hT₀ hnc a ha => ?_⟩
  · exact (universe_deadEnd _ Tribonacci.accepted hT₀ hnc a ha hd6).2
  · exact (universe_deadEnd_for _ Tribonacci.accepted hT₀ hnc a ha hd37).2

/-! #### A positive control for ρ on Tribonacci: one absolute lineage, replayed -/

/-- The Tribonacci seed `(01, 10)` (state 0 of the table). -/
def tribSeed : List (Fin 3) × List (Fin 3) := ([0, 1], [1, 0])

/-- The reading at level 1: the block `(102, 201)`, born as ordinal 1 of the seed. -/
def tribY1 : Occ (Fin 3) := ⟨([1, 0, 2], [2, 0, 1]), 0, 0, some ⟨tribSeed, 1⟩⟩

/-- The reading at level 2: the coincidence block `(0, 0)`, born as ordinal 0 of `(102, 201)`. -/
def tribY2 : Occ (Fin 3) := ⟨([0], [0]), 0, 0, some ⟨([1, 0, 2], [2, 0, 1]), 0⟩⟩

/-- The absolute steps `(0,0,0) -(1,1)-> (1,1,1) -(0,0)-> (2,2,2)` of the iterates of the seed
(`σ(01, 10) = (0102, 0201)`, `σ²(01, 10) = (0102010, 0100102)`), the literal steps of their
readings, and the rows: row 0 is the root reading `(0, 0)` of the seed, row 38 decodes to
`tribY1`, row 57 to `tribY2`, and the star of row 0 has `(1,1) -> 38`, that of row 38 has
`(0,0) -> 57`. -/
theorem trib_lineage_steps :
    absStep Tribonacci.table.s tribSeed ⟨0, 0, 0⟩ 1 1 = some ⟨1, 1, 1⟩ ∧
      absStep Tribonacci.table.s tribSeed ⟨1, 1, 1⟩ 0 0 = some ⟨2, 2, 2⟩ ∧
      occStep Tribonacci.table.s ⟨tribSeed, 0, 0, none⟩ 1 1 = some (.child tribY1) ∧
      occStep Tribonacci.table.s tribY1 0 0 = some (.child tribY2) ∧
      Tribonacci.table.states[0]? = some tribSeed ∧
      Tribonacci.table.decodeAt 0 = some ⟨tribSeed, 0, 0, none⟩ ∧
      Tribonacci.table.decodeAt 38 = some tribY1 ∧ Tribonacci.table.decodeAt 57 = some tribY2 ∧
      StarRow.child 1 1 38 ∈ Tribonacci.table.stars.getD 0 [] ∧
      StarRow.child 0 0 57 ∈ Tribonacci.table.stars.getD 38 [] := by
  decide +kernel

/-- `tribY1` reads `(1, 1, 1)` at offset `1`. -/
theorem trib_anchor1 : Anchor Tribonacci.table.s tribSeed ⟨1, 1, 1⟩ tribY1 1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, rfl, rfl⟩

/-- `tribY2` reads `(2, 2, 2)` at offset `2`. -/
theorem trib_anchor2 : Anchor Tribonacci.table.s tribSeed ⟨2, 2, 2⟩ tribY2 2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, rfl, rfl⟩

/-- The seed `(01, 10)` is a noncoincident listed state of the Tribonacci table. -/
theorem trib_seed_listed : tribSeed ∈ Tribonacci.table.states ∧ tribSeed.1 ≠ tribSeed.2 :=
  ⟨List.mem_of_getElem? trib_lineage_steps.2.2.2.2.1, by decide⟩

/-- The seed is balanced. -/
theorem trib_seed_bal : Equiv1 tribSeed.1 tribSeed.2 :=
  (seed_isBlock (by decide : (0 : Fin 3) ≠ 1)).2.1

/-- The root element of the universe at `(0, 0)`. -/
def tribU0 : Universe Tribonacci.table.s tribSeed :=
  ⟨rootAnchored Tribonacci.table.s trib_seed_bal 0 0,
    rootAnchored_mem Tribonacci.table.s trib_seed_bal (by decide) (by decide)⟩

/-- The anchored pair at level 1. -/
def tribA1 : Anchored Tribonacci.table.s tribSeed := ⟨(⟨1, 1, 1⟩, tribY1), 1, trib_anchor1⟩

/-- The anchored pair at level 2. -/
def tribA2 : Anchored Tribonacci.table.s tribSeed := ⟨(⟨2, 2, 2⟩, tribY2), 2, trib_anchor2⟩

/-- **The square commutes along one replayed Tribonacci lineage** (positive control for ρ and
the composite).  The absolute lineage `(0,0,0) → (1,1,1) → (2,2,2)` of the seed `(01, 10)` is
retained, lies in the declared universe, and its packets (`universePacket`) are the rows
`0 → 38 → 57`; the last reading is the coincidence block `(0, 0)` at a first child (outer
boundary, not strictly interior).  Through `packet_square_readings` and
`packet_square_readings_for`: the root element is productive for the coincidence target and
not for the success target, and so is its packet. -/
theorem trib_lineage :
    ∃ (h1 : tribA1 ∈ Universe Tribonacci.table.s tribSeed)
      (h2 : tribA2 ∈ Universe Tribonacci.table.s tribSeed),
      (universeGraph Tribonacci.table.s tribSeed).child tribU0 ⟨tribA1, h1⟩ ∧
      (universeGraph Tribonacci.table.s tribSeed).child ⟨tribA1, h1⟩ ⟨tribA2, h2⟩ ∧
      (universePacket Tribonacci.table Tribonacci.accepted trib_seed_listed.1
          trib_seed_listed.2 tribU0).val = 0 ∧
      (universePacket Tribonacci.table Tribonacci.accepted trib_seed_listed.1
          trib_seed_listed.2 ⟨tribA1, h1⟩).val = 38 ∧
      (universePacket Tribonacci.table Tribonacci.accepted trib_seed_listed.1
          trib_seed_listed.2 ⟨tribA2, h2⟩).val = 57 ∧
      tribY2.Coincident ∧ tribY2.Boundary ∧
      (universeGraph Tribonacci.table.s tribSeed).Productive tribU0 ∧
      Tribonacci.table.graph.Productive
        (universePacket Tribonacci.table Tribonacci.accepted trib_seed_listed.1
          trib_seed_listed.2 tribU0) ∧
      ¬ (universeGraphFor Tribonacci.table.s tribSeed Tribonacci.table.target).Productive
        tribU0 ∧
      ¬ Tribonacci.table.graphSuccess.Productive
        (universePacket Tribonacci.table Tribonacci.accepted trib_seed_listed.1
          trib_seed_listed.2 tribU0) := by
  obtain ⟨s1, s2, o1, o2, -, d0, d38, d57, -, -⟩ := trib_lineage_steps
  have e1 : (anchoredGraph Tribonacci.table.s tribSeed).child tribU0.1 tribA1 :=
    ⟨by decide, 1, 1, s1, o1⟩
  have e2 : (anchoredGraph Tribonacci.table.s tribSeed).child tribA1 tribA2 :=
    ⟨by decide, 0, 0, s2, o2⟩
  have h1 : tribA1 ∈ Universe Tribonacci.table.s tribSeed :=
    universe_closed _ _ tribU0.2 e1
  have h2 : tribA2 ∈ Universe Tribonacci.table.s tribSeed := universe_closed _ _ h1 e2
  have p0 := (universePacket_eq_iff Tribonacci.table Tribonacci.accepted trib_seed_listed.1
    trib_seed_listed.2 tribU0 ⟨0, by decide +kernel⟩).2 (occAt_of_decodeAt d0)
  have p1 := (universePacket_eq_iff Tribonacci.table Tribonacci.accepted trib_seed_listed.1
    trib_seed_listed.2 ⟨tribA1, h1⟩ ⟨38, by decide +kernel⟩).2 (occAt_of_decodeAt d38)
  have p2 := (universePacket_eq_iff Tribonacci.table Tribonacci.accepted trib_seed_listed.1
    trib_seed_listed.2 ⟨tribA2, h2⟩ ⟨57, by decide +kernel⟩).2 (occAt_of_decodeAt d57)
  have e1' : (universeGraph Tribonacci.table.s tribSeed).child tribU0 ⟨tribA1, h1⟩ := e1
  have e2' : (universeGraph Tribonacci.table.s tribSeed).child ⟨tribA1, h1⟩ ⟨tribA2, h2⟩ :=
    e2
  have hprod : (universeGraph Tribonacci.table.s tribSeed).Productive tribU0 :=
    ⟨⟨tribA2, h2⟩, (Relation.ReflTransGen.single e1').tail e2', rfl⟩
  refine ⟨h1, h2, e1', e2', by rw [p0], by rw [p1], by rw [p2], rfl,
    ⟨rfl, rfl, fun b hb => ?_⟩,
    hprod, (packet_square_readings Tribonacci.table Tribonacci.accepted trib_seed_listed.1
      trib_seed_listed.2 tribU0).1.1 hprod,
    trib_universe_no_success trib_seed_listed.1 trib_seed_listed.2 tribU0,
    fun ⟨j, _, hj⟩ => trib_no_success j hj⟩
  simp only [tribY2, Option.some.injEq] at hb
  rw [← hb]

/-! ### 2. Real-secondary `1/02/202`: the packet 2-cycle `209 → 429 → 209` -/

/-- The shape of the exported real-secondary table: 10 states, 26 factor rows, 507 rows,
118 root rows, 948 listed edges, 1274 split entries, 24 hub rows. -/
theorem rs_shape :
    RealSecondary.table.states.length = 10 ∧ RealSecondary.table.factors.length = 26 ∧
      RealSecondary.table.packets.length = 507 ∧ rootCount RealSecondary.table = 118 ∧
      edgeCount RealSecondary.table = 948 ∧ splitCount RealSecondary.table = 1274 ∧
      RealSecondary.table.hubs.length = 24 := by
  decide +kernel

/-- Row 209 of the real-secondary table. -/
def rsRow209 : Fin RealSecondary.table.packets.length := ⟨209, by decide +kernel⟩

/-- Row 429 of the real-secondary table. -/
def rsRow429 : Fin RealSecondary.table.packets.length := ⟨429, by decide +kernel⟩

/-- The substitution of the table is `rsSubst` of `Psc.OccurrenceGraph`, its state 0 is the seed
`(01, 10)` (`rsSeed`), and rows 209 and 429 decode to the calibration pairs `x209`, `x429`
(decoded by hand there); the star of 209 has the entry `(0,0) -> 429` and that of 429 the entry
`(0,2) -> 209`. -/
theorem rs_cycle_rows :
    RealSecondary.table.s = rsSubst ∧ RealSecondary.table.states[0]? = some rsSeed ∧
      RealSecondary.table.decodeAt 209 = some x209 ∧
      RealSecondary.table.decodeAt 429 = some x429 ∧
      StarRow.child 0 0 429 ∈ RealSecondary.table.stars.getD 209 [] ∧
      StarRow.child 0 2 209 ∈ RealSecondary.table.stars.getD 429 [] := by
  refine ⟨rfl, ?_⟩
  decide +kernel

/-- **The cycle is accepted at every literal layer.**  Rows 209 and 429 decode to `x209` and
`x429`; they form a 2-cycle of the packet graph and of the literal occurrence graph; their
stars are the literal stars (`Table.check_sound`, star equation), whose values are those of
`rs_rows_stars`; their carried addresses, letters and residuals are the literal ones
(`Table.check_sound`), with the values of `rs_rows_fields` (letters `(0, 2)` and `(1, 2)`). -/
theorem rs_cycle_literal :
    RealSecondary.table.occAt rsRow209 = x209 ∧ RealSecondary.table.occAt rsRow429 = x429 ∧
      RealSecondary.table.graph.child rsRow209 rsRow429 ∧
      RealSecondary.table.graph.child rsRow429 rsRow209 ∧
      Relation.TransGen RealSecondary.table.graph.child rsRow209 rsRow209 ∧
      (occGraph rsSubst).child x209 x429 ∧ (occGraph rsSubst).child x429 x209 ∧
      (RealSecondary.table.stars.getD 209 []).map RealSecondary.table.decodeEntry =
        (occStar rsSubst x209).map (fun r => (r.1, r.2.1, some r.2.2)) ∧
      (RealSecondary.table.stars.getD 429 []).map RealSecondary.table.decodeEntry =
        (occStar rsSubst x429).map (fun r => (r.1, r.2.1, some r.2.2)) ∧
      (RealSecondary.table.packets[rsRow209]).topAddr = some (2, 0, 4, 4) ∧
      (RealSecondary.table.packets[rsRow209]).botAddr = some (1, 2, 4, 4) ∧
      (RealSecondary.table.packets[rsRow429]).topAddr = some (4, 0, 9, 2) ∧
      (RealSecondary.table.packets[rsRow429]).botAddr = some (4, 0, 8, 1) ∧
      (RealSecondary.table.packets[rsRow209]).letters = (0, 2) ∧
      (RealSecondary.table.packets[rsRow429]).letters = (1, 2) ∧
      (RealSecondary.table.packets[rsRow209]).residual =
        RealSecondary.table.letters.map x209.residual ∧
      (RealSecondary.table.packets[rsRow429]).residual =
        RealSecondary.table.letters.map x429.residual := by
  obtain ⟨-, -, d209, d429, m1, m2⟩ := rs_cycle_rows
  have o209 : RealSecondary.table.occAt rsRow209 = x209 := occAt_of_decodeAt d209
  have o429 : RealSecondary.table.occAt rsRow429 = x429 := occAt_of_decodeAt d429
  have hs := Table.check_sound RealSecondary.table RealSecondary.accepted
  have c1 : RealSecondary.table.graph.child rsRow209 rsRow429 := ⟨0, 0, m1⟩
  have c2 : RealSecondary.table.graph.child rsRow429 rsRow209 := ⟨0, 2, m2⟩
  obtain ⟨f1, f2, f3, f4, f5, -, -⟩ := hs.2.2.2.2.1 rsRow209
  obtain ⟨g1, g2, g3, g4, g5, -, -⟩ := hs.2.2.2.2.1 rsRow429
  obtain ⟨a1, a2, a3, a4, l1, l2, l3, l4, -⟩ := rs_rows_fields
  rw [o209] at f1 f2 f3 f4 f5
  rw [o429] at g1 g2 g3 g4 g5
  have e209 : (RealSecondary.table.packets[rsRow209]).letters = (0, 2) :=
    Prod.ext (Option.some.inj (f3.symm.trans l1)) (Option.some.inj (f4.symm.trans l2))
  have e429 : (RealSecondary.table.packets[rsRow429]).letters = (1, 2) :=
    Prod.ext (Option.some.inj (g3.symm.trans l3)) (Option.some.inj (g4.symm.trans l4))
  have st209 := hs.2.2.2.1 rsRow209
  have st429 := hs.2.2.2.1 rsRow429
  rw [o209] at st209
  rw [o429] at st429
  exact ⟨o209, o429, c1, c2, .tail (.single c1) c2, rs_rows_occGraph.1, rs_rows_occGraph.2,
    st209, st429, f1.trans a1, f2.trans a2, g1.trans a3, g2.trans a4, e209, e429, f5, g5⟩

/-- The seed `(01, 10)` is a noncoincident listed state of the real-secondary table. -/
theorem rs_seed_listed : rsSeed ∈ RealSecondary.table.states ∧ rsSeed.1 ≠ rsSeed.2 :=
  ⟨List.mem_of_getElem? rs_cycle_rows.2.1, by decide⟩

/-- The element of the universe of the seed over `(3, 4, 4)` (`rsA3`, `rs_cycle_lineage`). -/
def rsU3 : Universe RealSecondary.table.s rsSeed := ⟨rsA3, rs_cycle_lineage.1⟩

/-- The element of the universe of the seed over `(4, 9, 8)` (`rsA4`, `rs_cycle_lineage`). -/
def rsU4 : Universe RealSecondary.table.s rsSeed := ⟨rsA4, rs_cycle_lineage.2.1⟩

/-- The packets of `rsU3` and `rsU4` are rows 209 and 429. -/
theorem rs_cycle_packets :
    universePacket RealSecondary.table RealSecondary.accepted rs_seed_listed.1 rs_seed_listed.2
        rsU3 = rsRow209 ∧
      universePacket RealSecondary.table RealSecondary.accepted rs_seed_listed.1
        rs_seed_listed.2 rsU4 = rsRow429 :=
  ⟨(universePacket_eq_iff _ _ _ _ rsU3 rsRow209).2 rs_cycle_literal.1,
    (universePacket_eq_iff _ _ _ _ rsU4 rsRow429).2 rs_cycle_literal.2.1⟩

/-- The rows along the packet cycle, `209, 429, 209, …`. -/
def rsCycleRow (n : ℕ) : Fin RealSecondary.table.packets.length :=
  if n % 2 = 0 then rsRow209 else rsRow429

/-- The packet cycle as an infinite path of the packet graph. -/
theorem rs_cycle_path : RealSecondary.table.graph.IsPath rsCycleRow := by
  intro n
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h' : (n + 1) % 2 = 1 := by omega
    simp only [rsCycleRow, h, h', ite_true]
    exact rs_cycle_literal.2.2.1
  · have h' : (n + 1) % 2 = 0 := by omega
    simp only [rsCycleRow, h, h']
    exact rs_cycle_literal.2.2.2.1

/-- **The packet cycle is realised only as an infinite absolute lineage, never as an absolute
cycle.**  For every noncoincident listed state `T₀` and every element `a` of its universe whose
packet is row 209: the packet cycle lifts (`packet_path_lift`) to an infinite path of the
universe graph from `a`, whose packets are `209, 429, 209, …` and whose level rises by one per
step, and no cycle of the universe graph passes through `a` (`universe_acyclic`).  Such an
element exists: `rsU3`, over `(3, 4, 4)` in the iterates of the seed (`rs_cycle_packets`). -/
theorem rs_cycle_realised {T₀ : List (Fin 3) × List (Fin 3)}
    (hT₀ : T₀ ∈ RealSecondary.table.states) (hnc : T₀.1 ≠ T₀.2)
    (a : Universe RealSecondary.table.s T₀)
    (ha : universePacket RealSecondary.table RealSecondary.accepted hT₀ hnc a = rsRow209) :
    (∃ p : ℕ → Universe RealSecondary.table.s T₀, p 0 = a ∧
      (universeGraph RealSecondary.table.s T₀).IsPath p ∧
      (∀ n, universePacket RealSecondary.table RealSecondary.accepted hT₀ hnc (p n) =
        rsCycleRow n) ∧
      ∀ n, (p n).1.1.1.level = a.1.1.1.level + n) ∧
    ¬ Relation.TransGen (universeGraph RealSecondary.table.s T₀).child a a :=
  ⟨packet_path_lift _ _ hT₀ hnc a rsCycleRow (by rw [ha]; rfl) rs_cycle_path,
    universe_acyclic _ _ a⟩

/-- **The premise the square does not supply.**  The balanced-pair states 7 and 8 of the
cycle, and the orientation `rsState8.swap` that row 209 reads, are not in any strict closed set
of `bpaGraph rsSubst`: state 7 has the child `rsState8.swap`, and both orientations of state 8
have the coincidence child `(2, 2)`, a target.  So the cycle does not lie on the strict
child-closed support that the C4 input type asks for; nothing here is evidence for or against
C4. -/
theorem rs_support_not_strict :
    (bpaGraph rsSubst).child rsState7 rsState8.swap ∧
      (bpaGraph rsSubst).child rsState8 ([2], [2]) ∧
      (bpaGraph rsSubst).child rsState8.swap ([2], [2]) ∧
      ∀ C : Set (List (Fin 3) × List (Fin 3)), rsState7 ∈ C ∨ rsState8 ∈ C ∨ rsState8.swap ∈ C →
        ¬ (bpaGraph rsSubst).StrictClosed C := by
  have c78 : (bpaGraph rsSubst).child rsState7 rsState8.swap :=
    ⟨by decide, show _ ∈ _ by decide⟩
  have c8 : (bpaGraph rsSubst).child rsState8 ([2], [2]) := ⟨by decide, show _ ∈ _ by decide⟩
  have c8' : (bpaGraph rsSubst).child rsState8.swap ([2], [2]) :=
    ⟨by decide, show _ ∈ _ by decide⟩
  refine ⟨c78, c8, c8', fun C hC hS => ?_⟩
  have h22 : ([2], [2]) ∈ C := by
    rcases hC with h7 | h8 | h8'
    · exact hS.closed (hS.closed h7 c78) c8'
    · exact hS.closed h8 c8
    · exact hS.closed h8' c8'
  exact hS.strict _ h22 rfl

/-! ### 3. Non-Pisot strict `1/012/1`: accepted, the square is blind to the spectrum -/

/-- **The incidence matrix of `1/012/1` has the integer eigenvectors `(1,2,1)`, `(1,-1,1)`,
`(1,0,-1)` with eigenvalues `2`, `-1`, `0`**, so its characteristic polynomial is
`x(x - 2)(x + 1) = x³ - x² - 2x`: reducible, with the root `-1` of modulus one, hence not the
characteristic polynomial of an irreducible Pisot substitution. -/
theorem np_incidence_eigen :
    (fun a => ∑ c, (inc NonPisot.table.s a c : ℤ) * ![1, 2, 1] c) = ![2, 4, 2] ∧
      (fun a => ∑ c, (inc NonPisot.table.s a c : ℤ) * ![1, -1, 1] c) = ![-1, 1, -1] ∧
      (fun a => ∑ c, (inc NonPisot.table.s a c : ℤ) * ![1, 0, -1] c) = ![0, 0, 0] := by
  decide +kernel

/-- The seed `(02, 20)` (state 1 of the non-Pisot table). -/
def npSeed : List (Fin 3) × List (Fin 3) := ([0, 2], [2, 0])

/-- The seed is a noncoincident listed state; root row 7 is its root reading at `(1, 1)`; its
star has the entry `(0,0) -> 21`; row 21 has `success = true`; the table has 4 states, 46 rows,
12 root rows, 82 listed edges and 82 split entries, and row 21 is its only success. -/
theorem np_rows :
    NonPisot.table.states[1]? = some npSeed ∧
      NonPisot.table.decodeAt 7 = some ⟨npSeed, 1, 1, none⟩ ∧
      StarRow.child 0 0 21 ∈ NonPisot.table.stars.getD 7 [] ∧
      (NonPisot.table.packets[21]?.map (·.success)) = some true ∧
      NonPisot.table.states.length = 4 ∧ NonPisot.table.packets.length = 46 ∧
      rootCount NonPisot.table = 12 ∧ edgeCount NonPisot.table = 82 ∧
      splitCount NonPisot.table = 82 ∧
      ((List.range 46).filter fun i =>
        (NonPisot.table.packets[i]?.map (·.success)) == some true) = [21] := by
  decide +kernel

/-- The seed `(02, 20)` is a noncoincident listed state of the non-Pisot table. -/
theorem np_seed_listed : npSeed ∈ NonPisot.table.states ∧ npSeed.1 ≠ npSeed.2 :=
  ⟨List.mem_of_getElem? np_rows.1, by decide⟩

/-- The seed is balanced. -/
theorem np_seed_bal : Equiv1 npSeed.1 npSeed.2 := (seed_isBlock (by decide : (0 : Fin 3) ≠ 2)).2.1

/-- The root element of the universe of the seed at `(1, 1)`. -/
def npU7 : Universe NonPisot.table.s npSeed :=
  ⟨rootAnchored NonPisot.table.s np_seed_bal 1 1,
    rootAnchored_mem NonPisot.table.s np_seed_bal (by decide) (by decide)⟩

/-- **The square accepts and transfers readings on a substitution outside the Pisot class.**
The table of `1/012/1` is accepted (`NonPisot.accepted`, a theorem of the data module), and the
headline square applies to it with no further hypothesis: the root element `npU7` of the
universe of `(02, 20)` has packet row 7, which reaches the success row 21; through
`packet_square_readings_for` and `packet_square_readings`, `npU7` is productive for the success
target and for the coincidence target.  The rejection of this specimen happens only at the
Pisot hypothesis (`np_incidence_eigen`), which the square does not read. -/
theorem np_square_blind :
    universePacket NonPisot.table NonPisot.accepted np_seed_listed.1 np_seed_listed.2 npU7 =
        ⟨7, by decide +kernel⟩ ∧
      NonPisot.table.graphSuccess.Productive ⟨7, by decide +kernel⟩ ∧
      (universeGraphFor NonPisot.table.s npSeed NonPisot.table.target).Productive npU7 ∧
      (universeGraph NonPisot.table.s npSeed).Productive npU7 := by
  obtain ⟨-, d7, m21, s21, -⟩ := np_rows
  have p7 := (universePacket_eq_iff NonPisot.table NonPisot.accepted np_seed_listed.1
    np_seed_listed.2 npU7 ⟨7, by decide +kernel⟩).2 (occAt_of_decodeAt d7)
  have hprod : NonPisot.table.graphSuccess.Productive ⟨7, by decide +kernel⟩ := by
    refine ⟨⟨21, by decide +kernel⟩, .single ⟨0, 0, m21⟩, ?_⟩
    change (NonPisot.table.packets[21]).success = true
    have : NonPisot.table.packets[21]? = some (NonPisot.table.packets[21]) :=
      List.getElem?_eq_getElem (by decide +kernel)
    rw [this] at s21
    simpa using s21
  have hprod' : (universeGraphFor NonPisot.table.s npSeed NonPisot.table.target).Productive npU7 :=
    (packet_square_readings_for NonPisot.table NonPisot.accepted np_seed_listed.1
      np_seed_listed.2 npU7).1.2 (p7 ▸ hprod)
  have hprodC : NonPisot.table.graph.Productive ⟨7, by decide +kernel⟩ := by
    obtain ⟨j, hj, ht⟩ := hprod
    exact ⟨j, hj, (Table.targets NonPisot.table NonPisot.accepted j).1.2
      (occGraphFor_target_le _ _ _ ((Table.targets NonPisot.table NonPisot.accepted j).2.1 ht))⟩
  exact ⟨p7, hprod, hprod', (packet_square_readings NonPisot.table NonPisot.accepted
    np_seed_listed.1 np_seed_listed.2 npU7).1.2 (p7 ▸ hprodC)⟩

/-! ### 4. The strong G/F template of `1/2/021`: refused at the literal factorisation -/

/-- The actual closure of `1/2/021` is accepted (`GfActual.accepted`, a theorem of the data
module); its shape: 8 states, 12 factor rows, 153 rows, 39 root rows, 235 listed edges, 220
split entries. -/
theorem gf_actual_shape :
    GfActual.table.states.length = 8 ∧ GfActual.table.factors.length = 12 ∧
      GfActual.table.packets.length = 153 ∧ rootCount GfActual.table = 39 ∧
      edgeCount GfActual.table = 235 ∧ splitCount GfActual.table = 220 := by
  decide +kernel

/-- First template state `(021, 120)`. -/
def gfT0 : List (Fin 3) × List (Fin 3) := ([0, 2, 1], [1, 2, 0])

/-- Second template state `(10122, 20121)`. -/
def gfT1 : List (Fin 3) × List (Fin 3) := ([1, 0, 1, 2, 2], [2, 0, 1, 2, 1])

/-- Third template state `(011202221, 201221102)`. -/
def gfT2 : List (Fin 3) × List (Fin 3) :=
  ([0, 1, 1, 2, 0, 2, 2, 2, 1], [2, 0, 1, 2, 2, 1, 1, 0, 2])

/-- **The literal ordered factorisation of the three template states.**  The substitution of
the committed table is `1/2/021`; the three states are irreducible blocks in normalised
orientation; the literal factorisation of their images has `1`, `2`, `5` blocks (the template
proposes `1`, `1`, `3` children); the one block of the image of the first state is
`(10212, 20211)`, in normalised orientation, where the template names `(10122, 20121)`; and the
image of the third state has the diagonal block `(2, 2)`. -/
theorem gf_template_literal :
    GfActual.table.s = ![[1], [2], [0, 2, 1]] ∧
      IsBlock gfT0 ∧ IsBlock gfT1 ∧ IsBlock gfT2 ∧
      isNormal gfT0.1 gfT0.2 = true ∧ isNormal gfT1.1 gfT1.2 = true ∧
      isNormal gfT2.1 gfT2.2 = true ∧
      (literalFactors GfActual.table.s gfT0).length = 1 ∧
      (literalFactors GfActual.table.s gfT1).length = 2 ∧
      (literalFactors GfActual.table.s gfT2).length = 5 ∧
      ([2], [2]) ∈ red (subst GfActual.table.s gfT2.1) (subst GfActual.table.s gfT2.2) ∧
      literalFactors GfActual.table.s gfT0 =
        [(some ([1, 0, 2, 1, 2], [2, 0, 2, 1, 1]), true, 0, 0, 5, 5)] := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **Any table over `1/2/021` that lists a template state with the template's child count is
refused by the factor clause**: if `gfT1` is listed with a number of factor rows other than `2`
(the template proposes `1`), or `gfT2` with a number other than `5` (the template proposes `3`),
`factorsOK` refuses, whatever the rows say. -/
theorem gf_template_refused (t : Table (Fin 3)) (hs : t.s = GfActual.table.s) {i : ℕ} :
    (t.states[i]? = some gfT1 → (t.factors.filter fun f => f.parent = i).length ≠ 2 →
        t.factorsOK = false) ∧
      (t.states[i]? = some gfT2 → (t.factors.filter fun f => f.parent = i).length ≠ 5 →
        t.factorsOK = false) := by
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, -, -⟩ := gf_template_literal
  refine ⟨fun hT hl => factorsOK_eq_false_of_length t hT (by decide) ?_,
    fun hT hl => factorsOK_eq_false_of_length t hT (by decide) ?_⟩
  · rwa [hs, h1]
  · rwa [hs, h2]

/-- The committed `1/2/021` table extended by the three template states (indices 8, 9, 10) with
the template's factor rows: `8 ↦ 9`, `9 ↦ 10` (side-swapped), `10 ↦ 8, 9, 10` (signs
`-, +, -`), with block bounds that tile the images (lengths 5, 9, 17).  No packet row is added. -/
def gfTemplate : Table (Fin 3) :=
  { GfActual.table with
    states := GfActual.table.states ++ [gfT0, gfT1, gfT2]
    factors := GfActual.table.factors ++ [⟨8, 0, 9, true, 0, 5, 5⟩,
      ⟨9, 0, 10, false, 0, 9, 9⟩, ⟨10, 0, 8, false, 0, 3, 17⟩, ⟨10, 1, 9, true, 3, 8, 17⟩,
      ⟨10, 2, 10, false, 8, 17, 17⟩] }

/-- **Each template state alone refuses the factor clause** (`factorsOK_eq_false_of_ne`).
The states 0-7 of `gfTemplate` keep the factor rows of the accepted `GfActual.table`.  At state
8 `(021, 120)` the counts agree (one row, one literal block) and the contents differ: the
template row names `gfT1 = (10122, 20121)`, the literal block is `(10212, 20211)`.  At state 9
the template has one row against two literal blocks, at state 10 three against five. -/
theorem gf_template_states_refused :
    (∀ i < 8, factorTuples gfTemplate i = factorTuples GfActual.table i) ∧
      gfTemplate.states[8]? = some gfT0 ∧ gfTemplate.states[9]? = some gfT1 ∧
      gfTemplate.states[10]? = some gfT2 ∧
      factorTuples gfTemplate 8 = [(some gfT1, true, 0, 0, 5, 5)] ∧
      literalFactors gfTemplate.s gfT0 =
        [(some ([1, 0, 2, 1, 2], [2, 0, 2, 1, 1]), true, 0, 0, 5, 5)] ∧
      (factorTuples gfTemplate 9).length = 1 ∧ (literalFactors gfTemplate.s gfT1).length = 2 ∧
      (factorTuples gfTemplate 10).length = 3 ∧ (literalFactors gfTemplate.s gfT2).length = 5 ∧
      (∀ i ∈ [8, 9, 10], ∃ T, gfTemplate.states[i]? = some T ∧ T.1 ≠ T.2 ∧
        factorTuples gfTemplate i ≠ literalFactors gfTemplate.s T ∧
        gfTemplate.factorsOK = false) := by
  have hv : (∀ i < 8, factorTuples gfTemplate i = factorTuples GfActual.table i) ∧
      gfTemplate.states[8]? = some gfT0 ∧ gfTemplate.states[9]? = some gfT1 ∧
      gfTemplate.states[10]? = some gfT2 ∧
      factorTuples gfTemplate 8 = [(some gfT1, true, 0, 0, 5, 5)] ∧
      literalFactors gfTemplate.s gfT0 =
        [(some ([1, 0, 2, 1, 2], [2, 0, 2, 1, 1]), true, 0, 0, 5, 5)] ∧
      (factorTuples gfTemplate 9).length = 1 ∧ (literalFactors gfTemplate.s gfT1).length = 2 ∧
      (factorTuples gfTemplate 10).length = 3 ∧ (literalFactors gfTemplate.s gfT2).length = 5 := by
    refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · interval_cases i <;> decide +kernel
    all_goals decide +kernel
  obtain ⟨h07, s8, s9, s10, f8, l8, f9, l9, f10, l10⟩ := hv
  have n8 : factorTuples gfTemplate 8 ≠ literalFactors gfTemplate.s gfT0 := by
    rw [f8, l8]
    decide
  have n9 : factorTuples gfTemplate 9 ≠ literalFactors gfTemplate.s gfT1 := fun h => by
    have := congrArg List.length h
    rw [f9, l9] at this
    exact absurd this (by decide)
  have n10 : factorTuples gfTemplate 10 ≠ literalFactors gfTemplate.s gfT2 := fun h => by
    have := congrArg List.length h
    rw [f10, l10] at this
    exact absurd this (by decide)
  refine ⟨h07, s8, s9, s10, f8, l8, f9, l9, f10, l10, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact ⟨gfT0, s8, by decide, n8, factorsOK_eq_false_of_ne _ s8 (by decide) n8⟩
  · exact ⟨gfT1, s9, by decide, n9, factorsOK_eq_false_of_ne _ s9 (by decide) n9⟩
  · exact ⟨gfT2, s10, by decide, n10, factorsOK_eq_false_of_ne _ s10 (by decide) n10⟩

/-- **The template table is refused, first at the factor clause (L3)**: its letters, states
and seeds pass; the factor clause refuses, at each of the three template states
(`gf_template_states_refused`: at `(021, 120)` on the content of its one block, at the other
two on the block counts); the root clause refuses too, because no root row was written for the
three template states; every other clause passes.  The second refusal is not a careless
mutation: a concrete table that lists the template states with their root rows and keeps the
template's factor rows as their only factor rows cannot pass the star clause.  The image of
`(021, 120)` is one block, so every digit pair of a root reading of it gives a child entry,
whose destination row decodes through a factor row of that state, hence to a block
`gfT1 = (10122, 20121)` or its swap instead of the literal `(10212, 20211)`.  The isolated
L3 refusals are the general `gf_template_refused` and `gf_template_states_refused`. -/
theorem gf_template_table_refused :
    gfTemplate.check = false ∧
      gfTemplate.clauses = [true, true, true, false, true, false, true, true, true, true, true] ∧
      gfTemplate.states[10]? = some gfT2 ∧
      (gfTemplate.factors.filter fun f => f.parent = 10).length = 3 := by
  have hc : gfTemplate.clauses =
      [true, true, true, false, true, false, true, true, true, true, true] := by decide +kernel
  refine ⟨by rw [Table.check_eq_clauses, hc]; rfl, hc, by decide +kernel, by decide +kernel⟩

/-! ### 5. The seed `(01, 10)` of `1/02/202`: no success at depth one, success at depth two -/

/-- Row 2 of the real-secondary table. -/
def rsRow2 : Fin RealSecondary.table.packets.length := ⟨2, by decide +kernel⟩

/-- Row 124 of the real-secondary table. -/
def rsRow124 : Fin RealSecondary.table.packets.length := ⟨124, by decide +kernel⟩

/-- Row 346 of the real-secondary table. -/
def rsRow346 : Fin RealSecondary.table.packets.length := ⟨346, by decide +kernel⟩

/-- Rows 0-3 are the root readings of the seed (row `r` at `(r / 2, r % 2)`); no child entry
of rows 0-3 names a row with `success = true`; row 2 has `(1,1) -> 124`, row 124 has
`(0,2) -> 346`, and row 346 has `success = true`. -/
theorem rs_seed_rows :
    (∀ r < 4, RealSecondary.table.decodeAt r = some ⟨rsSeed, r / 2, r % 2, none⟩) ∧
      ((List.range 4).all fun r => (RealSecondary.table.stars.getD r []).all fun e =>
        match e with
        | .child _ _ j => (RealSecondary.table.packets[j]?.map (·.success)) == some false
        | .split .. => true) = true ∧
      StarRow.child 1 1 124 ∈ RealSecondary.table.stars.getD 2 [] ∧
      StarRow.child 0 2 346 ∈ RealSecondary.table.stars.getD 124 [] ∧
      (RealSecondary.table.packets[346]?.map (·.success)) = some true := by
  decide +kernel

/-- **No success at depth one, at the absolute level.**  Every retained child of an element of
the universe of the seed at level 0 is not a packet success (success-target transfer: its
packet is a listed child of a root row 0-3, `packet_square`, and none of those is a success). -/
theorem rs_depth_one_no_success (a b : Universe RealSecondary.table.s rsSeed)
    (ha : a.1.1.1.level = 0) (hab : (universeGraph RealSecondary.table.s rsSeed).child a b) :
    ¬ (universeGraphFor RealSecondary.table.s rsSeed RealSecondary.table.target).target b := by
  obtain ⟨hroots, hno, -⟩ := rs_seed_rows
  have hR := (packet_square RealSecondary.table RealSecondary.accepted rs_seed_listed.1
    rs_seed_listed.2).2
  obtain ⟨h1, hP, hQ⟩ := universe_level_zero a.2 ha
  have hP' : a.1.1.1.top < 2 := hP
  have hQ' : a.1.1.1.bot < 2 := hQ
  set r := 2 * a.1.1.1.top + a.1.1.1.bot with hr
  have hr4 : r < 4 := by omega
  have hdec := hroots r hr4
  have hr2 : r / 2 = a.1.1.1.top := by omega
  have hr2' : r % 2 = a.1.1.1.bot := by omega
  rw [hr2, hr2'] at hdec
  have hrl : r < RealSecondary.table.packets.length := Table.lt_of_decodeAt hdec
  have hpa : universePacket RealSecondary.table RealSecondary.accepted rs_seed_listed.1
      rs_seed_listed.2 a = ⟨r, hrl⟩ :=
    (universePacket_eq_iff _ _ _ _ a ⟨r, hrl⟩).2 ((occAt_of_decodeAt hdec).trans h1.symm)
  intro hb
  have hc := hR.complete hab
  rw [hpa] at hc
  obtain ⟨d, e, hm⟩ := hc
  have ht := hR.targetDown b hb
  obtain ⟨j, hjeq⟩ : ∃ j, universePacket RealSecondary.table RealSecondary.accepted
      rs_seed_listed.1 rs_seed_listed.2 b = j := ⟨_, rfl⟩
  rw [hjeq] at hm ht
  change (RealSecondary.table.packets[j]).success = true at ht
  have hrr := List.all_eq_true.1 hno r (List.mem_range.2 hr4)
  have hj := List.all_eq_true.1 hrr _ hm
  simp only at hj
  rw [List.getElem?_eq_getElem j.2] at hj
  simp only [Fin.getElem_fin] at ht
  simp [ht] at hj

/-- The root element of the universe of the seed at `(1, 0)`. -/
def rsU10 : Universe RealSecondary.table.s rsSeed :=
  ⟨rootAnchored RealSecondary.table.s rs_seed_isBlock.2.1 1 0,
    rootAnchored_mem RealSecondary.table.s rs_seed_isBlock.2.1 (by decide) (by decide)⟩

/-- **Success at depth two, at the absolute level.**  The root element at `(1, 0)` has packet
row 2, the packet path `2 -(1,1)-> 124 -(0,2)-> 346` ends at a success, and through
`packet_square_readings_for` the root element is productive for the success target: some
retained absolute lineage of the iterates of `(01, 10)` reaches a strictly interior
coincidence. -/
theorem rs_depth_two_success :
    universePacket RealSecondary.table RealSecondary.accepted rs_seed_listed.1 rs_seed_listed.2
        rsU10 = rsRow2 ∧
      RealSecondary.table.graph.child rsRow2 rsRow124 ∧
      RealSecondary.table.graph.child rsRow124 rsRow346 ∧
      RealSecondary.table.graphSuccess.target rsRow346 ∧
      RealSecondary.table.graphSuccess.Productive rsRow2 ∧
      (universeGraphFor RealSecondary.table.s rsSeed RealSecondary.table.target).Productive
        rsU10 := by
  obtain ⟨hroots, -, m1, m2, s346⟩ := rs_seed_rows
  have p2 := (universePacket_eq_iff RealSecondary.table RealSecondary.accepted rs_seed_listed.1
    rs_seed_listed.2 rsU10 rsRow2).2 (occAt_of_decodeAt (hroots 2 (by decide)))
  have c1 : RealSecondary.table.graph.child rsRow2 rsRow124 := ⟨1, 1, m1⟩
  have c2 : RealSecondary.table.graph.child rsRow124 rsRow346 := ⟨0, 2, m2⟩
  have t346 : RealSecondary.table.graphSuccess.target rsRow346 := by
    change (RealSecondary.table.packets[rsRow346]).success = true
    have : RealSecondary.table.packets[346]? = some (RealSecondary.table.packets[rsRow346]) :=
      List.getElem?_eq_getElem rsRow346.2
    rw [this] at s346
    simpa using s346
  have hprod : RealSecondary.table.graphSuccess.Productive rsRow2 :=
    ⟨rsRow346, (Relation.ReflTransGen.single c1).tail c2, t346⟩
  exact ⟨p2, c1, c2, t346, hprod, (packet_square_readings_for RealSecondary.table
    RealSecondary.accepted rs_seed_listed.1 rs_seed_listed.2 rsU10).1.2 (p2 ▸ hprod)⟩

/-- Row 154 of the real-secondary table with its `success` bit set. -/
def rsSuccess154 : Table (Fin 3) :=
  { RealSecondary.table with
    packets := RealSecondary.table.packets.modify 154 fun p => { p with success := true } }

/-- **Matching letters at a nonzero residual are not a success.**  Row 154 carries the letters
`(2, 2)` and the residual `(-1, 1, 0)`, and its `success` bit is `false`; with the bit set, the
table is refused by the row clause (L4) only. -/
theorem rs_matching_letters_refused :
    (RealSecondary.table.packets[154]?.map fun p => (p.letters, p.residual, p.success)) =
        some ((2, 2), [-1, 1, 0], false) ∧
      rsSuccess154.check = false ∧
      rsSuccess154.clauses =
        [true, true, true, true, true, true, true, true, false, true, true] := by
  have hc : rsSuccess154.clauses =
      [true, true, true, true, true, true, true, true, false, true, true] := by decide +kernel
  exact ⟨by decide +kernel, by rw [Table.check_eq_clauses, hc]; rfl, hc⟩

/-! ### 6. Mutation controls replayed on exported tables

Each control replays the recipe of a Fibonacci control of `Psc.PacketCertificate` on a table
emitted by the Mojo exporter over the three-letter alphabet (`fibTable` is a hand-written
`Fin 2` table), and states the full clause vector (`Table.clauses`: letters, states, seeds,
factors, keys, roots, births, star count, rows, stars, hubs).  They add that the refusing
clauses are the same on exporter output, and, for the side swap, the duplicate and the forged
row, that the refusal holds for every key order or every birth record; the Fibonacci
counterpart is named in each docstring.  `fib_duplicate_key` (a copied row that no star names)
is not replayed; its isolated variant is (`np_duplicate_isolated`). -/

/-- Row 0 without its split entry `(0,2)`. -/
def npDroppedSplit : Table (Fin 3) :=
  { NonPisot.table with stars := NonPisot.table.stars.set 0 [.child 0 0 12, .child 0 1 13] }

/-- **A dropped split entry is refused by the star clause (L5) only** (the recipe of
`fib_dropped_split`). -/
theorem np_dropped_split :
    NonPisot.table.stars.getD 0 [] = [.child 0 0 12, .child 0 1 13, .split 0 2 0 1] ∧
      npDroppedSplit.check = false ∧
      npDroppedSplit.clauses =
        [true, true, true, true, true, true, true, true, true, false, true] := by
  have hc : npDroppedSplit.clauses =
      [true, true, true, true, true, true, true, true, true, false, true] := by decide +kernel
  exact ⟨by decide +kernel, by rw [Table.check_eq_clauses, hc]; rfl, hc⟩

/-- Row 12 (state 0 read side-swapped, born as ordinal 0 of root row 0) with the other
orientation bit. -/
def npSideSwapped : Table (Fin 3) :=
  { NonPisot.table with
    packets := NonPisot.table.packets.modify 12 fun p => { p with sign := true } }

/-- **A side-swapped row is refused** by the key, row and star clauses (L6, L4, L5; the recipe
of `fib_side_swapped`).  Row 12 is `(state 0, -, 0, 0, factor 0)`; with the other orientation
its key becomes that of row 30, `(state 0, +, 0, 0, factor 0)` (born from row 12), so the key
clause refuses it whatever the key order (`keysOK_eq_false_of_keyCode_eq`).  The row clause
refuses at row 12 only, on its letters: the row carries `(1, 0)`, and its pair now reads
`(0, 1)` (its addresses and residual still agree).  The star equation fails at row 12 itself
and at every row whose star names it: row 0 (its parent) and rows 22 and 30. -/
theorem np_side_swapped :
    npSideSwapped.check = false ∧
      npSideSwapped.clauses =
        [true, true, true, true, false, true, true, true, false, false, true] ∧
      (NonPisot.table.packets[12]?.map fun p => (p.state, p.sign, p.top, p.bot, p.factor)) =
        some (0, false, 0, 0, some 0) ∧
      (NonPisot.table.packets[30]?.map fun p => (p.state, p.sign, p.top, p.bot, p.factor)) =
        some (0, true, 0, 0, some 0) ∧
      npSideSwapped.packets[12]?.map npSideSwapped.keyCode =
        npSideSwapped.packets[30]?.map npSideSwapped.keyCode ∧
      (∀ ko : List ℕ, ({ npSideSwapped with keyOrder := ko } : Table (Fin 3)).keysOK = false) ∧
      (List.range 46).filter (fun i => !packetOKAt npSideSwapped i) = [12] ∧
      (npSideSwapped.packets[12]?.map (·.letters)) = some (1, 0) ∧
      ((npSideSwapped.decodeAt 12).map fun x => (x.block.1[x.top]?, x.block.2[x.bot]?)) =
        some (some 0, some 1) ∧
      (List.range 46).filter (fun i => !starOKAt npSideSwapped i) = [0, 12, 22, 30] := by
  have hc : npSideSwapped.clauses =
      [true, true, true, true, false, true, true, true, false, false, true] := by decide +kernel
  have hv : (NonPisot.table.packets[12]?.map fun p => (p.state, p.sign, p.top, p.bot, p.factor)) =
        some (0, false, 0, 0, some 0) ∧
      (NonPisot.table.packets[30]?.map fun p => (p.state, p.sign, p.top, p.bot, p.factor)) =
        some (0, true, 0, 0, some 0) ∧
      npSideSwapped.packets[12]?.map npSideSwapped.keyCode =
        npSideSwapped.packets[30]?.map npSideSwapped.keyCode ∧
      (List.range 46).filter (fun i => !packetOKAt npSideSwapped i) = [12] ∧
      (npSideSwapped.packets[12]?.map (·.letters)) = some (1, 0) ∧
      ((npSideSwapped.decodeAt 12).map fun x => (x.block.1[x.top]?, x.block.2[x.bot]?)) =
        some (some 0, some 1) ∧
      (List.range 46).filter (fun i => !starOKAt npSideSwapped i) = [0, 12, 22, 30] := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  obtain ⟨v12, v30, hk, hrow, hl1, hl2, hstar⟩ := hv
  have h12 : 12 < npSideSwapped.packets.length := by decide +kernel
  have h30 : 30 < npSideSwapped.packets.length := by decide +kernel
  exact ⟨by rw [Table.check_eq_clauses, hc]; rfl, hc, v12, v30, hk,
    fun ko => keysOK_eq_false_of_keyCode_eq { npSideSwapped with keyOrder := ko } (by decide)
      h12 h30 hk, hrow, hl1, hl2, hstar⟩

/-- The table of `fib_side_swapped`: row 6 of `fibTable` with the other orientation bit. -/
def fibSideSwapped : Table (Fin 2) :=
  { fibTable with packets := fibTable.packets.modify 6 fun p => { p with sign := true } }

/-- **The key refusal of `fib_side_swapped` is a collision too**: row 6 of `fibTable` is
`(state 0, -, 0, 1, factor 1)`; with the other orientation its key is that of row 12,
`(state 0, +, 0, 1, factor 1)`, so the key clause refuses it whatever the key order. -/
theorem fib_side_swapped_collision :
    fibSideSwapped.packets[6]?.map fibSideSwapped.keyCode =
        fibSideSwapped.packets[12]?.map fibSideSwapped.keyCode ∧
      ∀ ko : List ℕ, ({ fibSideSwapped with keyOrder := ko } : Table (Fin 2)).keysOK = false := by
  have hk : fibSideSwapped.packets[6]?.map fibSideSwapped.keyCode =
      fibSideSwapped.packets[12]?.map fibSideSwapped.keyCode := by decide
  have h6 : 6 < fibSideSwapped.packets.length := by decide
  have h12 : 12 < fibSideSwapped.packets.length := by decide
  exact ⟨hk, fun ko => keysOK_eq_false_of_keyCode_eq { fibSideSwapped with keyOrder := ko }
    (by decide) h6 h12 hk⟩

/-- Hub row 0 with its undefined slot coerced to `some false`. -/
def npHubCoerced : Table (Fin 3) :=
  { NonPisot.table with
    hubs := NonPisot.table.hubs.modify 0 fun r =>
      { r with bits := r.bits.map fun b => some (b.getD false) } }

/-- **A coerced undefined hub bit is refused by the hub clause (L7) only** (the recipe of
`fib_hub_coerced`). -/
theorem np_hub_coerced :
    (NonPisot.table.hubs[0]?.map (·.bits)) = some [some true, none] ∧
      npHubCoerced.check = false ∧
      npHubCoerced.clauses =
        [true, true, true, true, true, true, true, true, true, true, false] := by
  have hc : npHubCoerced.clauses =
      [true, true, true, true, true, true, true, true, true, true, false] := by decide +kernel
  exact ⟨by decide +kernel, by rw [Table.check_eq_clauses, hc]; rfl, hc⟩

/-- Row 12 duplicated as row 46, born from row 22: row 22's `(0,0)` child entry, which named
row 12, is repointed to row 46; row 46 carries the birth `(22, 0, 0)` and the star of row 12;
its key-order entry follows that of row 12. -/
def npDuplicate : Table (Fin 3) :=
  { NonPisot.table with
    packets := NonPisot.table.packets ++
      ((NonPisot.table.packets.drop 12).take 1).map fun p => { p with birth := some (22, 0, 0) }
    stars := NonPisot.table.stars.set 22 [.child 0 0 46, .child 0 1 13, .split 0 2 0 1] ++
      [NonPisot.table.stars.getD 12 []]
    keyOrder := NonPisot.table.keyOrder.take 1 ++ [46] ++ NonPisot.table.keyOrder.drop 1 }

/-- **A duplicated row is refused by the key clause (L6) alone** (the recipe of
`fib_duplicate_isolated`): row 12 has the incoming entries `(0,0)` of rows 0 (its birth), 22
and 30; with the second repointed to the copy, every other clause, the star and birth clauses
included, accepts the table.  Rows 12 and 46 decode to one occurrence pair, so no key order
passes the key clause (`keysOK_eq_false_of_keyCode_eq`). -/
theorem np_duplicate_isolated :
    NonPisot.table.stars.getD 22 [] = [.child 0 0 12, .child 0 1 13, .split 0 2 0 1] ∧
      (NonPisot.table.packets[12]?.map (·.birth)) = some (some (0, 0, 0)) ∧
      StarRow.child 0 0 12 ∈ NonPisot.table.stars.getD 30 [] ∧
      npDuplicate.check = false ∧
      npDuplicate.clauses =
        [true, true, true, true, false, true, true, true, true, true, true] ∧
      npDuplicate.decodeAt 12 = npDuplicate.decodeAt 46 ∧
      (npDuplicate.decodeAt 12).isSome = true ∧
      ∀ ko : List ℕ, ({ npDuplicate with keyOrder := ko } : Table (Fin 3)).keysOK = false := by
  have hc : npDuplicate.clauses =
      [true, true, true, true, false, true, true, true, true, true, true] := by decide +kernel
  have hv : NonPisot.table.stars.getD 22 [] = [.child 0 0 12, .child 0 1 13, .split 0 2 0 1] ∧
      (NonPisot.table.packets[12]?.map (·.birth)) = some (some (0, 0, 0)) ∧
      StarRow.child 0 0 12 ∈ NonPisot.table.stars.getD 30 [] ∧
      npDuplicate.decodeAt 12 = npDuplicate.decodeAt 46 ∧
      (npDuplicate.decodeAt 12).isSome = true ∧
      npDuplicate.packets[12]?.map npDuplicate.keyCode =
        npDuplicate.packets[46]?.map npDuplicate.keyCode := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  obtain ⟨v22, v12, v30, hd, hs, hk⟩ := hv
  have h12 : 12 < npDuplicate.packets.length := by decide +kernel
  have h46 : 46 < npDuplicate.packets.length := by decide +kernel
  exact ⟨v22, v12, v30, by rw [Table.check_eq_clauses, hc]; rfl, hc, hd, hs,
    fun ko => keysOK_eq_false_of_keyCode_eq { npDuplicate with keyOrder := ko } (by decide)
      h12 h46 hk⟩

/-- **Without `keysOK`, `occAt` is not injective** on `npDuplicate` (the recipe of
`fib_duplicate_not_injective`), which passes the other ten clauses: rows 12 and 46 have the
same occurrence pair. -/
theorem np_duplicate_not_injective : ¬ Function.Injective npDuplicate.occAt := by
  intro h
  have hl : 46 < npDuplicate.packets.length := by decide +kernel
  have h12 : npDuplicate.occAt ⟨12, by omega⟩ = npDuplicate.occAt ⟨46, hl⟩ := by
    unfold Table.occAt
    rw [np_duplicate_isolated.2.2.2.2.2.1]
  have := congrArg Fin.val (h h12)
  simp at this

/-- Row 13 with the global position of its top address replaced by `99`. -/
def npWrongGlobal : Table (Fin 3) :=
  { NonPisot.table with
    packets := NonPisot.table.packets.modify 13 fun p =>
      { p with topAddr := p.topAddr.map fun (a, b, _, d) => (a, b, 99, d) } }

/-- **A wrong global position is refused by the row clause (L4) only** (the recipe of
`fib_wrong_global`). -/
theorem np_wrong_global :
    npWrongGlobal.check = false ∧
      npWrongGlobal.clauses =
        [true, true, true, true, true, true, true, true, false, true, true] := by
  have hc : npWrongGlobal.clauses =
      [true, true, true, true, true, true, true, true, false, true, true] := by decide +kernel
  exact ⟨by rw [Table.check_eq_clauses, hc]; rfl, hc⟩

/-! #### A forged unreachable row on `1/02/202`

The recipe of `fibExtra_forged_*` without an extra state.  Row 147 of the real-secondary table
is the success `(state 5 = (2, 2), +, 0, 0, factor 3)`: the coincidence born as ordinal 1 of
the seed `(12, 21)` (state 2, through factor row 3).  Its mirror `(5, -, 0, 0, factor 3)`
decodes to the same coincidence born as ordinal 1 of the swapped seed `(21, 12)`, a valid
occurrence pair; no row of the table reads state 2 side-swapped, and the pair is the
occurrence pair of no row, hence (`Table.range_eq_reach`) it is reachable from no root pair of
a noncoincident listed state.  `rsForged b` adds it as row 507 with its literal fields, its
literal star (empty, at a coincidence), a key-order entry at its place (position 70) and the
birth record `b`. -/

/-- The occurrence pair of the forged row. -/
def rsForgedPair : Occ (Fin 3) := ⟨([2], [2]), 0, 0, some ⟨([2, 1], [1, 2]), 1⟩⟩

/-- The forged row: `(state 5, -, 0, 0, factor 3)` with the literal fields of `rsForgedPair`
and the birth record `b`. -/
def rsForgedRow (b : Option (ℕ × ℕ × ℕ)) : PacketRow (Fin 3) :=
  ⟨5, false, 0, 0, some 3, some (0, 2, 2, 0), some (1, 0, 2, 0), (2, 2), [0, 0, 0], true, true,
    b⟩

/-- The real-secondary table with the forged row 507 and the birth record `b`. -/
def rsForged (b : Option (ℕ × ℕ × ℕ)) : Table (Fin 3) :=
  { RealSecondary.table with
    packets := RealSecondary.table.packets ++ [rsForgedRow b]
    stars := RealSecondary.table.stars ++ [[]]
    keyOrder := RealSecondary.table.keyOrder.take 70 ++ [507] ++
      RealSecondary.table.keyOrder.drop 70 }

/-- The forged row decodes to `rsForgedPair`, a valid occurrence pair, strictly interior and a
success for the table's target; its literal star is empty; row 147 is its normalised sibling;
no row of the table reads state 2 side-swapped; and `rsForgedPair` is the occurrence pair of no
row of the accepted real-secondary table. -/
theorem rs_forged_outside :
    (rsForged none).decodeAt 507 = some rsForgedPair ∧ rsForgedPair.Valid rsSubst ∧
      rsForgedPair.Interior ∧ rsForgedPair.SuccessFor RealSecondary.table.target ∧
      occStar rsSubst rsForgedPair = [] ∧
      (RealSecondary.table.packets[147]?.map fun p => (p.state, p.sign, p.top, p.bot, p.factor)) =
        some (5, true, 0, 0, some 3) ∧
      (RealSecondary.table.packets[147]?.map (·.success)) = some true ∧
      RealSecondary.table.states[2]? = some ([1, 2], [2, 1]) ∧
      RealSecondary.table.packets.all (fun p => !(p.state == 2 && !p.sign)) = true ∧
      ∀ i, RealSecondary.table.occAt i ≠ rsForgedPair := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **The forged pair is not reachable** in `occGraph rsSubst` from any root pair of a
noncoincident listed state of the real-secondary table (`Table.range_eq_reach` and
`rs_forged_outside`). -/
theorem rs_forged_not_reached :
    ¬ ∃ T ∈ RealSecondary.table.states, T.1 ≠ T.2 ∧ ∃ P Q, P < T.1.length ∧ Q < T.2.length ∧
      (occGraph rsSubst).Reach ⟨T, P, Q, none⟩ rsForgedPair := by
  intro hx
  have hmem : rsForgedPair ∈ Set.range RealSecondary.table.occAt := by
    rw [Table.range_eq_reach RealSecondary.table RealSecondary.accepted]
    exact hx
  obtain ⟨i, hi⟩ := hmem
  exact rs_forged_outside.2.2.2.2.2.2.2.2.2 i hi

/-- No star of the real-secondary table has a child entry beyond row 506. -/
theorem rs_stars_bounded :
    RealSecondary.table.stars.length = 507 ∧ RealSecondary.table.packets.length = 507 ∧
      (RealSecondary.table.stars.all fun st => st.all fun r =>
        match r with
        | .child _ _ k => decide (k < 507)
        | .split .. => true) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- **The forged unreachable row is refused by the birth clause alone, for every birth
record**: no star names row 507, so `birthOK` refuses `rsForged b` whatever `b` is.  For the
birth `(10, 0, 2)` of row 147 (the forged row claims its sibling's birth) every other clause,
the row and star clauses included, accepts the table; the other ten clauses do not read the
birth field. -/
theorem rs_forged_refused :
    (∀ b, (rsForged b).birthOK = false) ∧
      (RealSecondary.table.packets[147]?.map (·.birth)) = some (some (10, 0, 2)) ∧
      (rsForged (some (10, 0, 2))).check = false ∧
      (rsForged (some (10, 0, 2))).clauses =
        [true, true, true, true, true, true, false, true, true, true, true] := by
  have hc : (rsForged (some (10, 0, 2))).clauses =
      [true, true, true, true, true, true, false, true, true, true, true] := by decide +kernel
  refine ⟨fun b => ?_, by decide +kernel, by rw [Table.check_eq_clauses, hc]; rfl, hc⟩
  obtain ⟨hsl, hpl, hall⟩ := rs_stars_bounded
  rw [Bool.eq_false_iff]
  intro h
  have h507 := List.all_eq_true.1 h 507 (List.mem_range.2 (by simp [rsForged, hpl]))
  have hp : (rsForged b).packets[507]? = some (rsForgedRow b) := by
    simp only [rsForged]
    rw [List.getElem?_append_right (by omega)]
    simp [hpl]
  rw [hp] at h507
  cases b with
  | none => simp [rsForgedRow] at h507
  | some b =>
    obtain ⟨j, d, e⟩ := b
    simp only [rsForgedRow, Bool.and_eq_true, decide_eq_true_eq] at h507
    obtain ⟨hj, hm⟩ := h507
    have hs : (rsForged (some (j, d, e))).stars.getD j [] =
        RealSecondary.table.stars.getD j [] := by
      simp only [rsForged, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rw [hs] at hm
    have hmem : StarRow.child d e 507 ∈ RealSecondary.table.stars.getD j [] :=
      List.contains_iff_mem.1 hm
    have hst : RealSecondary.table.stars.getD j [] ∈ RealSecondary.table.stars := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    have := List.all_eq_true.1 (List.all_eq_true.1 hall _ hst) _ hmem
    simp at this

/-! ### 7. A letter-pair quotient cycle of Tribonacci with no packet cycle over it -/

/-- The labelled 2-cycle `(0,1) -(1,0)-> (1,0) -(0,1)-> (0,1)` of the naive letter-pair quotient
(vertices: pairs of distinct letters; edge `(a,b) -(d,e)-> (σ(a)[d], σ(b)[e])`): the digit pair
it prescribes out of each of its two vertices, `none` elsewhere. -/
def lpLabel : Fin 3 × Fin 3 → Option (ℕ × ℕ)
  | (0, 1) => some (1, 0)
  | (1, 0) => some (0, 1)
  | _ => none

/-- The listed edges out of row `i` that follow the cycle: `i` carries the letters of a vertex
of the cycle and the edge has the digits the cycle prescribes there. -/
def lpSucc (t : Table (Fin 3)) (i : ℕ) : List ℕ :=
  match t.packets[i]?.bind (fun p => lpLabel p.letters) with
  | none => []
  | some (d, e) => (t.stars.getD i []).filterMap fun r =>
      match r with
      | .child d' e' j => if d' = d ∧ e' = e then some j else none
      | .split .. => none

/-- The ends of the packet walks of length `k` over the cycle, from every row carrying the
letters of one of its vertices. -/
def lpWalk (t : Table (Fin 3)) : ℕ → List ℕ
  | 0 => (List.range t.packets.length).filter fun i =>
      (t.packets[i]?.bind fun p => lpLabel p.letters).isSome
  | k + 1 => (lpWalk t k).flatMap (lpSucc t)

/-- A packet walk `q` of length `n` over the cycle: at each step the row carries the letters of
a vertex of the cycle, and the star lists the edge with the prescribed digits to the next row. -/
def LpStep (t : Table (Fin 3)) (q : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ d e, (t.packets[q k]?.bind fun p => lpLabel p.letters) = some (d, e) ∧
    StarRow.child d e (q (k + 1)) ∈ t.stars.getD (q k) []

/-- Every packet walk over the cycle ends in `lpWalk`. -/
theorem lpWalk_mem (t : Table (Fin 3)) (q : ℕ → ℕ) (n : ℕ)
    (h : ∀ k < n + 1, LpStep t q k) :
    ∀ k ≤ n + 1, q k ∈ lpWalk t k := by
  intro k hk
  induction k with
  | zero =>
    obtain ⟨d, e, hl, -⟩ := h 0 (by omega)
    have hlt : q 0 < t.packets.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hl
      exact absurd hl (by simp)
    simp only [lpWalk, List.mem_filter, List.mem_range]
    exact ⟨hlt, by rw [hl]; rfl⟩
  | succ k ih =>
    obtain ⟨d, e, hl, hm⟩ := h k (by omega)
    simp only [lpWalk, List.mem_flatMap]
    refine ⟨q k, ih (by omega), ?_⟩
    simp only [lpSucc, hl, List.mem_filterMap]
    exact ⟨_, hm, by simp⟩

/-- The two edges of the cycle are edges of the letter-pair quotient of Tribonacci:
`(σ(0)[1], σ(1)[0]) = (1, 0)` and `(σ(1)[0], σ(0)[1]) = (0, 1)`. -/
theorem trib_letterpair_cycle :
    (Tribonacci.table.s 0)[1]? = some 1 ∧ (Tribonacci.table.s 1)[0]? = some 0 := by
  decide +kernel

/-- **The letter-pair cycle has no packet cycle over it** (Tribonacci).  Every packet walk over
the cycle dies within four steps (`lpWalk` is empty at length 4: the full child stars keep the
digits and the splits that the letter-pair quotient forgets), hence there is no infinite packet
walk over it and no packet cycle over it. -/
theorem trib_letterpair_cycle_unrealised :
    lpWalk Tribonacci.table 4 = [] ∧
      (¬ ∃ q : ℕ → ℕ, ∀ k < 4, LpStep Tribonacci.table q k) ∧
      (¬ ∃ q : ℕ → ℕ, ∀ k, LpStep Tribonacci.table q k) ∧
      ¬ ∃ (q : ℕ → ℕ) (m : ℕ), 0 < m ∧ q m = q 0 ∧
        ∀ k < m, LpStep Tribonacci.table q k := by
  have h4 : lpWalk Tribonacci.table 4 = [] := by decide +kernel
  have hno : ¬ ∃ q : ℕ → ℕ, ∀ k < 4, LpStep Tribonacci.table q k := by
    rintro ⟨q, hq⟩
    have := lpWalk_mem Tribonacci.table q 3 hq 4 le_rfl
    rw [h4] at this
    exact absurd this (by simp)
  refine ⟨h4, hno, fun ⟨q, hq⟩ => hno ⟨q, fun k _ => hq k⟩, ?_⟩
  rintro ⟨q, m, hm, hqm, hq⟩
  refine hno ⟨fun k => q (k % m), fun k _ => ?_⟩
  have hk : k % m < m := Nat.mod_lt _ hm
  have hnext : q ((k + 1) % m) = q (k % m + 1) := by
    rw [← Nat.mod_add_mod]
    rcases Nat.lt_or_ge (k % m + 1) m with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]
    · have he : k % m + 1 = m := by omega
      rw [he, Nat.mod_self, hqm]
  obtain ⟨d, e, hl, hmem⟩ := hq (k % m) hk
  exact ⟨d, e, hl, by simp only; rw [hnext]; exact hmem⟩

end Psc.PacketSquareControls

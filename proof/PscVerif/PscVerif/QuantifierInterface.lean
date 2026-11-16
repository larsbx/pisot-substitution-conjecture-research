import Mathlib

/-!
# Quantifier interface for child graphs

A *child graph* is a set of states with a child relation and a target
predicate.  For the balanced pair algorithm the states are irreducible balanced
pairs, the children are the irreducible factors of the inflated pair, and the
targets are the coincidences; for an overlap graph the states are overlaps and
the targets are coincident overlaps.  Nothing below depends on that reading:
this module is graph logic only, and it proves **nothing** about any
substitution.

Three statements about a state `s` are routinely confused.  In temporal-logic
notation, with `T` the target set:

* **(E)** `Productive s` — `EF T`: *some* path from `s` reaches a target;
* **(AE)** `HereditarilyProductive s` — `AG EF T`: *every* state reachable from
  `s` is productive;
* **(A)** `Inevitable s` — `AF T`: *every* infinite admissible path from `s`
  meets a target.

The valid implications are `(A) ⇒ (AE) ⇒ (E)` (the first needs targets to be
child-closed and non-targets to have a child); neither converse holds: see the
countermodels `fork` (three states) and `lasso` (two states).

A fourth reading, `CyclicProductive s`, restricts (AE) to the reachable states
that lie on a cycle; it is the form of "every recurrent strongly connected set
contains a productive state" and of "every cyclic vertex has a descendant in
the target".  With a finite reachable set and a child at every non-target it is
equivalent to (AE) (`hereditarilyProductive_of_cyclic_of_finite`), and
`two_obstruction_skeleton` composes it with a second target set; without
finiteness it says nothing (`ray_cyclicProductive_vacuous`).

`InevMax s`, written (A⁺), is (A) for *maximal* trajectories: infinite
admissible paths and finite paths ending at a state with no child.  It is (A)
together with the absence of reachable dead ends (`inevMax_iff`), and with a
finite reachable set it is the absence of reachable strict cycles and dead ends
(`inevMax_iff_of_finite`); `stub` shows that (A) alone is vacuous at a dead
end.

Exclusion statements match the quantifiers exactly:

* (AE) ⇔ no nonempty child-closed target-free set is reachable
  (`hereditarilyProductive_iff_no_strictClosed`), with no finiteness;
* when the reachable set is finite, (AE) ⇔ no *closed strongly connected*
  target-free set is reachable
  (`exists_strictComponent_of_finite`); the countermodel `ray` shows that
  finiteness cannot be dropped: there the exclusion holds vacuously and no
  state is productive;
* when the reachable set is finite, (A) ⇔ no target-free cycle is reachable
  through non-targets (`inevitable_iff_no_strict_cycle_of_finite`); `lasso`
  has such a cycle, and it is not closed.

Two further graphs separate statements that are sometimes run together:
`loopRay` has a recurrent strict strongly connected set that is not closed and
no finite strict closed set, so exclusion of finite closed strict components
does not give "every recurrent strict component contains a productive state";
`comb` satisfies (AE) with an infinite reachable set, so (AE) is not
termination.

`chain N` is a family in which every member satisfies (A) with first hitting
time exactly `N`: no depth bound is uniform over the family, and below depth
`N` the member `chain N` is indistinguishable from `ray`
(`chain_agrees_with_ray`).

The last section adds multiplicities and a mass.  With a positive mass conserved
at the inflation rate `θ`, strict mass `o(θⁿ)` below `s` gives (AE)
(`MassGraph.hereditarilyProductive_of_nullStrict`): a reachable strict closed
set would keep its whole mass.  It does not give (A): in `lassoMass` one unit of
strict mass out of `2ⁿ` survives at every level, null and never zero.  And it
gives nothing without conservation: in `slow` the strict mass is null and a
strict closed set is reachable.  "Null" is therefore a statement about closed
strict sets carrying conserved positive mass, and never the statement that the
strict set is empty.
-/

namespace Psc.QuantifierInterface

universe u

/-- A child graph with a target predicate. -/
structure ChildGraph (S : Type u) where
  /-- `child s t`: `t` is a child of `s`. -/
  child : S → S → Prop
  /-- The target states (coincidences). -/
  target : S → Prop

namespace ChildGraph

variable {S : Type u} (G : ChildGraph S)

/-- Reachability by zero or more child steps. -/
abbrev Reach : S → S → Prop := Relation.ReflTransGen G.child

/-- A strict step: a child step out of a non-target. -/
abbrev StrictStep : S → S → Prop := fun a b => ¬ G.target a ∧ G.child a b

/-- **(E)**, `EF T`: some path from `s` reaches a target. -/
def Productive (s : S) : Prop := ∃ t, G.Reach s t ∧ G.target t

/-- **(AE)**, `AG EF T`: every state reachable from `s` is productive. -/
def HereditarilyProductive (s : S) : Prop := ∀ t, G.Reach s t → G.Productive t

/-- **(AE) on cyclic states**: every state reachable from `s` that lies on a
cycle is productive.  Since the states of a strongly connected set are
productive together, this is "every recurrent strongly connected set reachable
from `s` contains a productive state". -/
def CyclicProductive (s : S) : Prop :=
  ∀ t, G.Reach s t → Relation.TransGen G.child t t → G.Productive t

/-- An admissible path: an infinite sequence of child steps. -/
def IsPath (p : ℕ → S) : Prop := ∀ n, G.child (p n) (p (n + 1))

/-- **(A)**, `AF T`: every admissible path from `s` meets a target. -/
def Inevitable (s : S) : Prop :=
  ∀ p : ℕ → S, p 0 = s → G.IsPath p → ∃ n, G.target (p n)

/-- The inductive form of (A): `s` is a target, or all its children are
inevitable.  `inevitable_iff_inev` identifies it with the path form. -/
inductive Inev (G : ChildGraph S) : S → Prop
  | here {s : S} : G.target s → Inev G s
  | step {s : S} : (∀ t, G.child s t → Inev G t) → Inev G s

/-- `C` is child-closed. -/
def Closed (C : Set S) : Prop := ∀ ⦃s t⦄, s ∈ C → G.child s t → t ∈ C

/-- A **strict closed set**: nonempty, child-closed, and target-free. -/
structure StrictClosed (C : Set S) : Prop where
  nonempty : C.Nonempty
  closed : G.Closed C
  strict : ∀ s ∈ C, ¬ G.target s

/-- Every state of `C` reaches every state of `C`. -/
def StronglyConnected (C : Set S) : Prop := ∀ a ∈ C, ∀ b ∈ C, G.Reach a b

/-- Targets are child-closed (coincidences have only coincidence children). -/
def TargetClosed : Prop := ∀ ⦃s t⦄, G.target s → G.child s t → G.target t

/-- Every non-target has a child. -/
def NonTerminal : Prop := ∀ s, ¬ G.target s → ∃ t, G.child s t

variable {G} {s t : S} {C : Set S}

/-! ### Transport: backward for (E), forward for (AE) -/

theorem productive_of_target (h : G.target s) : G.Productive s :=
  ⟨s, .refl, h⟩

/-- (E) transports **backward** along reachability. -/
theorem productive_of_reach (hst : G.Reach s t) (ht : G.Productive t) : G.Productive s :=
  let ⟨u, htu, hu⟩ := ht
  ⟨u, hst.trans htu, hu⟩

/-- (AE) ⇒ (E). -/
theorem HereditarilyProductive.productive (h : G.HereditarilyProductive s) : G.Productive s :=
  h s .refl

/-- (AE) transports **forward** along reachability. -/
theorem HereditarilyProductive.of_reach (h : G.HereditarilyProductive s) (hst : G.Reach s t) :
    G.HereditarilyProductive t :=
  fun u htu => h u (hst.trans htu)

/-- (AE) gives its restriction to cyclic states. -/
theorem HereditarilyProductive.cyclicProductive (h : G.HereditarilyProductive s) :
    G.CyclicProductive s :=
  fun t hst _ => h t hst

/-! ### (AE) is closed-strict exclusion -/

theorem Closed.reach (hC : G.Closed C) (hs : s ∈ C) (hst : G.Reach s t) : t ∈ C := by
  induction hst with
  | refl => exact hs
  | tail _ hbc ih => exact hC ih hbc

theorem closed_reachSet (s : S) : G.Closed {t | G.Reach s t} :=
  fun _ _ ha hab => Relation.ReflTransGen.tail ha hab

/-- No state of a strict closed set is productive. -/
theorem StrictClosed.not_productive (hC : G.StrictClosed C) (hs : s ∈ C) : ¬ G.Productive s :=
  fun ⟨t, hst, ht⟩ => hC.strict t (hC.closed.reach hs hst) ht

/-- The states reachable from a nonproductive state form a strict closed set. -/
theorem strictClosed_reachSet (h : ¬ G.Productive s) : G.StrictClosed {t | G.Reach s t} where
  nonempty := ⟨s, .refl⟩
  closed := closed_reachSet s
  strict t hst ht := h ⟨t, hst, ht⟩

/-- **(AE) ⇔ closed-strict exclusion**, with no finiteness hypothesis: every
state reachable from `s` is productive iff no strict closed set is reachable
from `s`. -/
theorem hereditarilyProductive_iff_no_strictClosed (s : S) :
    G.HereditarilyProductive s ↔ ¬ ∃ C : Set S, G.StrictClosed C ∧ ∃ t ∈ C, G.Reach s t := by
  constructor
  · rintro h ⟨C, hC, t, ht, hst⟩
    exact hC.not_productive ht (h t hst)
  · intro h t hst
    by_contra hnp
    exact h ⟨_, strictClosed_reachSet hnp, t, .refl, hst⟩

/-! ### (A): path form and inductive form -/

theorem Inev.inevitable (h : G.Inev s) : G.Inevitable s := by
  induction h with
  | here ht =>
    intro p hp _
    exact ⟨0, hp ▸ ht⟩
  | step _ ih =>
    intro p hp hpath
    have h01 : G.child _ (p 1) := hp ▸ hpath 0
    obtain ⟨n, hn⟩ := ih (p 1) h01 (fun n => p (n + 1)) rfl fun n => hpath (n + 1)
    exact ⟨n + 1, hn⟩

/-- A state that is not inevitable is a non-target with a child that is not
inevitable. -/
theorem exists_child_not_inev (h : ¬ G.Inev s) :
    ¬ G.target s ∧ ∃ t, G.child s t ∧ ¬ G.Inev t := by
  refine ⟨fun ht => h (.here ht), ?_⟩
  by_contra hc
  exact h (.step fun t hst => by_contra fun ht => hc ⟨t, hst, ht⟩)

/-- From a state that is not inevitable there is an admissible path that never
meets a target (dependent choice). -/
theorem exists_strict_path_of_not_inev (h : ¬ G.Inev s) :
    ∃ p : ℕ → S, p 0 = s ∧ G.IsPath p ∧ ∀ n, ¬ G.Inev (p n) := by
  have next : ∀ a : {a : S // ¬ G.Inev a}, ∃ b : {b : S // ¬ G.Inev b}, G.child a.1 b.1 :=
    fun a =>
      let ⟨_, b, hab, hb⟩ := exists_child_not_inev a.2
      ⟨⟨b, hb⟩, hab⟩
  choose f hf using next
  refine ⟨fun n => (f^[n] ⟨s, h⟩).1, rfl, fun n => ?_, fun n => (f^[n] ⟨s, h⟩).2⟩
  simp only [Function.iterate_succ_apply']
  exact hf _

theorem Inevitable.inev (h : G.Inevitable s) : G.Inev s := by
  by_contra hs
  obtain ⟨p, hp0, hpath, hp⟩ := exists_strict_path_of_not_inev hs
  obtain ⟨n, hn⟩ := h p hp0 hpath
  exact hp n (.here hn)

/-- The path form and the inductive form of (A) agree. -/
theorem inevitable_iff_inev : G.Inevitable s ↔ G.Inev s :=
  ⟨Inevitable.inev, Inev.inevitable⟩

/-! ### (A) ⇒ (AE) -/

theorem TargetClosed.reach (hT : G.TargetClosed) (hs : G.target s) (hst : G.Reach s t) :
    G.target t := by
  induction hst with
  | refl => exact hs
  | tail _ hbc ih => exact hT ih hbc

theorem Inev.hereditarilyProductive (hT : G.TargetClosed) (hN : G.NonTerminal) (h : G.Inev s) :
    G.HereditarilyProductive s := by
  induction h with
  | here ht => exact fun t hst => productive_of_target (hT.reach ht hst)
  | @step a _ ih =>
    intro t hat
    rcases Relation.ReflTransGen.cases_head hat with heq | ⟨c, hac, hct⟩
    · rw [← heq]
      by_cases hta : G.target a
      · exact productive_of_target hta
      · obtain ⟨c, hc⟩ := hN a hta
        exact productive_of_reach (.single hc) (ih c hc).productive
    · exact ih c hac t hct

/-- **(A) ⇒ (AE)** when targets are child-closed and non-targets have a child. -/
theorem Inevitable.hereditarilyProductive (hT : G.TargetClosed) (hN : G.NonTerminal)
    (h : G.Inevitable s) : G.HereditarilyProductive s :=
  h.inev.hereditarilyProductive hT hN

/-! ### Finite reachable set: closed strongly connected strict sets -/

/-- **Extraction.**  If the set of states reachable from `s` is finite and some
reachable state is nonproductive, a finite strict closed *strongly connected*
set is reachable from `s`.  Finiteness of the reachable set is an input. -/
theorem exists_strictComponent_of_finite (hfin : {t | G.Reach s t}.Finite)
    (h : ¬ G.HereditarilyProductive s) :
    ∃ C : Set S, C.Finite ∧ G.StrictClosed C ∧ G.StronglyConnected C ∧ ∃ t ∈ C, G.Reach s t := by
  obtain ⟨t, hst, hnp⟩ : ∃ t, G.Reach s t ∧ ¬ G.Productive t := by
    by_contra hc
    exact h fun t hst => by_contra fun hnp => hc ⟨t, hst, hnp⟩
  have hDfin : {u | G.Reach t u}.Finite := hfin.subset fun u hu => hst.trans hu
  obtain ⟨u, hu, hmin⟩ := Set.exists_min_image {u | G.Reach t u}
    (fun u => {v | G.Reach u v}.ncard) hDfin ⟨t, .refl⟩
  have hufin : {v | G.Reach u v}.Finite := hDfin.subset fun v hv => Relation.ReflTransGen.trans hu hv
  refine ⟨{v | G.Reach u v}, hufin, ⟨⟨u, .refl⟩, closed_reachSet u, fun v hv hvt => ?_⟩,
    fun a ha b hb => ?_, u, .refl, hst.trans hu⟩
  · exact hnp ⟨v, Relation.ReflTransGen.trans hu hv, hvt⟩
  · have hsub : {v | G.Reach a v} ⊆ {v | G.Reach u v} :=
      fun v hv => Relation.ReflTransGen.trans ha hv
    have heq : {v | G.Reach a v} = {v | G.Reach u v} :=
      Set.eq_of_subset_of_ncard_le hsub (hmin a (Relation.ReflTransGen.trans hu ha)) hufin
    have hau : u ∈ {v | G.Reach a v} := heq ▸ (Relation.ReflTransGen.refl : G.Reach u u)
    exact Relation.ReflTransGen.trans hau hb

/-- **The typed bridge from component exclusion to (AE).**  Two separate inputs:
`hfin`, finiteness of the reachable set (an extraction/termination statement),
and `hexcl`, that no finite strict closed strongly connected set is reachable
(a component-exclusion statement).  `ray_exclusion_vacuous` shows `hfin` cannot
be dropped. -/
theorem hereditarilyProductive_of_finite_of_exclusion (hfin : {t | G.Reach s t}.Finite)
    (hexcl : ¬ ∃ C : Set S, C.Finite ∧ G.StrictClosed C ∧ G.StronglyConnected C ∧
      ∃ t ∈ C, G.Reach s t) :
    G.HereditarilyProductive s := by
  by_contra h
  exact hexcl (exists_strictComponent_of_finite hfin h)

/-- With a finite reachable set, (AE) is exactly exclusion of reachable finite
strict closed strongly connected sets. -/
theorem hereditarilyProductive_iff_exclusion_of_finite (hfin : {t | G.Reach s t}.Finite) :
    G.HereditarilyProductive s ↔
      ¬ ∃ C : Set S, C.Finite ∧ G.StrictClosed C ∧ G.StronglyConnected C ∧
        ∃ t ∈ C, G.Reach s t :=
  ⟨fun h ⟨_, _, hC, _, t, ht, hst⟩ => hC.not_productive ht (h t hst),
    hereditarilyProductive_of_finite_of_exclusion hfin⟩

/-- **Cyclic vertices suffice in a finite graph.**  If the reachable set is
finite, every non-target has a child, and every reachable state that lies on a
cycle is productive, then every reachable state is productive.  This is the
form "for every cyclic vertex there is a path to the target": a statement of
type (AE), quantified over all cyclic vertices and existential in the path.
Finiteness cannot be dropped (`ray_cyclicProductive_vacuous`). -/
theorem hereditarilyProductive_of_cyclic_of_finite (hfin : {t | G.Reach s t}.Finite)
    (hN : G.NonTerminal) (hcyc : G.CyclicProductive s) :
    G.HereditarilyProductive s := by
  by_contra h
  obtain ⟨C, -, hC, hSC, t, ht, hst⟩ := exists_strictComponent_of_finite hfin h
  obtain ⟨c, htc⟩ := hN t (hC.strict t ht)
  exact hC.not_productive ht
    (hcyc t hst (Relation.TransGen.head' htc (hSC c (hC.closed ht htc) t ht)))

/-- **The graph skeleton of a two-obstruction completion.**  Let `zero` mark a
set of intermediate states (offset-zero overlaps).  If the reachable set is
finite, every non-target has a child, every reachable cyclic state has a `zero`
descendant (`hB`), and every reachable `zero` state is productive (`hA`), then
every reachable state is productive.  `hA` and `hB` are hypotheses: the theorem
is the implication, and `fork_without_A`, `fork_without_B` show that neither
can be dropped. -/
theorem two_obstruction_skeleton (zero : S → Prop) (hfin : {t | G.Reach s t}.Finite)
    (hN : G.NonTerminal)
    (hB : ∀ t, G.Reach s t → Relation.TransGen G.child t t → ∃ y, G.Reach t y ∧ zero y)
    (hA : ∀ y, G.Reach s y → zero y → G.Productive y) :
    G.HereditarilyProductive s :=
  hereditarilyProductive_of_cyclic_of_finite hfin hN fun t hst hc =>
    let ⟨y, hty, hy⟩ := hB t hst hc
    productive_of_reach hty (hA y (hst.trans hty) hy)

/-! ### Finite reachable set: (A) is exclusion of every strict cycle -/

/-- An inevitable non-target has only inevitable children. -/
theorem Inev.of_strictStep (h : G.Inev s) (hst : G.StrictStep s t) : G.Inev t := by
  cases h with
  | here ht => exact absurd ht hst.1
  | step hch => exact hch t hst.2

theorem Inev.of_strictReach (h : G.Inev s) (hst : Relation.ReflTransGen G.StrictStep s t) :
    G.Inev t := by
  induction hst with
  | refl => exact h
  | tail _ hbc ih => exact ih.of_strictStep hbc

/-- An inevitable state lies on no strict cycle. -/
theorem Inev.not_strict_cycle (h : G.Inev s) : ¬ Relation.TransGen G.StrictStep s s := by
  induction h with
  | here ht =>
    intro hc
    obtain ⟨c, hac, -⟩ := Relation.TransGen.head'_iff.1 hc
    exact hac.1 ht
  | @step a _ ih =>
    intro hc
    obtain ⟨c, hac, hca⟩ := Relation.TransGen.head'_iff.1 hc
    exact ih c hac.2 (Relation.TransGen.tail' hca hac)

/-- Along an admissible path that avoids targets, later states are reached by
strict steps. -/
theorem strictReach_of_strict_path {p : ℕ → S} (hpath : G.IsPath p)
    (hp : ∀ n, ¬ G.target (p n)) (i k : ℕ) :
    Relation.ReflTransGen G.StrictStep (p i) (p (i + k)) := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact ih.tail ⟨hp _, hpath _⟩

/-- **(A) with a finite reachable set.**  Every admissible path from `s` meets a
target iff no cycle of non-targets is reachable from `s` through non-targets.
The cycle need not be child-closed: compare
`hereditarilyProductive_iff_exclusion_of_finite`. -/
theorem inevitable_iff_no_strict_cycle_of_finite (hfin : {t | G.Reach s t}.Finite) :
    G.Inevitable s ↔
      ¬ ∃ t, Relation.ReflTransGen G.StrictStep s t ∧ Relation.TransGen G.StrictStep t t := by
  constructor
  · rintro h ⟨t, hst, hcyc⟩
    exact (h.inev.of_strictReach hst).not_strict_cycle hcyc
  · intro h
    rw [inevitable_iff_inev]
    by_contra hs
    obtain ⟨p, hp0, hpath, hp⟩ := exists_strict_path_of_not_inev hs
    have hpt : ∀ n, ¬ G.target (p n) := fun n hn => hp n (.here hn)
    have hreach : ∀ n, G.Reach s (p n) := fun n => by
      have := strictReach_of_strict_path hpath hpt 0 n
      rw [Nat.zero_add, hp0] at this
      exact this.lift id fun _ _ hab => hab.2
    have hninj : ¬ Function.Injective p := fun hinj =>
      (Set.infinite_range_of_injective hinj) (hfin.subset (by rintro _ ⟨n, rfl⟩; exact hreach n))
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
      simpa [Function.Injective] using hninj
    wlog hlt : i < j generalizing i j
    · exact this j i hij.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    obtain ⟨k, rfl⟩ : ∃ k, j = i + (k + 1) := ⟨j - i - 1, by omega⟩
    refine h ⟨p i, ?_, ?_⟩
    · have := strictReach_of_strict_path hpath hpt 0 i
      rwa [Nat.zero_add, hp0] at this
    · have hk := strictReach_of_strict_path hpath hpt (i + 1) k
      have h1 : G.StrictStep (p i) (p (i + 1)) := ⟨hpt i, hpath i⟩
      have : Relation.TransGen G.StrictStep (p i) (p (i + 1 + k)) :=
        Relation.TransGen.head' h1 hk
      rwa [show i + 1 + k = i + (k + 1) by omega, ← hij] at this

/-! ### Maximal trajectories: dead ends count -/

/-- A **dead end**: a non-target with no child. -/
def DeadEnd (G : ChildGraph S) (s : S) : Prop := ¬ G.target s ∧ ∀ t, ¬ G.child s t

/-- **(A⁺)**: every *maximal* trajectory from `s` meets a target, where a
maximal trajectory is an infinite admissible path or a finite path that ends at
a state with no child.  Inductive form: `s` is a target, or `s` has a child and
every child satisfies (A⁺).  It differs from (A) exactly by the dead ends
(`inevMax_iff`). -/
inductive InevMax (G : ChildGraph S) : S → Prop
  | here {s : S} : G.target s → InevMax G s
  | step {s : S} : (∃ t, G.child s t) → (∀ t, G.child s t → InevMax G t) → InevMax G s

theorem InevMax.inev (h : G.InevMax s) : G.Inev s := by
  induction h with
  | here ht => exact .here ht
  | step _ _ ih => exact .step ih

/-- No non-target is reached from a target by strict steps other than itself. -/
theorem eq_of_strictReach_of_target (ht : G.target s)
    (hst : Relation.ReflTransGen G.StrictStep s t) : s = t := by
  rcases Relation.ReflTransGen.cases_head hst with h | ⟨c, hsc, -⟩
  · exact h
  · exact absurd ht hsc.1

/-- **(A⁺) is (A) together with the absence of reachable dead ends.** -/
theorem inevMax_iff :
    G.InevMax s ↔ G.Inev s ∧ ¬ ∃ t, Relation.ReflTransGen G.StrictStep s t ∧ G.DeadEnd t := by
  constructor
  · intro h
    refine ⟨h.inev, ?_⟩
    induction h with
    | here ht =>
      rintro ⟨t, hst, hd⟩
      exact hd.1 (eq_of_strictReach_of_target ht hst ▸ ht)
    | @step a hch _ ih =>
      rintro ⟨t, hat, hd⟩
      rcases Relation.ReflTransGen.cases_head hat with heq | ⟨c, hac, hct⟩
      · obtain ⟨c, hc⟩ := hch
        exact hd.2 c (heq ▸ hc)
      · exact ih c hac.2 ⟨t, hct, hd⟩
  · rintro ⟨h, hnd⟩
    induction h with
    | here ht => exact .here ht
    | @step a _ ih =>
      by_cases hta : G.target a
      · exact .here hta
      · refine .step ?_ fun t hat => ih t hat ?_
        · by_contra hno
          exact hnd ⟨a, .refl, hta, fun t hat => hno ⟨t, hat⟩⟩
        · rintro ⟨u, htu, hd⟩
          exact hnd ⟨u, Relation.ReflTransGen.head ⟨hta, hat⟩ htu, hd⟩

/-- **(A⁺) with a finite reachable set.**  Every maximal trajectory from `s`
meets a target iff no state reached from `s` through non-targets lies on a cycle
of non-targets or is a dead end.  The dead end is one of the full graph: a
non-target all of whose children are targets is not one. -/
theorem inevMax_iff_of_finite (hfin : {t | G.Reach s t}.Finite) :
    G.InevMax s ↔
      ¬ ∃ t, Relation.ReflTransGen G.StrictStep s t ∧
        (Relation.TransGen G.StrictStep t t ∨ G.DeadEnd t) := by
  rw [inevMax_iff, ← inevitable_iff_inev, inevitable_iff_no_strict_cycle_of_finite hfin]
  constructor
  · rintro ⟨h1, h2⟩ ⟨t, hst, hc | hd⟩
    · exact h1 ⟨t, hst, hc⟩
    · exact h2 ⟨t, hst, hd⟩
  · intro h
    exact ⟨fun ⟨t, hst, hc⟩ => h ⟨t, hst, Or.inl hc⟩, fun ⟨t, hst, hd⟩ => h ⟨t, hst, Or.inr hd⟩⟩

/-- (A⁺) gives (AE) when targets are child-closed, with no hypothesis on
non-targets: a dead end is excluded by (A⁺) itself. -/
theorem InevMax.hereditarilyProductive (hT : G.TargetClosed) (h : G.InevMax s) :
    G.HereditarilyProductive s := by
  induction h with
  | here ht => exact fun t hst => productive_of_target (hT.reach ht hst)
  | @step a hch _ ih =>
    intro t hat
    rcases Relation.ReflTransGen.cases_head hat with heq | ⟨c, hac, hct⟩
    · rw [← heq]
      obtain ⟨c, hc⟩ := hch
      exact productive_of_reach (.single hc) (ih c hc).productive
    · exact ih c hac t hct

end ChildGraph

open ChildGraph

/-! ## Minimal countermodels -/

/-! ### `fork`: (E) without (AE) -/

/-- Three states: the root, a coincidence, and a strict trap. -/
inductive Fork
  | root | good | bad
  deriving DecidableEq

instance : Fintype Fork where
  elems := {.root, .good, .bad}
  complete := by intro x; cases x <;> decide

/-- `root → good`, `root → bad`, `good → good`, `bad → bad`; the target is
`good`. -/
def fork : ChildGraph Fork where
  child a b :=
    match a with
    | .root => b = .good ∨ b = .bad
    | .good => b = .good
    | .bad => b = .bad
  target a := a = .good

theorem fork_targetClosed : fork.TargetClosed := by
  rintro a b (rfl : a = .good) hab
  exact hab

theorem fork_nonTerminal : fork.NonTerminal := by
  rintro (_ | _ | _) _
  · exact ⟨.good, Or.inl rfl⟩
  · exact ⟨.good, rfl⟩
  · exact ⟨.bad, rfl⟩

/-- `{bad}` is a strict closed strongly connected set of `fork`. -/
theorem fork_strictClosed : fork.StrictClosed {Fork.bad} where
  nonempty := ⟨.bad, rfl⟩
  closed := by
    rintro a b (rfl : a = .bad) hab
    exact hab
  strict := by
    rintro a (rfl : a = .bad) (h : Fork.bad = Fork.good)
    exact absurd h (by decide)

theorem fork_stronglyConnected : fork.StronglyConnected {Fork.bad} := by
  rintro a (rfl : a = .bad) b (rfl : b = .bad)
  exact .refl

theorem fork_root_productive : fork.Productive .root :=
  ⟨.good, .single (Or.inl rfl), rfl⟩

theorem fork_bad_not_productive : ¬ fork.Productive .bad :=
  fork_strictClosed.not_productive rfl

/-- **(E) does not imply (AE).**  The root of `fork` is productive, and its
child `bad` is not: a selected path to a coincidence does not exclude a strict
closed strongly connected set below the same root. -/
theorem fork_not_hereditarilyProductive :
    fork.Productive .root ∧ fork.child .root .bad ∧ ¬ fork.Productive .bad ∧
      ¬ fork.HereditarilyProductive .root :=
  ⟨fork_root_productive, Or.inr rfl, fork_bad_not_productive,
    fun h => fork_bad_not_productive (h .bad (.single (Or.inr rfl)))⟩

/-- (E) does not transport forward along a child step. -/
theorem productive_not_forward :
    ¬ ∀ (G : ChildGraph Fork) (a b : Fork), G.child a b → G.Productive a → G.Productive b :=
  fun h => fork_bad_not_productive (h fork .root .bad (Or.inr rfl) fork_root_productive)

theorem fork_reach_finite : {t | fork.Reach .root t}.Finite :=
  Set.toFinite _

theorem fork_reach_bad {t : Fork} (h : fork.Reach .bad t) : t = .bad :=
  fork_strictClosed.closed.reach (C := {Fork.bad}) rfl h

theorem fork_reach_good {t : Fork} (h : fork.Reach .good t) : t = .good := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    subst ih
    exact hbc

/-- **`hA` cannot be dropped.**  With `zero` the two non-root states of `fork`,
every cyclic state has a `zero` descendant (itself), the `zero` state `bad` is
not productive, and the conclusion of `two_obstruction_skeleton` fails. -/
theorem fork_without_A :
    (∀ t, fork.Reach .root t → Relation.TransGen fork.child t t →
        ∃ y, fork.Reach t y ∧ y ≠ Fork.root) ∧
      ¬ (∀ y, fork.Reach .root y → y ≠ Fork.root → fork.Productive y) ∧
      ¬ fork.HereditarilyProductive .root := by
  refine ⟨fun t _ hc => ?_, fun h => ?_, fork_not_hereditarilyProductive.2.2.2⟩
  · cases t with
    | root =>
      exfalso
      obtain ⟨c, hrc, hcr⟩ := Relation.TransGen.head'_iff.1 hc
      rcases hrc with rfl | rfl
      · exact absurd (fork_reach_good hcr) (by decide)
      · exact absurd (fork_reach_bad hcr) (by decide)
    | good => exact ⟨.good, .refl, by decide⟩
    | bad => exact ⟨.bad, .refl, by decide⟩
  · exact fork_bad_not_productive (h .bad (.single (Or.inr rfl)) (by decide))

/-- **`hB` cannot be dropped.**  With `zero` the target `good` of `fork`, every
`zero` state is productive, the cyclic state `bad` has no `zero` descendant, and
the conclusion of `two_obstruction_skeleton` fails. -/
theorem fork_without_B :
    (∀ y, fork.Reach .root y → y = Fork.good → fork.Productive y) ∧
      ¬ (∀ t, fork.Reach .root t → Relation.TransGen fork.child t t →
        ∃ y, fork.Reach t y ∧ y = Fork.good) ∧
      ¬ fork.HereditarilyProductive .root := by
  refine ⟨fun y _ hy => productive_of_target hy, fun h => ?_,
    fork_not_hereditarilyProductive.2.2.2⟩
  obtain ⟨y, hby, hy⟩ := h .bad (.single (Or.inr rfl)) (.single rfl)
  exact absurd ((fork_reach_bad hby).symm.trans hy) (by decide)

/-! ### `lasso`: (AE) without (A) -/

/-- Two states: `false` (a non-target with a self-loop and an exit) and `true`
(the target).  `false → false`, `false → true`, `true → true`. -/
def lasso : ChildGraph Bool where
  child a b := a = false ∨ b = true
  target a := a = true

theorem lasso_targetClosed : lasso.TargetClosed := by
  rintro a b (rfl : a = true) hab
  rcases hab with h | h
  · exact absurd h (by decide)
  · exact h

theorem lasso_nonTerminal : lasso.NonTerminal :=
  fun _ _ => ⟨true, Or.inr rfl⟩

theorem lasso_productive (a : Bool) : lasso.Productive a :=
  ⟨true, .single (Or.inr rfl), rfl⟩

/-- Every state of `lasso` is hereditarily productive. -/
theorem lasso_hereditarilyProductive (a : Bool) : lasso.HereditarilyProductive a :=
  fun t _ => lasso_productive t

/-- `lasso` has no strict closed set at all. -/
theorem lasso_no_strictClosed (C : Set Bool) : ¬ lasso.StrictClosed C := fun hC =>
    let ⟨a, ha⟩ := hC.nonempty
    hC.not_productive ha (lasso_productive a)

/-- The constant path at `false` is admissible and never meets the target. -/
theorem lasso_strict_path :
    lasso.IsPath (fun _ => false) ∧ ∀ n : ℕ, ¬ lasso.target ((fun _ => false) n) :=
  ⟨fun _ => Or.inl rfl, fun _ (h : false = true) => Bool.false_ne_true h⟩

/-- **(AE) does not imply (A).**  In `lasso` every state is hereditarily
productive and no strict closed set exists, yet an admissible path from `false`
never meets the target. -/
theorem lasso_not_inevitable :
    lasso.HereditarilyProductive false ∧ (∀ C : Set Bool, ¬ lasso.StrictClosed C) ∧
      ¬ lasso.Inevitable false :=
  ⟨lasso_hereditarilyProductive false, lasso_no_strictClosed, fun h =>
    let ⟨n, hn⟩ := h (fun _ => false) rfl lasso_strict_path.1
    lasso_strict_path.2 n hn⟩

/-- The strict cycle of `lasso` is strongly connected and target-free but **not**
child-closed: excluding closed strict components does not exclude it. -/
theorem lasso_cycle_not_closed :
    lasso.StronglyConnected {false} ∧ (∀ a ∈ ({false} : Set Bool), ¬ lasso.target a) ∧
      Relation.TransGen lasso.StrictStep false false ∧ ¬ lasso.Closed {false} := by
  refine ⟨?_, ?_, .single ⟨fun (h : false = true) => Bool.false_ne_true h, Or.inl rfl⟩,
    fun h => ?_⟩
  · rintro a (rfl : a = false) b (rfl : b = false)
    exact .refl
  · rintro a (rfl : a = false) (h : false = true)
    exact Bool.false_ne_true h
  · have : true ∈ ({false} : Set Bool) := h (Set.mem_singleton false) (Or.inl rfl)
    exact absurd this (by decide)

/-! ### `ray`: component exclusion without finiteness -/

/-- The ray `0 → 1 → 2 → ⋯` with no target. -/
def ray : ChildGraph ℕ where
  child a b := b = a + 1
  target _ := False

theorem ray_reach_le {a b : ℕ} (h : ray.Reach a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih =>
    have : _ = _ + 1 := hbc
    omega

theorem ray_reach_of_le {a b : ℕ} (h : a ≤ b) : ray.Reach a b := by
  induction b, h using Nat.le_induction with
  | base => exact .refl
  | succ b _ ih => exact ih.tail rfl

theorem ray_not_productive (a : ℕ) : ¬ ray.Productive a :=
  fun ⟨_, _, h⟩ => h

/-- No nonempty finite set of the ray is child-closed. -/
theorem ray_no_finite_closed (C : Set ℕ) (hfin : C.Finite) (hne : C.Nonempty) :
    ¬ ray.Closed C := fun hC => by
  obtain ⟨m, hm, hmax⟩ := Set.exists_max_image C id hfin hne
  have : m + 1 ≤ m := hmax (m + 1) (hC hm rfl)
  omega

/-- The ray has no cycle. -/
theorem ray_no_cycle (a : ℕ) : ¬ Relation.TransGen ray.child a a := fun h => by
  obtain ⟨c, hac, hca⟩ := Relation.TransGen.head'_iff.1 h
  have h1 : c = a + 1 := hac
  have h2 := ray_reach_le hca
  omega

/-- **(AE) on cyclic states does not give (E) without finiteness.**  The ray has
no cycle, so every reachable cyclic state is productive vacuously, and no state
is productive. -/
theorem ray_cyclicProductive_vacuous : ray.CyclicProductive 0 ∧ ¬ ray.Productive 0 :=
  ⟨fun t _ hc => absurd hc (ray_no_cycle t), ray_not_productive 0⟩

/-- The set of states reachable from `0` in the ray is infinite. -/
theorem ray_reachable_infinite : ¬ {t | ray.Reach 0 t}.Finite := by
  have : {t | ray.Reach 0 t} = Set.univ :=
    Set.eq_univ_of_forall fun t => ray_reach_of_le (Nat.zero_le t)
  rw [this]
  exact Set.infinite_univ

/-- **Component exclusion does not give productivity without finiteness.**  In
the ray no finite strict closed set exists (so every statement excluding finite
strict closed strongly connected sets holds vacuously) and there is no cycle,
yet no state is productive.  The finiteness hypothesis of
`hereditarilyProductive_of_finite_of_exclusion` is a separate input. -/
theorem ray_exclusion_vacuous :
    (¬ ∃ C : Set ℕ, C.Finite ∧ ray.StrictClosed C ∧ ray.StronglyConnected C ∧
        ∃ t ∈ C, ray.Reach 0 t) ∧
      (∀ a, ¬ Relation.TransGen ray.child a a) ∧ ¬ ray.Productive 0 ∧
      ¬ ray.HereditarilyProductive 0 :=
  ⟨fun ⟨C, hfin, hC, _⟩ => ray_no_finite_closed C hfin hC.nonempty hC.closed, ray_no_cycle,
    ray_not_productive 0, fun h => ray_not_productive 0 h.productive⟩

/-! ### `loopRay`: a recurrent strict component that is not closed, and no finite closed one -/

/-- A self-looping non-target `none` feeding the ray `some 0 → some 1 → ⋯`; no
target. -/
def loopRay : ChildGraph (Option ℕ) where
  child a b :=
    match a with
    | none => b = none ∨ b = some 0
    | some n => b = some (n + 1)
  target _ := False

theorem loopRay_closed_some {C : Set (Option ℕ)} (hC : loopRay.Closed C) {n : ℕ}
    (hn : some n ∈ C) (k : ℕ) : some (n + k) ∈ C := by
  induction k with
  | zero => exact hn
  | succ k ih => exact hC ih (show some (n + (k + 1)) = some (n + k + 1) from rfl)

/-- No nonempty finite set of `loopRay` is child-closed. -/
theorem loopRay_no_finite_closed (C : Set (Option ℕ)) (hfin : C.Finite) (hne : C.Nonempty) :
    ¬ loopRay.Closed C := fun hC => by
  have h0 : some 0 ∈ C := by
    obtain ⟨a, ha⟩ := hne
    cases a with
    | none => exact hC ha (Or.inr rfl)
    | some n =>
      by_contra h
      have hinj : Function.Injective fun k : ℕ => (some (n + k) : Option ℕ) :=
        fun i j hij => by simpa using hij
      exact Set.infinite_range_of_injective hinj
        (hfin.subset (by rintro _ ⟨k, rfl⟩; exact loopRay_closed_some hC ha k))
  have hinj : Function.Injective fun k : ℕ => (some k : Option ℕ) := fun i j hij => by simpa using hij
  exact Set.infinite_range_of_injective hinj
    (hfin.subset (by
      rintro _ ⟨k, rfl⟩
      simpa using loopRay_closed_some hC h0 k))

/-- **Exclusion of finite closed strict components says nothing about a
recurrent strict component that is not closed.**  In `loopRay` no finite strict
closed set exists, the state `none` is recurrent and strongly connected with
itself, and no state is productive: "every recurrent target-free strongly
connected set contains a productive state" fails although every exclusion of
finite strict closed sets holds vacuously. -/
theorem loopRay_recurrent_not_closed :
    (¬ ∃ C : Set (Option ℕ), C.Finite ∧ loopRay.StrictClosed C) ∧
      Relation.TransGen loopRay.child none none ∧ loopRay.StronglyConnected {none} ∧
      (∀ a, ¬ loopRay.Productive a) ∧ ¬ loopRay.CyclicProductive none :=
  ⟨fun ⟨C, hfin, hC⟩ => loopRay_no_finite_closed C hfin hC.nonempty hC.closed,
    .single (Or.inl rfl),
    by rintro a (rfl : a = none) b (rfl : b = none); exact .refl,
    fun _ ⟨_, _, h⟩ => h,
    fun h => (h none .refl (.single (Or.inl rfl))).elim fun _ ⟨_, ht⟩ => ht⟩

/-! ### `comb`: (AE) with an infinite reachable set -/

/-- The ray `some 0 → some 1 → ⋯` with an exit `some n → none` at every state;
the target is `none`, which has no child. -/
def comb : ChildGraph (Option ℕ) where
  child a b :=
    match a with
    | none => False
    | some n => b = some (n + 1) ∨ b = none
  target a := a = none

theorem comb_productive (a : Option ℕ) : comb.Productive a := by
  cases a with
  | none => exact productive_of_target rfl
  | some n => exact ⟨none, .single (Or.inr rfl), rfl⟩

theorem comb_reach_some (n k : ℕ) : comb.Reach (some n) (some (n + k)) := by
  induction k with
  | zero => exact .refl
  | succ k ih => exact ih.tail (Or.inl rfl)

/-- **(AE) is not termination.**  In `comb` every state is hereditarily
productive, the set reachable from `some 0` is infinite, and an admissible path
from `some 0` never meets the target: productivity of every reachable state
neither gives nor needs a finite reachable set. -/
theorem comb_productive_infinite :
    comb.HereditarilyProductive (some 0) ∧ ¬ {t | comb.Reach (some 0) t}.Finite ∧
      ¬ comb.Inevitable (some 0) := by
  refine ⟨fun t _ => comb_productive t, fun hfin => ?_, fun h => ?_⟩
  · have hinj : Function.Injective fun k : ℕ => (some k : Option ℕ) :=
      fun i j hij => by simpa using hij
    exact Set.infinite_range_of_injective hinj
      (hfin.subset (by
        rintro _ ⟨k, rfl⟩
        simpa using comb_reach_some 0 k))
  · obtain ⟨n, hn⟩ := h (fun n => some n) rfl fun n => Or.inl rfl
    exact absurd hn (by simp [comb])

/-! ### `stub`: (A) holds vacuously at a dead end -/

/-- One non-target state with no child. -/
def stub : ChildGraph Unit where
  child _ _ := False
  target _ := False

/-- **(A) is vacuous at a dead end.**  In `stub` there is no admissible infinite
path, so (A) holds; the state is a dead end, so (A⁺), (AE) and (E) all fail.
An "every path" statement about infinite paths says nothing about a retained
graph in which a non-target has lost its children. -/
theorem stub_inevitable_not_productive :
    stub.Inevitable () ∧ stub.DeadEnd () ∧ ¬ stub.InevMax () ∧ ¬ stub.Productive () := by
  refine ⟨fun p _ hp => (hp 0).elim, ⟨fun h => h, fun _ h => h⟩, fun h => ?_, fun ⟨_, _, h⟩ => h⟩
  cases h with
  | here ht => exact ht
  | step hch _ => exact hch.elim fun _ h => h

/-! ### `chain N`: finite at each parameter, not uniform -/

/-- The chain `0 → 1 → ⋯ → N` with `N` absorbing; the targets are the states
`≥ N`. -/
def chain (N : ℕ) : ChildGraph ℕ where
  child a b := b = if a < N then a + 1 else a
  target a := N ≤ a

/-- The first `d` child steps from `0` meet a target. -/
def HitsWithin (G : ChildGraph ℕ) (d : ℕ) : Prop :=
  ∀ p : ℕ → ℕ, p 0 = 0 → G.IsPath p → ∃ n ≤ d, G.target (p n)

theorem chain_path_eq {N : ℕ} {p : ℕ → ℕ} (hp0 : p 0 = 0) (hpath : (chain N).IsPath p) :
    ∀ n, p n = min n N := by
  intro n
  induction n with
  | zero => simp [hp0]
  | succ n ih =>
    have h : p (n + 1) = if p n < N then p n + 1 else p n := hpath n
    rw [h, ih]
    split_ifs with hlt <;> omega

/-- The path `n ↦ min n N` is admissible in `chain N`. -/
theorem chain_isPath (N : ℕ) : (chain N).IsPath (fun n => min n N) := by
  intro n
  show min (n + 1) N = if min n N < N then min n N + 1 else min n N
  split_ifs with hlt <;> omega

/-- Every member of the family satisfies (A), with hitting time at most `N`. -/
theorem chain_hitsWithin (N : ℕ) : HitsWithin (chain N) N := fun p hp0 hpath =>
  ⟨N, le_rfl, by
    show N ≤ p N
    rw [chain_path_eq hp0 hpath N]
    simp⟩

theorem chain_inevitable (N : ℕ) : (chain N).Inevitable 0 := fun p hp0 hpath =>
  let ⟨n, _, hn⟩ := chain_hitsWithin N p hp0 hpath
  ⟨n, hn⟩

/-- The hitting time of `chain N` is not below `N`. -/
theorem chain_not_hitsWithin {N d : ℕ} (h : d < N) : ¬ HitsWithin (chain N) d := fun hd => by
  obtain ⟨n, hn, ht⟩ := hd (fun n => min n N) (by simp) (chain_isPath N)
  have : N ≤ min n N := ht
  omega

/-- **Finite at each parameter is not uniform.**  Each `chain N` meets a target
within some depth, and no depth serves the whole family: `∀ N ∃ d` holds and
`∃ d ∀ N` fails. -/
theorem chain_not_uniform :
    (∀ N, ∃ d, HitsWithin (chain N) d) ∧ ¬ ∃ d, ∀ N, HitsWithin (chain N) d :=
  ⟨fun N => ⟨N, chain_hitsWithin N⟩, fun ⟨d, hd⟩ => chain_not_hitsWithin (Nat.lt_succ_self d) (hd (d + 1))⟩

/-- **Bounded depth does not separate the family from its limit.**  On the
states below `N`, `chain N` and the target-free `ray` have the same children
and the same targets: an inspection to depth `< N` cannot tell the member
`chain N`, which satisfies (A), from `ray`, where no state is productive. -/
theorem chain_agrees_with_ray {N a : ℕ} (h : a < N) :
    (∀ b, (chain N).child a b ↔ ray.child a b) ∧ ((chain N).target a ↔ ray.target a) := by
  refine ⟨fun b => ?_, ?_⟩
  · show (b = if a < N then a + 1 else a) ↔ b = a + 1
    simp [h]
  · show N ≤ a ↔ False
    exact iff_false_intro (Nat.not_le.2 h)

/-! ## Null strict mass is not emptiness -/

/-- A child graph with multiplicities and a mass: `children s` lists the
children of `s` with repetition, `h` is a mass on states and `θ` the inflation
factor. -/
structure MassGraph (S : Type u) where
  children : S → List S
  target : S → Prop
  h : S → ℚ
  θ : ℚ

namespace MassGraph

variable {S : Type u} (M : MassGraph S)

/-- The underlying child graph. -/
def toChildGraph : ChildGraph S where
  child s t := t ∈ M.children s
  target := M.target

open Classical in
/-- The mass of the non-target descendants of `s` at level `n`, with
multiplicity. -/
noncomputable def strictMass : ℕ → S → ℚ
  | 0, s => if M.target s then 0 else M.h s
  | n + 1, s => ((M.children s).map (strictMass n)).sum

/-- The mass of all descendants of `s` at level `n`, with multiplicity. -/
def totalMass : ℕ → S → ℚ
  | 0, s => M.h s
  | n + 1, s => ((M.children s).map (totalMass n)).sum

/-- **Conservation**: the mass of a state is carried, at rate `θ`, by its
children. -/
def Conserved : Prop := ∀ s, M.θ * M.h s = ((M.children s).map M.h).sum

/-- **Null strict mass** below `s`: the strict mass at level `n` is `o(θⁿ)`. -/
def NullStrict (s : S) : Prop := ∀ ε > 0, ∃ N, ∀ n ≥ N, M.strictMass n s < ε * M.θ ^ n

variable {M}

theorem totalMass_eq (hc : M.Conserved) (n : ℕ) (s : S) :
    M.totalMass n s = M.θ ^ n * M.h s := by
  induction n generalizing s with
  | zero => simp [totalMass]
  | succ n ih =>
    have : (M.children s).map (M.totalMass n) = (M.children s).map fun c => M.θ ^ n * M.h c :=
      List.map_congr_left fun c _ => ih c
    rw [totalMass, this, List.sum_map_mul_left, ← hc s]
    ring

theorem strictMass_nonneg (hh : ∀ s, 0 ≤ M.h s) (n : ℕ) (s : S) : 0 ≤ M.strictMass n s := by
  induction n generalizing s with
  | zero =>
    rw [strictMass]
    split_ifs
    · exact le_rfl
    · exact hh s
  | succ n ih =>
    rw [strictMass]
    exact List.sum_nonneg fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact ih c

/-- **A strict closed set keeps all its mass.**  Under conservation, the strict
mass below a state of a strict closed set is its whole mass, `θⁿ h(s)`, at
every level. -/
theorem strictMass_of_strictClosed (hc : M.Conserved) {C : Set S}
    (hC : M.toChildGraph.StrictClosed C) (n : ℕ) {s : S} (hs : s ∈ C) :
    M.strictMass n s = M.θ ^ n * M.h s := by
  induction n generalizing s with
  | zero =>
    have : ¬ M.target s := hC.strict s hs
    simp [strictMass, this]
  | succ n ih =>
    have : (M.children s).map (M.strictMass n) = (M.children s).map fun c => M.θ ^ n * M.h c :=
      List.map_congr_left fun c hcs => ih (hC.closed hs hcs)
    rw [strictMass, this, List.sum_map_mul_left, ← hc s]
    ring

/-- The strict mass below a child bounds the strict mass below its parent one
level later. -/
theorem strictMass_child_le (hh : ∀ s, 0 ≤ M.h s) {s c : S} (hsc : c ∈ M.children s) (n : ℕ) :
    M.strictMass n c ≤ M.strictMass (n + 1) s := by
  rw [strictMass]
  exact List.single_le_sum (fun x hx => by
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
    exact strictMass_nonneg hh n d) _ (List.mem_map.2 ⟨c, hsc, rfl⟩)

/-- The strict mass below a reachable state persists below the root, some fixed
number of levels later. -/
theorem exists_strictMass_le (hh : ∀ s, 0 ≤ M.h s) {s t : S} (hst : M.toChildGraph.Reach s t) :
    ∃ k, ∀ n, M.strictMass n t ≤ M.strictMass (k + n) s := by
  induction hst using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, fun n => by rw [Nat.zero_add]⟩
  | head hac _ ih =>
    obtain ⟨k, hk⟩ := ih
    refine ⟨k + 1, fun n => (hk n).trans ?_⟩
    rw [show k + 1 + n = k + n + 1 by omega]
    exact strictMass_child_le hh hac (k + n)

/-- **Null strict mass gives (AE), and needs positivity and conservation.**  If
the mass is positive and conserved and the strict mass below `s` is `o(θⁿ)`,
every state reachable from `s` is productive: a reachable strict closed set
would keep a mass `θⁿ h(t)` forever.  The conclusion is (AE), not (A)
(`lassoMass_null_not_inevitable`), and it fails without conservation
(`slow_null_not_hereditarilyProductive`). -/
theorem hereditarilyProductive_of_nullStrict (hpos : ∀ s, 0 < M.h s) (hθ : 0 < M.θ)
    (hc : M.Conserved) {s : S} (hnull : M.NullStrict s) :
    M.toChildGraph.HereditarilyProductive s := by
  rw [hereditarilyProductive_iff_no_strictClosed]
  rintro ⟨C, hC, t, ht, hst⟩
  obtain ⟨k, hk⟩ := exists_strictMass_le (fun s => (hpos s).le) hst
  obtain ⟨N, hN⟩ := hnull (M.h t / M.θ ^ k) (div_pos (hpos t) (pow_pos hθ k))
  have h1 := hN (k + N) (Nat.le_add_left N k)
  have h2 := hk N
  rw [strictMass_of_strictClosed hc hC N ht] at h2
  have h3 : M.h t / M.θ ^ k * M.θ ^ (k + N) = M.θ ^ N * M.h t := by
    rw [pow_add]
    field_simp
  rw [h3] at h1
  exact absurd h2 (not_le.2 h1)

end MassGraph

open MassGraph

/-- For every `ε > 0`, eventually `1 < ε · 2ⁿ`. -/
theorem eventually_one_lt_mul_two_pow {ε : ℚ} (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, (1 : ℚ) < ε * 2 ^ n := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (1 / ε) (by norm_num : (1 : ℚ) < 2)
  refine ⟨N, fun n hn => ?_⟩
  have h2 : (2 : ℚ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h3 : 1 / ε < 2 ^ n := lt_of_lt_of_le hN h2
  rw [div_lt_iff₀ hε] at h3
  linarith

/-! ### `lassoMass`: null strict mass, and a strict path -/

/-- `lasso` with multiplicities: `false ↦ [false, true]`, `true ↦ [true, true]`,
unit mass, `θ = 2`. -/
def lassoMass : MassGraph Bool where
  children a := if a then [true, true] else [false, true]
  target a := a = true
  h _ := 1
  θ := 2

theorem lassoMass_conserved : lassoMass.Conserved := by
  intro a
  cases a <;> norm_num [lassoMass]

theorem lassoMass_strictMass_true (n : ℕ) : lassoMass.strictMass n true = 0 := by
  induction n with
  | zero => simp [strictMass, lassoMass]
  | succ n ih =>
    rw [strictMass, show lassoMass.children true = [true, true] from rfl]
    simp [ih]

/-- Exactly one unit of strict mass survives at every level. -/
theorem lassoMass_strictMass_false (n : ℕ) : lassoMass.strictMass n false = 1 := by
  induction n with
  | zero => simp [strictMass, lassoMass]
  | succ n ih =>
    rw [strictMass, show lassoMass.children false = [false, true] from rfl]
    simp [ih, lassoMass_strictMass_true]

theorem lassoMass_totalMass (n : ℕ) (a : Bool) : lassoMass.totalMass n a = 2 ^ n := by
  rw [totalMass_eq lassoMass_conserved]
  simp [lassoMass]

theorem lassoMass_nullStrict : lassoMass.NullStrict false := fun ε hε => by
  obtain ⟨N, hN⟩ := eventually_one_lt_mul_two_pow hε
  exact ⟨N, fun n hn => by rw [lassoMass_strictMass_false]; exact hN n hn⟩

/-- **Null is not empty.**  In `lassoMass` the mass is positive and conserved
and the strict mass below `false` is one unit out of `2ⁿ` at level `n`: it is
null and never zero, every state is hereditarily productive, and an admissible
path from `false` never meets the target. -/
theorem lassoMass_null_not_inevitable :
    lassoMass.Conserved ∧ lassoMass.NullStrict false ∧
      (∀ n, lassoMass.strictMass n false = 1 ∧ lassoMass.totalMass n false = 2 ^ n) ∧
      lassoMass.toChildGraph.HereditarilyProductive false ∧
      ¬ lassoMass.toChildGraph.Inevitable false := by
  refine ⟨lassoMass_conserved, lassoMass_nullStrict,
    fun n => ⟨lassoMass_strictMass_false n, lassoMass_totalMass n false⟩,
    hereditarilyProductive_of_nullStrict (fun _ => one_pos) two_pos lassoMass_conserved
      lassoMass_nullStrict, fun h => ?_⟩
  obtain ⟨n, hn⟩ := h (fun _ => false) rfl fun _ => by
    show false ∈ lassoMass.children false
    simp [lassoMass]
  exact Bool.false_ne_true hn

/-! ### `slow`: null strict mass without conservation, and a strict closed set -/

/-- `root ↦ [bad, good]`, `good ↦ [good, good]`, `bad ↦ [bad]`, unit mass,
`θ = 2`: the strict state `bad` does not grow at the rate `θ`. -/
def slow : MassGraph Fork where
  children a :=
    match a with
    | .root => [.bad, .good]
    | .good => [.good, .good]
    | .bad => [.bad]
  target a := a = .good
  h _ := 1
  θ := 2

theorem slow_strictMass_good (n : ℕ) : slow.strictMass n .good = 0 := by
  induction n with
  | zero => simp [strictMass, slow]
  | succ n ih =>
    rw [strictMass, show slow.children .good = [.good, .good] from rfl]
    simp [ih]

theorem slow_strictMass_bad (n : ℕ) : slow.strictMass n .bad = 1 := by
  induction n with
  | zero => simp [strictMass, slow]
  | succ n ih =>
    rw [strictMass, show slow.children .bad = [.bad] from rfl]
    simp [ih]

theorem slow_strictMass_root (n : ℕ) : slow.strictMass n .root = 1 := by
  cases n with
  | zero => simp [strictMass, slow]
  | succ n =>
    rw [strictMass, show slow.children .root = [.bad, .good] from rfl]
    simp [slow_strictMass_bad, slow_strictMass_good]

theorem slow_strictClosed : slow.toChildGraph.StrictClosed {Fork.bad} where
  nonempty := ⟨.bad, rfl⟩
  closed := by
    rintro a b (rfl : a = .bad) (hab : b ∈ [Fork.bad])
    simpa using hab
  strict := by
    rintro a (rfl : a = .bad) (h : Fork.bad = Fork.good)
    exact absurd h (by decide)

/-- **Null strict mass without conservation does not give (AE).**  In `slow` the
strict mass below the root is one unit at every level, null against `2ⁿ`; the
mass is positive; conservation fails at `bad`; and `bad` is a reachable strict
closed set, so the root is not hereditarily productive. -/
theorem slow_null_not_hereditarilyProductive :
    slow.NullStrict .root ∧ (∀ a, 0 < slow.h a) ∧ ¬ slow.Conserved ∧
      slow.toChildGraph.StrictClosed {Fork.bad} ∧
      ¬ slow.toChildGraph.HereditarilyProductive .root := by
  refine ⟨fun ε hε => ?_, fun _ => one_pos, fun hc => ?_, slow_strictClosed, fun h => ?_⟩
  · obtain ⟨N, hN⟩ := eventually_one_lt_mul_two_pow hε
    exact ⟨N, fun n hn => by rw [slow_strictMass_root]; exact hN n hn⟩
  · have := hc .bad
    norm_num [slow] at this
  · exact slow_strictClosed.not_productive rfl
      (h .bad (.single (show Fork.bad ∈ slow.children .root by simp [slow])))

end Psc.QuantifierInterface

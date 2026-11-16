import PscVerif.QuantifierInterface
import PscVerif.QuotientDistance

/-!
# Refinement of child graphs: completeness, soundness, path lifting

An *actual* child graph `G` on `X` (literal occurrences) is compared with a
*quotient* child graph `P` on `Y` (packets, types, labels) through a projection
`π : X → Y`.  Three obligations are routinely run together; they are different
statements with different consequences.

* **Completeness** (`Complete`): every actual edge has its quotient edge.
  The quotient has dropped nothing.
* **Soundness**: every quotient edge is realised by an actual edge, in one of
  two strengths: from **some** source of the fibre (`SoundSome`), or from
  **every** source of the fibre (`SoundEvery`).
* **Path lifting**: every infinite quotient path from `π x` is the projection
  of an actual path from `x` (`LiftsPaths x`), or only every finite prefix of it
  is (`LiftsPrefixes x`).

What each gives, for the readings of `Psc.QuantifierInterface`:

| Hypotheses | Transfer |
| --- | --- |
| `Complete`, targets preserved | (E) at `x` ⇒ (E) at `π x` |
| `Complete`, targets reflected | (A) at `π x` ⇒ (A) at `x` |
| `SoundEvery`, targets reflected | (E) at `π x` ⇒ (E) at `x` |
| `SoundEvery` | `LiftsPaths x` for every `x` (dependent choice) |
| `LiftsPaths x`, targets preserved | (A) at `x` ⇒ (A) at `π x` |
| `Complete`, `SoundEvery`, targets preserved | (AE) at `x` ⇒ (AE) at `π x` |
| `Complete`, `SoundEvery`, targets reflected | (AE) at `π x` ⇒ (AE) at `x` |
| `Complete`, `SoundEvery`, targets reflected | (AE°) at `π x` ⇒ (AE°) at `x` |
| `LiftsPrefixes x`, finitely many children at each actual state | `LiftsPaths x` (König) |

Countermodels, each a theorem below:

* `dropped`: sound from every source and not complete; (AE) holds in the
  quotient and fails in the actual graph.  A quotient that omits a child
  proves nothing about every descendant.
* `undrawn`: sound from every source and not complete; (AE) holds in the
  actual graph and fails in the quotient.
* `overdrawn`: complete and not sound; (E) and (AE) hold in the quotient and
  fail in the actual graph.  `overdrawnFork`: complete and not sound; (AE) holds
  in the actual graph and fails in the quotient.
* `broken`: complete and sound from some source, not from every source; each
  edge of a quotient path to the target is realised and no actual path is.
* `unroll`: complete and sound from every source; the quotient has a cycle and
  the actual graph has none.  A quotient cycle is realised as an infinite
  actual path, not as an actual cycle, and (AE°) does not transfer from the
  actual graph to the quotient.
* `tail`: the same with a finite actual graph; the source of a cyclic quotient
  state reaches a cycle and does not lie on one.
* `fan`: complete; every finite prefix of the quotient path lifts and the
  infinite path does not; the actual root has infinitely many children.

`PscVerif.QuotientDistance.Refinement` is the instance on finite index types
(`quotientDistance_iff`): its `projects` is `Complete`, its `lifts` is
`SoundEvery`, and its `terminal_iff` is `TargetDown` with `TargetUp`.

Graph logic only.  Nothing here says that any particular packet graph is a
refinement of any occurrence graph.
-/

namespace Psc.GraphRefinement

open Psc.QuantifierInterface Psc.QuantifierInterface.ChildGraph

universe u v

variable {X : Type u} {Y : Type v}

/-- **Completeness**: every actual edge projects to a quotient edge. -/
def Complete (G : ChildGraph X) (P : ChildGraph Y) (π : X → Y) : Prop :=
  ∀ ⦃x x'⦄, G.child x x' → P.child (π x) (π x')

/-- **Soundness from some source**: every quotient edge is the projection of an
actual edge. -/
def SoundSome (G : ChildGraph X) (P : ChildGraph Y) (π : X → Y) : Prop :=
  ∀ ⦃y y'⦄, P.child y y' → ∃ x x', π x = y ∧ π x' = y' ∧ G.child x x'

/-- **Soundness from every source**: every quotient edge out of `π x` is the
projection of an actual edge out of `x`. -/
def SoundEvery (G : ChildGraph X) (P : ChildGraph Y) (π : X → Y) : Prop :=
  ∀ x ⦃y'⦄, P.child (π x) y' → ∃ x', G.child x x' ∧ π x' = y'

/-- Targets are preserved by the projection. -/
def TargetDown (G : ChildGraph X) (P : ChildGraph Y) (π : X → Y) : Prop :=
  ∀ x, G.target x → P.target (π x)

/-- Targets are reflected by the projection. -/
def TargetUp (G : ChildGraph X) (P : ChildGraph Y) (π : X → Y) : Prop :=
  ∀ x, P.target (π x) → G.target x

/-- **Infinite path lifting** at `x`: every infinite quotient path from `π x`
is the projection of an actual path from `x`. -/
def LiftsPaths (G : ChildGraph X) (P : ChildGraph Y) (π : X → Y) (x : X) : Prop :=
  ∀ q : ℕ → Y, q 0 = π x → P.IsPath q →
    ∃ p : ℕ → X, p 0 = x ∧ G.IsPath p ∧ ∀ n, π (p n) = q n

/-- `p` lifts the first `n` steps of `q`, read from time `k`, starting at
`a`. -/
def PrefixLift (G : ChildGraph X) (π : X → Y) (q : ℕ → Y) (n : ℕ) (a : X) (k : ℕ) : Prop :=
  ∃ p : ℕ → X, p 0 = a ∧ (∀ i < n, G.child (p i) (p (i + 1))) ∧ ∀ i ≤ n, π (p i) = q (k + i)

/-- **Finite path lifting** at `x`: every finite prefix of every infinite
quotient path from `π x` is the projection of an actual path from `x`. -/
def LiftsPrefixes (G : ChildGraph X) (P : ChildGraph Y) (π : X → Y) (x : X) : Prop :=
  ∀ q : ℕ → Y, q 0 = π x → P.IsPath q → ∀ n, PrefixLift G π q n x 0

variable {G : ChildGraph X} {P : ChildGraph Y} {π : X → Y} {x : X}

/-! ### Completeness -/

theorem Complete.reach (hC : Complete G P π) {x x' : X} (h : G.Reach x x') :
    P.Reach (π x) (π x') := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail (hC hbc)

theorem Complete.transGen (hC : Complete G P π) {x x' : X}
    (h : Relation.TransGen G.child x x') : Relation.TransGen P.child (π x) (π x') := by
  induction h with
  | single h => exact .single (hC h)
  | tail _ hbc ih => exact ih.tail (hC hbc)

/-- Completeness projects (E), when targets are preserved. -/
theorem Complete.productive (hC : Complete G P π) (hT : TargetDown G P π)
    (h : G.Productive x) : P.Productive (π x) :=
  let ⟨t, hxt, ht⟩ := h
  ⟨π t, hC.reach hxt, hT t ht⟩

theorem Complete.isPath (hC : Complete G P π) {p : ℕ → X} (hp : G.IsPath p) :
    P.IsPath fun n => π (p n) :=
  fun n => hC (hp n)

/-- Completeness pulls (A) back, when targets are reflected. -/
theorem Complete.inevitable (hC : Complete G P π) (hT : TargetUp G P π)
    (h : P.Inevitable (π x)) : G.Inevitable x := fun p hp0 hp =>
  let ⟨n, hn⟩ := h (fun n => π (p n)) (congrArg π hp0) (hC.isPath hp)
  ⟨n, hT (p n) hn⟩

/-! ### Soundness from every source -/

theorem SoundEvery.reach_lift (hS : SoundEvery G P π) {y : Y} (h : P.Reach (π x) y) :
    ∃ x', G.Reach x x' ∧ π x' = y := by
  induction h with
  | refl => exact ⟨x, .refl, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨b, hxb, rfl⟩ := ih
    obtain ⟨c, hbc', hc⟩ := hS b hbc
    exact ⟨c, hxb.tail hbc', hc⟩

/-- Soundness from every source lifts (E), when targets are reflected. -/
theorem SoundEvery.productive (hS : SoundEvery G P π) (hT : TargetUp G P π)
    (h : P.Productive (π x)) : G.Productive x := by
  obtain ⟨y, hxy, hy⟩ := h
  obtain ⟨x', hxx', rfl⟩ := hS.reach_lift hxy
  exact ⟨x', hxx', hT x' hy⟩

/-- **Soundness from every source gives infinite path lifting** (dependent
choice): no separate obligation remains. -/
theorem SoundEvery.liftsPaths (hS : SoundEvery G P π) (x : X) : LiftsPaths G P π x := by
  intro q hq0 hq
  have next : ∀ a : {a : X × ℕ // π a.1 = q a.2},
      ∃ b : {b : X × ℕ // π b.1 = q b.2}, G.child a.1.1 b.1.1 ∧ b.1.2 = a.1.2 + 1 := by
    rintro ⟨⟨a, n⟩, ha⟩
    have hstep : P.child (π a) (q (n + 1)) := by
      have := hq n
      rwa [← show π a = q n from ha] at this
    obtain ⟨b, hab, hb⟩ := hS a hstep
    exact ⟨⟨(b, n + 1), hb⟩, hab, rfl⟩
  choose f hf using next
  let s : ℕ → {a : X × ℕ // π a.1 = q a.2} := fun n => f^[n] ⟨(x, 0), hq0.symm⟩
  have hidx : ∀ n, (s n).1.2 = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show (f^[n + 1] _).1.2 = n + 1
      rw [Function.iterate_succ_apply', (hf _).2]
      exact congrArg (· + 1) ih
  refine ⟨fun n => (s n).1.1, rfl, fun n => ?_, fun n => ?_⟩
  · show G.child (f^[n] _).1.1 (f^[n + 1] _).1.1
    rw [Function.iterate_succ_apply']
    exact (hf _).1
  · have := (s n).2
    rwa [hidx n] at this

/-- Infinite path lifting pushes (A) forward, when targets are preserved. -/
theorem LiftsPaths.inevitable (hL : LiftsPaths G P π x) (hT : TargetDown G P π)
    (h : G.Inevitable x) : P.Inevitable (π x) := fun q hq0 hq =>
  let ⟨p, hp0, hp, hpq⟩ := hL q hq0 hq
  let ⟨n, hn⟩ := h p hp0 hp
  ⟨n, hpq n ▸ hT (p n) hn⟩

/-! ### Completeness and soundness from every source -/

/-- (AE) projects, under completeness, soundness from every source and
preservation of targets.  Neither completeness nor soundness can be dropped
(`undrawn_hereditarilyProductive`, `overdrawnFork_hereditarilyProductive`). -/
theorem hereditarilyProductive_project (hC : Complete G P π) (hS : SoundEvery G P π)
    (hTd : TargetDown G P π) (h : G.HereditarilyProductive x) :
    P.HereditarilyProductive (π x) := by
  intro y hy
  obtain ⟨x', hxx', rfl⟩ := hS.reach_lift hy
  exact hC.productive hTd (h x' hxx')

/-- (AE) lifts, under completeness, soundness from every source and reflection
of targets.  Neither completeness nor soundness can be dropped
(`dropped_hereditarilyProductive`, `overdrawn_productive`). -/
theorem hereditarilyProductive_lift (hC : Complete G P π) (hS : SoundEvery G P π)
    (hTu : TargetUp G P π) (h : P.HereditarilyProductive (π x)) :
    G.HereditarilyProductive x :=
  fun x' hxx' => hS.productive hTu (h (π x') (hC.reach hxx'))

/-- **(AE) is invariant** under a complete projection that is sound from every
source and preserves and reflects targets. -/
theorem hereditarilyProductive_iff (hC : Complete G P π) (hS : SoundEvery G P π)
    (hTd : TargetDown G P π) (hTu : TargetUp G P π) :
    G.HereditarilyProductive x ↔ P.HereditarilyProductive (π x) :=
  ⟨hereditarilyProductive_project hC hS hTd, hereditarilyProductive_lift hC hS hTu⟩

/-- **(A) is invariant** under the same hypotheses. -/
theorem inevitable_iff (hC : Complete G P π) (hS : SoundEvery G P π)
    (hTd : TargetDown G P π) (hTu : TargetUp G P π) :
    G.Inevitable x ↔ P.Inevitable (π x) :=
  ⟨(hS.liftsPaths x).inevitable hTd, hC.inevitable hTu⟩

/-- (AE°) pulls back: a cyclic actual state projects to a cyclic quotient
state.  The converse fails (`unroll_cyclicProductive`). -/
theorem cyclicProductive_of_quotient (hC : Complete G P π) (hS : SoundEvery G P π)
    (hTu : TargetUp G P π) (h : P.CyclicProductive (π x)) : G.CyclicProductive x :=
  fun t hxt hc => hS.productive hTu (h (π t) (hC.reach hxt) (hC.transGen hc))

/-! ### König: finite prefixes to an infinite lift -/

theorem PrefixLift.mono {q : ℕ → Y} {n : ℕ} {a : X} {k : ℕ}
    (h : PrefixLift G π q (n + 1) a k) : PrefixLift G π q n a k :=
  let ⟨p, hp0, hp, hpq⟩ := h
  ⟨p, hp0, fun i hi => hp i (Nat.lt_succ_of_lt hi), fun i hi => hpq i (Nat.le_succ_of_le hi)⟩

theorem PrefixLift.mono_le {q : ℕ → Y} {m n : ℕ} {a : X} {k : ℕ} (hmn : m ≤ n)
    (h : PrefixLift G π q n a k) : PrefixLift G π q m a k := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih h.mono

/-- A lift of `n + 1` steps from `a` passes through a child of `a` from which
`n` steps lift. -/
theorem PrefixLift.child {q : ℕ → Y} {n : ℕ} {a : X} {k : ℕ}
    (h : PrefixLift G π q (n + 1) a k) :
    ∃ c, G.child a c ∧ PrefixLift G π q n c (k + 1) := by
  obtain ⟨p, hp0, hp, hpq⟩ := h
  refine ⟨p 1, hp0 ▸ hp 0 (Nat.succ_pos n), fun i => p (i + 1), rfl,
    fun i hi => hp (i + 1) (Nat.succ_lt_succ hi), fun i hi => ?_⟩
  have := hpq (i + 1) (Nat.succ_le_succ hi)
  rwa [show k + (i + 1) = k + 1 + i by omega] at this

/-- **König step.**  If `a` has finitely many children and every finite prefix
lifts from `a`, some child of `a` has the same property one step later. -/
theorem exists_child_prefixLift {q : ℕ → Y} {a : X} {k : ℕ}
    (hfin : {c | G.child a c}.Finite) (h : ∀ n, PrefixLift G π q n a k) :
    ∃ c, G.child a c ∧ ∀ n, PrefixLift G π q n c (k + 1) := by
  by_contra hno
  have hbad : ∀ c, G.child a c → ∃ n, ¬ PrefixLift G π q n c (k + 1) := by
    intro c hc
    by_contra hall
    exact hno ⟨c, hc, fun n => by_contra fun hn => hall ⟨n, hn⟩⟩
  classical
  let f : X → ℕ := fun c => if hc : G.child a c then Classical.choose (hbad c hc) else 0
  obtain ⟨c, hac, hc⟩ := (h (hfin.toFinset.sup f + 1)).child
  have hle : f c ≤ hfin.toFinset.sup f := Finset.le_sup (hfin.mem_toFinset.2 hac)
  have hfc : ¬ PrefixLift G π q (f c) c (k + 1) := by
    have := Classical.choose_spec (hbad c hac)
    simpa [f, hac] using this
  exact hfc (hc.mono_le hle)

/-- **König's lemma for path lifting.**  If every actual state has finitely many
children, finite path lifting at `x` gives infinite path lifting at `x`.  The
finiteness hypothesis cannot be dropped (`fan_no_lift`). -/
theorem liftsPaths_of_liftsPrefixes (hfin : ∀ a, {c | G.child a c}.Finite)
    (h : LiftsPrefixes G P π x) : LiftsPaths G P π x := by
  intro q hq0 hq
  have next : ∀ a : {a : X × ℕ // ∀ n, PrefixLift G π q n a.1 a.2},
      ∃ b : {b : X × ℕ // ∀ n, PrefixLift G π q n b.1 b.2},
        G.child a.1.1 b.1.1 ∧ b.1.2 = a.1.2 + 1 := by
    rintro ⟨⟨a, k⟩, ha⟩
    obtain ⟨c, hac, hc⟩ := exists_child_prefixLift (hfin a) ha
    exact ⟨⟨(c, k + 1), hc⟩, hac, rfl⟩
  choose f hf using next
  let s : ℕ → {a : X × ℕ // ∀ n, PrefixLift G π q n a.1 a.2} :=
    fun n => f^[n] ⟨(x, 0), h q hq0 hq⟩
  have hidx : ∀ n, (s n).1.2 = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show (f^[n + 1] _).1.2 = n + 1
      rw [Function.iterate_succ_apply', (hf _).2]
      exact congrArg (· + 1) ih
  refine ⟨fun n => (s n).1.1, rfl, fun n => ?_, fun n => ?_⟩
  · show G.child (f^[n] _).1.1 (f^[n + 1] _).1.1
    rw [Function.iterate_succ_apply']
    exact (hf _).1
  · obtain ⟨p, hp0, -, hpq⟩ := (s n).2 0
    have := hpq 0 le_rfl
    rw [hp0, hidx n, Nat.add_zero] at this
    exact this

/-! ### The finite functional instance -/

/-- `PscVerif.QuotientDistance.Refinement` is the instance of these obligations
on finite index types: `projects` is completeness, `lifts` is soundness from
every source, and `terminal_iff` is preservation and reflection of targets. -/
theorem quotientDistance_iff {n m : ℕ} {actual : Fin n → Fin n → Prop}
    {quotient : Fin m → Fin m → Prop} {typed : Fin n → Prop} {terminal : Fin m → Prop}
    {project : Fin n → Fin m} :
    PscVerif.QuotientDistance.Refinement actual quotient typed terminal project ↔
      Complete ⟨actual, typed⟩ ⟨quotient, terminal⟩ project ∧
        SoundEvery ⟨actual, typed⟩ ⟨quotient, terminal⟩ project ∧
        TargetDown ⟨actual, typed⟩ ⟨quotient, terminal⟩ project ∧
        TargetUp ⟨actual, typed⟩ ⟨quotient, terminal⟩ project :=
  ⟨fun h => ⟨fun u v huv => h.projects u v huv, fun u q hq => h.lifts u q hq,
      fun u hu => (h.terminal_iff u).1 hu, fun u hu => (h.terminal_iff u).2 hu⟩,
    fun ⟨hC, hS, hTd, hTu⟩ => ⟨fun _ _ huv => hC huv, fun u _ hq => hS u hq,
      fun u => ⟨hTd u, hTu u⟩⟩⟩

/-- Under a `PscVerif.QuotientDistance.Refinement`, (AE) and (A) at an actual
state are (AE) and (A) at its projection. -/
theorem quotientDistance_invariant {n m : ℕ} {actual : Fin n → Fin n → Prop}
    {quotient : Fin m → Fin m → Prop} {typed : Fin n → Prop} {terminal : Fin m → Prop}
    {project : Fin n → Fin m}
    (h : PscVerif.QuotientDistance.Refinement actual quotient typed terminal project)
    (u : Fin n) :
    ((⟨actual, typed⟩ : ChildGraph (Fin n)).HereditarilyProductive u ↔
        (⟨quotient, terminal⟩ : ChildGraph (Fin m)).HereditarilyProductive (project u)) ∧
      ((⟨actual, typed⟩ : ChildGraph (Fin n)).Inevitable u ↔
        (⟨quotient, terminal⟩ : ChildGraph (Fin m)).Inevitable (project u)) :=
  let ⟨hC, hS, hTd, hTu⟩ := quotientDistance_iff.1 h
  ⟨hereditarilyProductive_iff hC hS hTd hTu, inevitable_iff hC hS hTd hTu⟩

/-! ## Countermodels -/

/-! ### `dropped`: sound, not complete -/

/-- `fork` with the edge `root → bad` removed: a quotient that omits a child. -/
def forkDropped : ChildGraph Fork where
  child a b :=
    match a with
    | .root => b = .good
    | .good => b = .good
    | .bad => b = .bad
  target a := a = .good

theorem dropped_soundEvery : SoundEvery fork forkDropped id := by
  intro a b hab
  refine ⟨b, ?_, rfl⟩
  cases a with
  | root => exact Or.inl hab
  | good => exact hab
  | bad => exact hab

theorem dropped_not_complete : ¬ Complete fork forkDropped id := fun hC => by
  have h : Fork.bad = Fork.good := hC (show fork.child .root .bad from Or.inr rfl)
  exact absurd h (by decide)

theorem forkDropped_reach_root {t : Fork} (h : forkDropped.Reach .root t) :
    t = .root ∨ t = .good := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
    rcases ih with rfl | rfl
    · exact Or.inr hbc
    · exact Or.inr hbc

/-- **A quotient that dropped a child proves nothing about every descendant.**
The projection is the identity, sound from every source and with the same
targets; (AE) holds at the root of the quotient and fails at the root of the
actual graph. -/
theorem dropped_hereditarilyProductive :
    SoundEvery fork forkDropped id ∧ ¬ Complete fork forkDropped id ∧
      forkDropped.HereditarilyProductive .root ∧ ¬ fork.HereditarilyProductive .root := by
  refine ⟨dropped_soundEvery, dropped_not_complete, fun t ht => ?_,
    fork_not_hereditarilyProductive.2.2.2⟩
  rcases forkDropped_reach_root ht with rfl | rfl
  · exact ⟨.good, .single rfl, rfl⟩
  · exact productive_of_target rfl

/-! ### `undrawn`: sound, not complete; (AE) does not project -/

/-- Actual: `false → true` with `true` the target.  Quotient: the same two
states and targets with no edge. -/
def step2 : ChildGraph Bool where
  child a b := a = false ∧ b = true
  target a := a = true

/-- Two states, no edge, target `true`. -/
def noEdge : ChildGraph Bool where
  child _ _ := False
  target a := a = true

/-- **Without completeness (AE) does not project.**  The identity onto a
quotient that lost the only edge is sound from every source (vacuously) and
preserves and reflects targets; (AE) holds at the actual state and fails at its
projection. -/
theorem undrawn_hereditarilyProductive :
    SoundEvery step2 noEdge id ∧ TargetDown step2 noEdge id ∧ TargetUp step2 noEdge id ∧
      ¬ Complete step2 noEdge id ∧ step2.HereditarilyProductive false ∧
      ¬ noEdge.HereditarilyProductive false := by
  refine ⟨fun _ _ h => h.elim, fun _ h => h, fun _ h => h,
    fun hC => hC (show step2.child false true from ⟨rfl, rfl⟩), fun t _ => ?_, fun h => ?_⟩
  · cases t with
    | false => exact ⟨true, .single ⟨rfl, rfl⟩, rfl⟩
    | true => exact productive_of_target rfl
  · obtain ⟨t, hft, (ht : t = true)⟩ := h false .refl
    subst ht
    rcases Relation.ReflTransGen.cases_head hft with h | ⟨_, hc, -⟩
    · exact Bool.false_ne_true h
    · exact hc

/-! ### `overdrawn`: complete, not sound -/

/-- **Completeness alone lifts neither (E) nor (AE).**  The actual graph is
`stub` (one non-target with no child), the quotient is `lasso`, the projection
sends the state to the non-target of `lasso`.  The projection is complete
(vacuously) and preserves and reflects targets; (E) and (AE) hold in the
quotient and fail in the actual graph. -/
theorem overdrawn_productive :
    Complete stub lasso (fun _ => false) ∧ TargetDown stub lasso (fun _ => false) ∧
      TargetUp stub lasso (fun _ => false) ∧ ¬ SoundEvery stub lasso (fun _ => false) ∧
      lasso.Productive false ∧ ¬ stub.Productive () ∧
      lasso.HereditarilyProductive false ∧ ¬ stub.HereditarilyProductive () := by
  refine ⟨fun _ _ h => h.elim, fun _ h => h.elim, fun _ (h : false = true) => Bool.false_ne_true h,
    fun hS => ?_, lasso_productive false, stub_inevitable_not_productive.2.2.2,
    lasso_hereditarilyProductive false,
    fun h => stub_inevitable_not_productive.2.2.2 h.productive⟩
  obtain ⟨_, h, -⟩ := hS () (show lasso.child false true from Or.inr rfl)
  exact h

/-- `false ↦ root`, `true ↦ good`. -/
def forkProj : Bool → Fork
  | false => .root
  | true => .good

/-- **Without soundness (AE) does not project.**  `step2` maps into `fork` by
`false ↦ root`, `true ↦ good`: the projection is complete and preserves and
reflects targets, the quotient has the extra edge `root → bad`, and (AE) holds
at the actual state and fails at its projection. -/
theorem overdrawnFork_hereditarilyProductive :
    Complete step2 fork forkProj ∧ TargetDown step2 fork forkProj ∧
      TargetUp step2 fork forkProj ∧ ¬ SoundEvery step2 fork forkProj ∧
      step2.HereditarilyProductive false ∧ ¬ fork.HereditarilyProductive (forkProj false) := by
  refine ⟨?_, ?_, ?_, fun hS => ?_, undrawn_hereditarilyProductive.2.2.2.2.1,
    fork_not_hereditarilyProductive.2.2.2⟩
  · rintro a b ⟨rfl, rfl⟩
    exact Or.inl rfl
  · rintro a (rfl : a = true)
    rfl
  · intro a (h : forkProj a = Fork.good)
    cases a with
    | false => exact absurd h (by decide)
    | true => rfl
  · obtain ⟨b, ⟨-, rfl⟩, hb⟩ := hS false (show fork.child .root .bad from Or.inr rfl)
    exact absurd hb (by decide)

/-! ### `broken`: sound from some source only -/

/-- Actual states: `x₁ → y₁` and `y₂ → z`, with `z` the target. -/
inductive Broken
  | x1 | y1 | y2 | z
  deriving DecidableEq

/-- The actual graph of `broken`. -/
def brokenActual : ChildGraph Broken where
  child a b :=
    match a with
    | .x1 => b = .y1
    | .y2 => b = .z
    | _ => False
  target a := a = .z

/-- The quotient `0 → 1 → 2` with target `2`. -/
def brokenQuotient : ChildGraph (Fin 3) where
  child a b := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 2)
  target a := a = 2

/-- `x₁ ↦ 0`, `y₁, y₂ ↦ 1`, `z ↦ 2`. -/
def brokenProj : Broken → Fin 3
  | .x1 => 0
  | .y1 => 1
  | .y2 => 1
  | .z => 2

theorem broken_complete : Complete brokenActual brokenQuotient brokenProj := by
  intro a b hab
  cases a with
  | x1 =>
    obtain rfl : b = .y1 := hab
    exact Or.inl ⟨rfl, rfl⟩
  | y2 =>
    obtain rfl : b = .z := hab
    exact Or.inr ⟨rfl, rfl⟩
  | y1 => exact hab.elim
  | z => exact hab.elim

theorem broken_soundSome : SoundSome brokenActual brokenQuotient brokenProj := by
  rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact ⟨.x1, .y1, rfl, rfl, rfl⟩
  · exact ⟨.y2, .z, rfl, rfl, rfl⟩

theorem brokenActual_reach_x1 {t : Broken} (h : brokenActual.Reach .x1 t) :
    t = .x1 ∨ t = .y1 := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
    rcases ih with rfl | rfl
    · exact Or.inr hbc
    · exact hbc.elim

/-- **Soundness from some source does not lift a path.**  The projection is
complete, every quotient edge is realised by an actual edge, targets are
preserved and reflected, the quotient state `0` reaches the target, and the
actual state `x₁` above it does not: the two edges are realised by different
occurrences of the middle state. -/
theorem broken_productive :
    Complete brokenActual brokenQuotient brokenProj ∧
      SoundSome brokenActual brokenQuotient brokenProj ∧
      TargetDown brokenActual brokenQuotient brokenProj ∧
      TargetUp brokenActual brokenQuotient brokenProj ∧
      ¬ SoundEvery brokenActual brokenQuotient brokenProj ∧
      brokenQuotient.Productive (brokenProj .x1) ∧ ¬ brokenActual.Productive .x1 := by
  refine ⟨broken_complete, broken_soundSome, ?_, ?_, fun hS => ?_, ?_, ?_⟩
  · rintro a (rfl : a = .z)
    rfl
  · intro a (h : brokenProj a = 2)
    cases a with
    | z => rfl
    | x1 => exact absurd h (by decide)
    | y1 => exact absurd h (by decide)
    | y2 => exact absurd h (by decide)
  · obtain ⟨_, h, -⟩ := hS .y1 (show brokenQuotient.child 1 2 from Or.inr ⟨rfl, rfl⟩)
    exact h
  · exact ⟨2, Relation.ReflTransGen.head (Or.inl ⟨rfl, rfl⟩) (.single (Or.inr ⟨rfl, rfl⟩)), rfl⟩
  · rintro ⟨t, ht, (rfl : t = .z)⟩
    rcases brokenActual_reach_x1 ht with h | h <;> exact absurd h (by decide)

/-! ### `unroll`: a quotient cycle with no actual cycle -/

/-- One non-target state with a self-loop. -/
def loop : ChildGraph Unit where
  child _ _ := True
  target _ := False

theorem unroll_complete : Complete ray loop (fun _ => ()) := fun _ _ _ => trivial

theorem unroll_soundEvery : SoundEvery ray loop (fun _ => ()) :=
  fun a _ _ => ⟨a + 1, rfl, rfl⟩

/-- **A quotient cycle need not be realised by an actual cycle.**  The ray
projects onto the one-state loop; the projection is complete, sound from every
source, and has no targets on either side.  The quotient has a cycle and the
actual graph has none; the quotient cycle lifts to an infinite actual path. -/
theorem unroll_cycle :
    Complete ray loop (fun _ => ()) ∧ SoundEvery ray loop (fun _ => ()) ∧
      Relation.TransGen loop.child () () ∧ (∀ a, ¬ Relation.TransGen ray.child a a) ∧
      LiftsPaths ray loop (fun _ => ()) 0 :=
  ⟨unroll_complete, unroll_soundEvery, .single trivial, ray_no_cycle,
    unroll_soundEvery.liftsPaths 0⟩

/-- **(AE°) does not transfer from the actual graph to the quotient**, even for
a complete projection that is sound from every source: the ray satisfies (AE°)
vacuously and the loop does not. -/
theorem unroll_cyclicProductive :
    ray.CyclicProductive 0 ∧ ¬ loop.CyclicProductive () :=
  ⟨ray_cyclicProductive_vacuous.1,
    fun h => (h () .refl (.single trivial)).elim fun _ ⟨_, ht⟩ => ht⟩

/-! ### `tail`: a cyclic quotient state over a finite actual graph -/

/-- `false → true → true`, no target: a tail leading into a loop. -/
def tail : ChildGraph Bool where
  child _ b := b = true
  target _ := False

/-- **A cyclic quotient state need not have a cyclic source, even when the
actual graph is finite.**  The tail projects onto the one-state loop, completely
and soundly from every source; the quotient state lies on a cycle, the source
`false` does not, and it reaches one. -/
theorem tail_not_cyclic :
    Complete tail loop (fun _ => ()) ∧ SoundEvery tail loop (fun _ => ()) ∧
      Relation.TransGen loop.child () () ∧ ¬ Relation.TransGen tail.child false false ∧
      tail.Reach false true ∧ Relation.TransGen tail.child true true := by
  refine ⟨fun _ _ _ => trivial, fun _ _ _ => ⟨true, rfl, rfl⟩, .single trivial, fun h => ?_,
    .single rfl, .single rfl⟩
  have key : ∀ {a b : Bool}, Relation.TransGen tail.child a b → b = true := by
    intro a b hab
    induction hab with
    | single h => exact h
    | tail _ h _ => exact h
  exact Bool.false_ne_true (key h)

/-! ### `fan`: every finite prefix lifts, the infinite path does not -/

/-- A root `none` with a child `some (n, 0)` for every `n`, and chains
`some (n, 0) → some (n, 1) → ⋯ → some (n, n)`. -/
def fan : ChildGraph (Option (ℕ × ℕ)) where
  child a b :=
    match a with
    | none => ∃ n, b = some (n, 0)
    | some (n, k) => k < n ∧ b = some (n, k + 1)
  target _ := False

/-- The root goes to `0`, the state `(n, k)` to `k + 1`. -/
def fanProj : Option (ℕ × ℕ) → ℕ
  | none => 0
  | some (_, k) => k + 1

theorem fan_complete : Complete fan ray fanProj := by
  intro a b hab
  cases a with
  | none =>
    obtain ⟨n, rfl⟩ := hab
    rfl
  | some nk =>
    obtain ⟨n, k⟩ := nk
    obtain ⟨-, rfl⟩ := hab
    rfl

/-- The only path of the ray from `0` is the identity. -/
theorem ray_path_eq {q : ℕ → ℕ} (hq0 : q 0 = 0) (hq : ray.IsPath q) : ∀ n, q n = n := by
  intro n
  induction n with
  | zero => exact hq0
  | succ n ih =>
    have : q (n + 1) = q n + 1 := hq n
    rw [this, ih]

/-- Every finite prefix of the quotient path lifts from the root, through the
chain of that length. -/
theorem fan_liftsPrefixes : LiftsPrefixes fan ray fanProj none := by
  intro q hq0 hq m
  have hqn := ray_path_eq hq0 hq
  refine ⟨fun i => match i with | 0 => none | i + 1 => some (m, i), rfl, fun i hi => ?_, fun i _ => ?_⟩
  · cases i with
    | zero => exact ⟨m, rfl⟩
    | succ i => exact ⟨by omega, rfl⟩
  · cases i with
    | zero => simp [fanProj, hqn]
    | succ i => simp [fanProj, hqn]

/-- An actual path of `fan` that enters the chain `n` stays on it. -/
theorem fan_path_chain {p : ℕ → Option (ℕ × ℕ)} (hp : fan.IsPath p) {n : ℕ}
    (h1 : p 1 = some (n, 0)) : ∀ i, p (i + 1) = some (n, i) := by
  intro i
  induction i with
  | zero => exact h1
  | succ i ih =>
    have h := hp (i + 1)
    rw [ih] at h
    exact h.2

/-- **Finite path lifting without infinite path lifting.**  The projection is
complete, every finite prefix of the quotient path from `0` lifts from the
root, and no infinite actual path leaves the root at all: the root has
infinitely many children, each starting a finite chain. -/
theorem fan_no_lift :
    Complete fan ray fanProj ∧ LiftsPrefixes fan ray fanProj none ∧
      ray.IsPath (fun n => n) ∧ (¬ ∃ p : ℕ → Option (ℕ × ℕ), p 0 = none ∧ fan.IsPath p) ∧
      ¬ LiftsPaths fan ray fanProj none := by
  have hno : ¬ ∃ p : ℕ → Option (ℕ × ℕ), p 0 = none ∧ fan.IsPath p := by
    rintro ⟨p, hp0, hp⟩
    have h0 := hp 0
    rw [hp0] at h0
    obtain ⟨n, h1⟩ := h0
    have hlast := hp (n + 1)
    rw [fan_path_chain hp h1 n] at hlast
    exact absurd hlast.1 (lt_irrefl n)
  refine ⟨fan_complete, fan_liftsPrefixes, fun _ => rfl, hno, fun hL => ?_⟩
  obtain ⟨p, hp0, hp, -⟩ := hL (fun n => n) rfl fun _ => rfl
  exact hno ⟨p, hp0, hp⟩

/-- The root of `fan` has infinitely many children: the hypothesis of
`liftsPaths_of_liftsPrefixes` fails exactly there. -/
theorem fan_root_infinite : ¬ {c | fan.child none c}.Finite := fun hfin => by
  have hinj : Function.Injective fun n : ℕ => (some (n, 0) : Option (ℕ × ℕ)) :=
    fun i j hij => by simpa using hij
  exact Set.infinite_range_of_injective hinj
    (hfin.subset (by rintro _ ⟨n, rfl⟩; exact ⟨n, rfl⟩))

end Psc.GraphRefinement

import PscVerif.GraphRefinement

/-!
# Refinements and embeddings of child graphs, and the readings they transfer

Additions to `Psc.GraphRefinement` for the packet square (roadmap
immediate-sequence item 2; `docs/packet-square-stop-go-2026-11-10.md`).  The
obligations `Complete`, `SoundSome`, `SoundEvery`, `TargetDown`, `TargetUp`,
`LiftsPaths`, `PrefixLift`, `LiftsPrefixes`, the transfers proved from them and
the countermodels `forkDropped`, `step2`, `noEdge`, `broken`, `loop`, `fan` are
those of `PscVerif.GraphRefinement`, and `fork`, `ray`, `stub` those of
`PscVerif.QuantifierInterface`: imported, not restated.  The one graph defined
here is the countermodel `chains`.

## Two bundles of the same four obligations

* `Refines G P π`: the projection `π` of the actual graph `G` onto the quotient
  `P` is complete, sound from every source, and preserves and reflects targets.
* `Embeds P G e`: the map `e` of a table `P` into the actual graph `G` sends
  every table edge to an actual edge (`sound`), lists every actual child of a
  represented state (`complete`: full child stars), and has the same targets.

`embeds_iff_refines`: the two are one statement, with the table as the actual
side.  So when a table is mapped into an actual graph the words point the
other way: "every listed edge is actual" (`Embeds.sound`) is `Complete` with
the table as source, and "full child stars" (`Embeds.complete`) is
`SoundEvery`.  `Embeds.closed_range`: the image of an embedding is
child-closed.  `refinement_iff_refines`: the `Fin`-indexed
`PscVerif.QuotientDistance.Refinement` is `Refines` on the induced child graphs
(a corollary of `quotientDistance_iff`).

## Transfers added here

`π : X → Y`, actual `G`, quotient `P`.

| Reading | actual `x` ⇒ quotient `π x` | quotient `π x` ⇒ actual `x` |
| --- | --- | --- |
| dead end | `SoundEvery`, `TargetUp` (`deadEnd_down`) | `Complete`, `TargetDown` (`deadEnd_up`) |
| (A), inductive form `Inev` | `SoundEvery`, `TargetDown` (`SoundEvery.inev`) | `Complete`, `TargetUp` (`Complete.inev`) |
| (A⁺) `InevMax` | `Complete`, `SoundEvery`, `TargetDown` (`inevMax_to_quotient`) | `Complete`, `SoundEvery`, `TargetUp` (`inevMax_of_quotient`) |

`Refines.productive_iff`, `Refines.hereditarilyProductive_iff`,
`Refines.inevitable_iff`, `Refines.inevMax_iff` package the four both-way
transfers under `Refines`; (AE°) transfers under `Refines` only from the
quotient to the actual graph (`Refines.cyclicProductive_of_quotient`;
`unroll_cyclicProductive` is the committed countermodel to the other
direction).  For an **injective** embedding (AE°) holds at a table state iff it
holds at its image (`Embeds.cyclicProductive_iff`); injectivity is used once,
to close a lifted actual cycle at its starting row, and it cannot be dropped
(`unroll_embeds`).

Finite path lifting from every source on arbitrary types:
`SoundEvery.prefixLift_finite` lifts every finite quotient path, of exact
length, from every source, including a finite path that extends to no infinite
one (`step2_no_infinite_path`).  It is the analogue, without `Fin`, of
`PscVerif.QuotientDistance.path_lift`, which reads only the `lifts` field
(`SoundEvery`) of a `Refinement`.  `SoundEvery.prefixLift`, the form the brief
fixes, is its corollary for the finite stretches of an infinite quotient path;
`SoundEvery.liftsPrefixes`.  König's lemma for one fixed quotient
path (`exists_path_of_prefixLifts`), and the variant whose prefixes lift from
*some* source of a finite set (`exists_lift_of_finite_sources`, which assumes
both finitely many children at every actual state and a finite set of sources;
neither can be dropped: `fan_finite_sources_no_lift`,
`chains_finite_sources_no_lift`).  The latter is recorded for the generic
picture only: when the set of candidate sources is infinite it gives nothing,
and infinite lifting is then obtained from `SoundEvery` (`SoundEvery.liftsPaths`,
committed) instead.

## Countermodels, each a theorem

* `dropped_inevitable`: sound from every source, not complete, same targets
  (`dropped_targets`); (A) holds at the quotient root and fails at the actual
  root.  `fan_inevitable`: complete, without infinite path lifting, no targets
  on either side (`fan_targets`); (A) holds at the actual root (vacuously: no
  infinite path leaves it) and fails at its projection.
* `broken_liftsPaths_vacuous`: the committed `broken` does **not** separate
  soundness from some source from infinite path lifting; its quotient has no
  infinite path, so `LiftsPaths` holds at every state.  `brokenLoop_no_lift`
  (`step2` onto `loop`): complete and sound from some source, not from every
  source, and the quotient self-loop does not lift.  It reflects targets and
  does not preserve them (`brokenLoop_targets`); `LiftsPaths` does not read
  targets.
* `dropped_inevMax`, `overdrawn_inevMax`, `undrawn_inevMax`,
  `overdrawnFork_inevMax`: neither `Complete` nor `SoundEvery` can be dropped
  from either (A⁺) transfer.
* `unroll_embeds`: a non-injective embedding along which (AE°) holds at the
  table state and fails at its image.
* `fan_finite_sources_no_lift` (one source, a root with infinitely many
  children) and `chains_finite_sources_no_lift` (every state with at most one
  child, infinitely many sources): neither finiteness hypothesis of
  `exists_lift_of_finite_sources` can be dropped.

Graph logic only.  Nothing here says that any packet table embeds into any
occurrence graph, that any packet or occurrence projection is a refinement, or
anything about a substitution.
-/

namespace Psc.GraphRefinement

open Psc.QuantifierInterface Psc.QuantifierInterface.ChildGraph

universe u v

variable {X : Type u} {Y : Type v}

/-! ## Refinement and embedding -/

/-- **Refinement**: `π` projects the actual graph `G` onto the quotient `P`
completely, soundly from every source, preserving and reflecting targets. -/
structure Refines (G : ChildGraph X) (P : ChildGraph Y) (π : X → Y) : Prop where
  complete : Complete G P π
  soundEvery : SoundEvery G P π
  targetDown : TargetDown G P π
  targetUp : TargetUp G P π

/-- **Embedding with full child stars**: `e` maps a table `P` into the actual
graph `G`.  `sound`: every table edge is an actual edge.  `complete`: every
actual child of a represented state is represented by a table child.
`target_iff`: the targets agree. -/
structure Embeds (P : ChildGraph Y) (G : ChildGraph X) (e : Y → X) : Prop where
  sound : ∀ ⦃y y'⦄, P.child y y' → G.child (e y) (e y')
  complete : ∀ y ⦃x'⦄, G.child (e y) x' → ∃ y', P.child y y' ∧ e y' = x'
  target_iff : ∀ y, P.target y ↔ G.target (e y)

/-- `Refines` is the conjunction of the four obligations. -/
theorem refines_iff {G : ChildGraph X} {P : ChildGraph Y} {π : X → Y} :
    Refines G P π ↔ Complete G P π ∧ SoundEvery G P π ∧ TargetDown G P π ∧ TargetUp G P π :=
  ⟨fun h => ⟨h.complete, h.soundEvery, h.targetDown, h.targetUp⟩,
    fun ⟨hC, hS, hTd, hTu⟩ => ⟨hC, hS, hTd, hTu⟩⟩

/-- **An embedding is a refinement with the table as the actual side**:
`Embeds.sound` is `Complete`, `Embeds.complete` is `SoundEvery`, and
`Embeds.target_iff` is `TargetDown` with `TargetUp`. -/
theorem embeds_iff_refines {P : ChildGraph Y} {G : ChildGraph X} {e : Y → X} :
    Embeds P G e ↔ Refines P G e :=
  ⟨fun h => ⟨h.sound, h.complete, fun y => (h.target_iff y).1, fun y => (h.target_iff y).2⟩,
    fun h => ⟨h.complete, h.soundEvery, fun y => ⟨h.targetDown y, h.targetUp y⟩⟩⟩

theorem Embeds.refines {P : ChildGraph Y} {G : ChildGraph X} {e : Y → X} (h : Embeds P G e) :
    Refines P G e :=
  embeds_iff_refines.1 h

theorem Refines.embeds {P : ChildGraph Y} {G : ChildGraph X} {e : Y → X} (h : Refines P G e) :
    Embeds P G e :=
  embeds_iff_refines.2 h

/-- The image of an embedding is child-closed in the actual graph. -/
theorem Embeds.closed_range {P : ChildGraph Y} {G : ChildGraph X} {e : Y → X}
    (h : Embeds P G e) : G.Closed (Set.range e) := by
  rintro _ x' ⟨y, rfl⟩ hx
  obtain ⟨y', -, rfl⟩ := h.complete y hx
  exact ⟨y', rfl⟩

/-- The `Fin`-indexed `PscVerif.QuotientDistance.Refinement` is `Refines` on the
induced child graphs: a corollary of `quotientDistance_iff`. -/
theorem refinement_iff_refines {n m : ℕ} {actual : Fin n → Fin n → Prop}
    {quotient : Fin m → Fin m → Prop} {typed : Fin n → Prop} {terminal : Fin m → Prop}
    {project : Fin n → Fin m} :
    PscVerif.QuotientDistance.Refinement actual quotient typed terminal project ↔
      Refines (⟨actual, typed⟩ : ChildGraph (Fin n)) ⟨quotient, terminal⟩ project :=
  quotientDistance_iff.trans refines_iff.symm

variable {G : ChildGraph X} {P : ChildGraph Y} {π : X → Y} {x : X}

/-! ## Strict reachability and dead ends -/

/-- Strict reachability projects along a complete projection that reflects
targets. -/
theorem Complete.strictReach (hC : Complete G P π) (hT : TargetUp G P π) {x x' : X}
    (h : Relation.ReflTransGen G.StrictStep x x') :
    Relation.ReflTransGen P.StrictStep (π x) (π x') := by
  induction h with
  | refl => exact .refl
  | tail _ hbc ih => exact ih.tail ⟨fun ht => hbc.1 (hT _ ht), hC hbc.2⟩

/-- Strict reachability lifts from every source along a projection that is sound
from every source and preserves targets. -/
theorem SoundEvery.strictReach_lift (hS : SoundEvery G P π) (hT : TargetDown G P π) {y : Y}
    (h : Relation.ReflTransGen P.StrictStep (π x) y) :
    ∃ x', Relation.ReflTransGen G.StrictStep x x' ∧ π x' = y := by
  induction h with
  | refl => exact ⟨x, .refl, rfl⟩
  | tail _ hbc ih =>
    obtain ⟨b, hxb, rfl⟩ := ih
    obtain ⟨c, hbc', hc⟩ := hS b hbc.2
    exact ⟨c, hxb.tail ⟨fun ht => hbc.1 (hT _ ht), hbc'⟩, hc⟩

/-- **A dead end projects to a dead end** along a projection that is sound from
every source and reflects targets. -/
theorem deadEnd_down (hS : SoundEvery G P π) (hT : TargetUp G P π) (h : G.DeadEnd x) :
    P.DeadEnd (π x) :=
  ⟨fun ht => h.1 (hT x ht), fun y' hy => by
    obtain ⟨x', hx', -⟩ := hS x hy
    exact h.2 x' hx'⟩

/-- **A quotient dead end is a dead end at every source of its fibre**, along a
complete projection that preserves targets. -/
theorem deadEnd_up (hC : Complete G P π) (hT : TargetDown G P π) (h : P.DeadEnd (π x)) :
    G.DeadEnd x :=
  ⟨fun ht => h.1 (hT x ht), fun x' hx => h.2 (π x') (hC hx)⟩

/-! ## (A) in inductive form, and (A⁺) -/

/-- (A) pulls back along a complete projection that reflects targets
(inductive form of `Complete.inevitable`). -/
theorem Complete.inev (hC : Complete G P π) (hT : TargetUp G P π) :
    ∀ {y : Y}, P.Inev y → ∀ {x : X}, π x = y → G.Inev x := by
  intro y h
  induction h with
  | here ht => intro x hx; exact .here (hT x (hx ▸ ht))
  | step _ ih => intro x hx; exact .step fun t hxt => ih (π t) (hx ▸ hC hxt) rfl

/-- (A) pushes forward along a projection that is sound from every source and
preserves targets (inductive form; no choice). -/
theorem SoundEvery.inev (hS : SoundEvery G P π) (hT : TargetDown G P π) :
    ∀ {x : X}, G.Inev x → P.Inev (π x) := by
  intro x h
  induction h with
  | here ht => exact .here (hT _ ht)
  | step _ ih =>
    refine .step fun y hy => ?_
    obtain ⟨x', hx', rfl⟩ := hS _ hy
    exact ih x' hx'

/-- **(A⁺) pulls back** along a complete projection that is sound from every
source and reflects targets.  Completeness and reflection of targets carry (A)
back (`Complete.inev`) and carry a strict actual path (through non-targets) to a
dead end forward to a strict quotient path (`Complete.strictReach`); soundness
from every source and reflection of targets make its end a quotient dead end
(`deadEnd_down`).  Neither `Complete` nor `SoundEvery` can be dropped
(`dropped_inevMax`, `overdrawn_inevMax`). -/
theorem inevMax_of_quotient (hC : Complete G P π) (hS : SoundEvery G P π)
    (hT : TargetUp G P π) (h : P.InevMax (π x)) : G.InevMax x := by
  rw [inevMax_iff] at h ⊢
  refine ⟨hC.inev hT h.1 rfl, ?_⟩
  rintro ⟨t, hxt, hd⟩
  exact h.2 ⟨π t, hC.strictReach hT hxt, deadEnd_down hS hT hd⟩

/-- **(A⁺) pushes forward** along a complete projection that is sound from every
source and preserves targets.  Soundness from every source and preservation of
targets carry (A) forward (`SoundEvery.inev`) and lift a strict quotient path
(through non-targets) to a dead end to a strict actual path from `x`
(`SoundEvery.strictReach_lift`); completeness and preservation of targets make
its end an actual dead end (`deadEnd_up`).  Neither `Complete` nor `SoundEvery`
can be dropped (`undrawn_inevMax`, `overdrawnFork_inevMax`). -/
theorem inevMax_to_quotient (hC : Complete G P π) (hS : SoundEvery G P π)
    (hT : TargetDown G P π) (h : G.InevMax x) : P.InevMax (π x) := by
  rw [inevMax_iff] at h ⊢
  refine ⟨hS.inev hT h.1, ?_⟩
  rintro ⟨y, hxy, hd⟩
  obtain ⟨t, hxt, rfl⟩ := hS.strictReach_lift hT hxy
  exact h.2 ⟨t, hxt, deadEnd_up hC hT hd⟩

/-! ## The readings under `Refines` -/

/-- (E) is invariant under a refinement. -/
theorem Refines.productive_iff (h : Refines G P π) : G.Productive x ↔ P.Productive (π x) :=
  ⟨h.complete.productive h.targetDown, h.soundEvery.productive h.targetUp⟩

/-- (AE) is invariant under a refinement. -/
theorem Refines.hereditarilyProductive_iff (h : Refines G P π) :
    G.HereditarilyProductive x ↔ P.HereditarilyProductive (π x) :=
  Psc.GraphRefinement.hereditarilyProductive_iff h.complete h.soundEvery h.targetDown h.targetUp

/-- (A) is invariant under a refinement. -/
theorem Refines.inevitable_iff (h : Refines G P π) : G.Inevitable x ↔ P.Inevitable (π x) :=
  Psc.GraphRefinement.inevitable_iff h.complete h.soundEvery h.targetDown h.targetUp

/-- **(A⁺) is invariant** under a refinement. -/
theorem Refines.inevMax_iff (h : Refines G P π) : G.InevMax x ↔ P.InevMax (π x) :=
  ⟨inevMax_to_quotient h.complete h.soundEvery h.targetDown,
    inevMax_of_quotient h.complete h.soundEvery h.targetUp⟩

/-- (AE°) pulls back along a refinement.  It does not push forward
(`unroll_cyclicProductive`). -/
theorem Refines.cyclicProductive_of_quotient (h : Refines G P π)
    (hc : P.CyclicProductive (π x)) : G.CyclicProductive x :=
  Psc.GraphRefinement.cyclicProductive_of_quotient h.complete h.soundEvery h.targetUp hc

/-- A refinement lifts every infinite quotient path from every source. -/
theorem Refines.liftsPaths (h : Refines G P π) (x : X) : LiftsPaths G P π x :=
  h.soundEvery.liftsPaths x

/-! ## Cycles along an injective embedding -/

/-- A nonempty quotient path lifts from every source, as a nonempty actual
path. -/
theorem SoundEvery.transGen_lift (hS : SoundEvery G P π) {y : Y}
    (h : Relation.TransGen P.child (π x) y) :
    ∃ x', Relation.TransGen G.child x x' ∧ π x' = y := by
  induction h with
  | single hy =>
    obtain ⟨x', hxx', hx'⟩ := hS x hy
    exact ⟨x', .single hxx', hx'⟩
  | tail _ hbc ih =>
    obtain ⟨b, hxb, rfl⟩ := ih
    obtain ⟨c, hbc', hc⟩ := hS b hbc
    exact ⟨c, hxb.tail hbc', hc⟩

/-- **(AE°) along an injective embedding.**  A table state satisfies (AE°) iff
its image does.  `⇐` is `cyclicProductive_of_quotient` with the table as the
actual side and needs no injectivity.  `⇒`: a state `t` on an actual cycle and
reached from `e y` is `e z` for a row `z` reached from `y` (full child stars);
lifting the cycle edge by edge through the full child stars ends at a row `w`
with `e w = e z`; injectivity, used here and only here, gives `w = z`, a table
cycle at `z`; so `z` is productive, and `t = e z` is productive by soundness of
the table edges.  Without injectivity the lift can end at another row over the
same actual state (`unroll_embeds`). -/
theorem Embeds.cyclicProductive_iff {e : Y → X} (h : Embeds P G e) (hinj : Function.Injective e)
    (y : Y) : P.CyclicProductive y ↔ G.CyclicProductive (e y) := by
  have hR := h.refines
  refine ⟨fun hP t hyt hcyc => ?_,
    Psc.GraphRefinement.cyclicProductive_of_quotient hR.complete hR.soundEvery hR.targetUp⟩
  obtain ⟨z, hyz, rfl⟩ := hR.soundEvery.reach_lift hyt
  obtain ⟨w, hzw, hw⟩ := hR.soundEvery.transGen_lift hcyc
  have hzz : Relation.TransGen P.child z z := hinj hw ▸ hzw
  exact hR.complete.productive hR.targetDown (hP z hyz hzz)

/-! ## Finite path lifting -/

/-- **Finite path lifting from every source**, on arbitrary types.  If the `n`
steps of `q` read from time `k` are quotient edges, they lift, as `n` actual
edges, from every source `a` over `q k`.  Nothing is assumed of `q` after time
`k + n`, so every finite quotient path (extended in any way to `ℕ → Y`) lifts,
including one that extends to no infinite path (`step2_no_infinite_path`).  The
analogue of
`PscVerif.QuotientDistance.path_lift` without `Fin`; like `path_lift`, which
reads only the `lifts` field of a `Refinement`, it uses soundness from every
source and nothing else. -/
theorem SoundEvery.prefixLift_finite (hS : SoundEvery G P π) (q : ℕ → Y) :
    ∀ (n : ℕ) (a : X) (k : ℕ), (∀ i < n, P.child (q (k + i)) (q (k + i + 1))) →
      π a = q k → PrefixLift G π q n a k := by
  intro n
  induction n with
  | zero => intro a k _ ha; exact ⟨fun _ => a, rfl, fun i hi => absurd hi (Nat.not_lt_zero i),
      fun i hi => by obtain rfl : i = 0 := Nat.le_zero.1 hi; simpa using ha⟩
  | succ n ih =>
    intro a k hq ha
    have hstep : P.child (π a) (q (k + 1)) := ha ▸ hq 0 (Nat.succ_pos n)
    obtain ⟨b, hab, hb⟩ := hS a hstep
    obtain ⟨p, hp0, hp, hpq⟩ := ih b (k + 1) (fun i hi => by
      have := hq (i + 1) (by omega)
      rwa [show k + (i + 1) = k + 1 + i by omega] at this) hb
    refine ⟨fun i => match i with | 0 => a | i + 1 => p i, rfl, fun i hi => ?_, fun i hi => ?_⟩
    · cases i with
      | zero => simpa [hp0] using hab
      | succ i => exact hp i (by omega)
    · cases i with
      | zero => simpa using ha
      | succ i =>
        have := hpq i (by omega)
        rwa [show k + 1 + i = k + (i + 1) by omega] at this

/-- **Finite stretches of an infinite quotient path lift from every source**
(the form the brief fixes): every `n` steps of the infinite quotient path `q`,
read from time `k`, lift from every source `a` over `q k`.  The corollary of
`SoundEvery.prefixLift_finite` that reads the first `n` steps of `hq`.  Its
hypothesis `hq` is an infinite path, so it does not reach a finite quotient path
that extends to no infinite one (in `step2`, the path `false, true`, ending at a
state with no child); `SoundEvery.prefixLift_finite` does. -/
theorem SoundEvery.prefixLift (hS : SoundEvery G P π) (q : ℕ → Y) (hq : P.IsPath q) :
    ∀ (n : ℕ) (a : X) (k : ℕ), π a = q k → PrefixLift G π q n a k :=
  fun n a k ha => hS.prefixLift_finite q n a k (fun i _ => hq (k + i)) ha

/-- Soundness from every source gives finite path lifting at every state. -/
theorem SoundEvery.liftsPrefixes (hS : SoundEvery G P π) (x : X) : LiftsPrefixes G P π x :=
  fun q hq0 hq n => hS.prefixLift q hq n x 0 hq0.symm

/-- **König's lemma for one quotient path.**  If every actual state has
finitely many children and every finite prefix of `q`, read from time `k`,
lifts from `a`, then all of `q` from time `k` lifts from `a`.  (The committed
`liftsPaths_of_liftsPrefixes` is the form quantified over every quotient path
from `π a`.) -/
theorem exists_path_of_prefixLifts (hfin : ∀ a, {c | G.child a c}.Finite) {q : ℕ → Y}
    {a : X} {k : ℕ} (h : ∀ n, PrefixLift G π q n a k) :
    ∃ p : ℕ → X, p 0 = a ∧ G.IsPath p ∧ ∀ n, π (p n) = q (k + n) := by
  have next : ∀ b : {b : X × ℕ // ∀ n, PrefixLift G π q n b.1 b.2},
      ∃ c : {c : X × ℕ // ∀ n, PrefixLift G π q n c.1 c.2},
        G.child b.1.1 c.1.1 ∧ c.1.2 = b.1.2 + 1 := by
    rintro ⟨⟨b, j⟩, hb⟩
    obtain ⟨c, hbc, hc⟩ := exists_child_prefixLift (hfin b) hb
    exact ⟨⟨(c, j + 1), hc⟩, hbc, rfl⟩
  choose f hf using next
  let s : ℕ → {b : X × ℕ // ∀ n, PrefixLift G π q n b.1 b.2} :=
    fun n => f^[n] ⟨(a, k), h⟩
  have hidx : ∀ n, (s n).1.2 = k + n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      show (f^[n + 1] _).1.2 = k + (n + 1)
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

/-- **Infinite lifting from some source of a finite set of sources** (pigeonhole,
then König).  If every actual state has finitely many children, `S` is finite,
and every finite prefix of `q` lifts from some source in `S`, then `q` lifts
from some source in `S`.  Both finiteness hypotheses are needed: the pigeonhole
step uses `S` finite, the König step finitely many children.  Without finitely
many children it fails on `fan` with `S = {none}`
(`fan_finite_sources_no_lift`); without `S` finite it fails on `chains`, where
every state has at most one child (`chains_finite_sources_no_lift`).  It says
nothing when the set of candidate sources is infinite. -/
theorem exists_lift_of_finite_sources (hfin : ∀ a, {c | G.child a c}.Finite) {S : Set X}
    (hS : S.Finite) (q : ℕ → Y) (hpre : ∀ n, ∃ x ∈ S, PrefixLift G π q n x 0) :
    ∃ x ∈ S, ∃ p : ℕ → X, p 0 = x ∧ G.IsPath p ∧ ∀ n, π (p n) = q n := by
  have hall : ∃ x ∈ S, ∀ n, PrefixLift G π q n x 0 := by
    by_contra hno
    have hbad : ∀ x ∈ S, ∃ n, ¬ PrefixLift G π q n x 0 := by
      intro x hx
      by_contra hall
      exact hno ⟨x, hx, fun n => by_contra fun hn => hall ⟨n, hn⟩⟩
    classical
    let f : X → ℕ := fun x => if hx : x ∈ S then Classical.choose (hbad x hx) else 0
    obtain ⟨x, hx, hxN⟩ := hpre (hS.toFinset.sup f)
    have hle : f x ≤ hS.toFinset.sup f := Finset.le_sup (hS.mem_toFinset.2 hx)
    have hfx : ¬ PrefixLift G π q (f x) x 0 := by
      have := Classical.choose_spec (hbad x hx)
      simpa [f, hx] using this
    exact hfx (hxN.mono_le hle)
  obtain ⟨x, hx, hxl⟩ := hall
  obtain ⟨p, hp0, hp, hpq⟩ := exists_path_of_prefixLifts hfin hxl
  exact ⟨x, hx, p, hp0, hp, fun n => by simpa using hpq n⟩

/-! ## Countermodels -/

/-- `fork` and `forkDropped` have the same targets: the identity preserves and
reflects them. -/
theorem dropped_targets : TargetDown fork forkDropped id ∧ TargetUp fork forkDropped id :=
  ⟨fun _ h => h, fun _ h => h⟩

/-- **(A) does not pull back without completeness.**  The identity of `fork`
onto `forkDropped` (the edge `root → bad` removed) is sound from every source
and has the same targets (so `TargetUp` holds: `dropped_targets`); (A) holds at
the quotient root and fails at the actual root, along the path
`root, bad, bad, …`. -/
theorem dropped_inevitable :
    SoundEvery fork forkDropped id ∧ ¬ Complete fork forkDropped id ∧
      forkDropped.Inevitable .root ∧ ¬ fork.Inevitable .root := by
  refine ⟨dropped_soundEvery, dropped_not_complete, fun p hp0 hp => ⟨1, ?_⟩, fun h => ?_⟩
  · have h0 := hp 0
    rw [hp0] at h0
    exact h0
  · obtain ⟨n, hn⟩ := h (fun n => if n = 0 then .root else .bad) rfl (fun n => by
      cases n with
      | zero => exact Or.inr rfl
      | succ n => rfl)
    have hn' : (if n = 0 then Fork.root else Fork.bad) = Fork.good := hn
    split_ifs at hn'

/-- `fan` and `ray` have no targets: `fanProj` preserves and reflects them,
vacuously. -/
theorem fan_targets : TargetDown fan ray fanProj ∧ TargetUp fan ray fanProj :=
  ⟨fun _ h => h.elim, fun _ h => h.elim⟩

/-- **(A) does not push forward without infinite path lifting.**  `fan` projects
onto the ray completely (targets are empty on both sides, so `TargetDown`
holds: `fan_targets`); (A) holds at the
actual root, vacuously, because no infinite actual path leaves it
(`fan_no_lift`, which also gives finite but not infinite path lifting there),
and fails at its projection, along the ray itself. -/
theorem fan_inevitable :
    Complete fan ray fanProj ∧ fan.Inevitable none ∧ ¬ ray.Inevitable (fanProj none) := by
  refine ⟨fan_complete, fun p hp0 hp => (fan_no_lift.2.2.2.1 ⟨p, hp0, hp⟩).elim, fun h => ?_⟩
  obtain ⟨n, hn⟩ := h (fun n => n) rfl (fun _ => rfl)
  exact hn

/-- **`broken` does not separate soundness from some source from infinite path
lifting.**  Its quotient `0 → 1 → 2` has no infinite path, so `LiftsPaths` holds
vacuously at every actual state.  It separates `SoundSome` from `SoundEvery` for
(E) along a finite path only (`broken_productive`). -/
theorem broken_liftsPaths_vacuous (x : Broken) :
    LiftsPaths brokenActual brokenQuotient brokenProj x := by
  intro q _ hq
  exfalso
  have h0 := hq 0
  have h1 := hq 1
  have h2 := hq 2
  rcases h0 with ⟨_, h01⟩ | ⟨_, h01⟩ <;> rcases h1 with ⟨h10, h11⟩ | ⟨h10, h11⟩ <;>
    rcases h2 with ⟨h20, _⟩ | ⟨h20, _⟩ <;> simp_all

/-- **Soundness from some source without infinite path lifting.**  Actual
`step2` (`false → true`; `true` has no child, but it is `step2`'s target, so it
is not a `DeadEnd`); quotient the one-state `loop`.  Every edge projects and the
quotient edge is realised (by `false → true`), but not from the source `true`,
and the quotient self-loop has no lift from `false`.  The map to `loop`
reflects targets vacuously and does not preserve them (`brokenLoop_targets`);
`LiftsPaths` does not read targets. -/
theorem brokenLoop_no_lift :
    Complete step2 loop (fun _ => ()) ∧ SoundSome step2 loop (fun _ => ()) ∧
      ¬ SoundEvery step2 loop (fun _ => ()) ∧ ¬ LiftsPaths step2 loop (fun _ => ()) false := by
  refine ⟨fun _ _ _ => trivial, fun _ _ _ => ⟨false, true, rfl, rfl, rfl, rfl⟩, fun hS => ?_,
    fun hL => ?_⟩
  · obtain ⟨b, ⟨h, -⟩, -⟩ := hS true (show loop.child () () from trivial)
    exact Bool.noConfusion h
  · obtain ⟨p, hp0, hp, -⟩ := hL (fun _ => ()) rfl (fun _ => trivial)
    have h0 := hp 0
    have h1 := hp 1
    rw [hp0] at h0
    obtain ⟨-, h0'⟩ := h0
    obtain ⟨h1', -⟩ := h1
    rw [h0'] at h1'
    exact Bool.noConfusion h1'

/-- The targets of `brokenLoop`: the map of `step2` onto `loop` reflects targets
(vacuously: `loop` has none) and does not preserve them (`true` is `step2`'s
target), and `true`, which has no child, is not a `DeadEnd` of `step2`. -/
theorem brokenLoop_targets :
    TargetUp step2 loop (fun _ => ()) ∧ ¬ TargetDown step2 loop (fun _ => ()) ∧
      ¬ step2.DeadEnd true :=
  ⟨fun _ h => h.elim, fun h => h true rfl, fun h => h.1 rfl⟩

/-- **(A⁺) does not pull back without completeness.**  `dropped` again: sound
from every source, targets reflected, not complete; (A⁺) holds at the quotient
root and fails at the actual root. -/
theorem dropped_inevMax :
    SoundEvery fork forkDropped id ∧ TargetUp fork forkDropped id ∧
      ¬ Complete fork forkDropped id ∧ forkDropped.InevMax .root ∧ ¬ fork.InevMax .root := by
  refine ⟨dropped_soundEvery, dropped_targets.2, dropped_not_complete,
    .step ⟨.good, rfl⟩ fun t ht => ?_, fun h => dropped_inevitable.2.2.2 h.inev.inevitable⟩
  obtain rfl : t = .good := ht
  exact .here rfl

/-- **(A⁺) does not pull back without soundness from every source.**  The dead
end `stub` projects onto the state `false` of `step2`: completely (vacuously),
with targets preserved and reflected, and not soundly.  (A⁺) holds at the
quotient state and fails at the actual dead end, where (A) holds vacuously
(`stub_inevitable_not_productive`). -/
theorem overdrawn_inevMax :
    Complete stub step2 (fun _ => false) ∧ TargetDown stub step2 (fun _ => false) ∧
      TargetUp stub step2 (fun _ => false) ∧ ¬ SoundEvery stub step2 (fun _ => false) ∧
      step2.InevMax false ∧ ¬ stub.InevMax () := by
  refine ⟨fun _ _ h => h.elim, fun _ h => h.elim,
    fun _ (h : false = true) => Bool.false_ne_true h, fun hS => ?_,
    .step ⟨true, rfl, rfl⟩ fun t ht => ?_, stub_inevitable_not_productive.2.2.1⟩
  · obtain ⟨_, h, -⟩ := hS () (show step2.child false true from ⟨rfl, rfl⟩)
    exact h
  · obtain ⟨-, rfl⟩ := ht
    exact .here rfl

/-- **(A⁺) does not push forward without completeness.**  `undrawn` again: the
identity of `step2` onto `noEdge` is sound from every source (vacuously), with
targets preserved and reflected, and not complete; (A⁺) holds at the actual
state and fails at its projection, which is a dead end. -/
theorem undrawn_inevMax :
    SoundEvery step2 noEdge id ∧ TargetDown step2 noEdge id ∧ TargetUp step2 noEdge id ∧
      ¬ Complete step2 noEdge id ∧ step2.InevMax false ∧ ¬ noEdge.InevMax false := by
  obtain ⟨hS, hTd, hTu, hC, -, -⟩ := undrawn_hereditarilyProductive
  refine ⟨hS, hTd, hTu, hC, overdrawn_inevMax.2.2.2.2.1, fun h => ?_⟩
  cases h with
  | here ht => exact Bool.false_ne_true ht
  | step hch _ => exact hch.elim fun _ h => h

/-- **(A⁺) does not push forward without soundness from every source.**
`overdrawnFork` again: `step2` maps into `fork` completely, with targets
preserved and reflected, and not soundly (the quotient has the extra edge
`root → bad`); (A⁺) holds at the actual state and fails at its projection. -/
theorem overdrawnFork_inevMax :
    Complete step2 fork forkProj ∧ TargetDown step2 fork forkProj ∧
      TargetUp step2 fork forkProj ∧ ¬ SoundEvery step2 fork forkProj ∧
      step2.InevMax false ∧ ¬ fork.InevMax (forkProj false) := by
  obtain ⟨hC, hTd, hTu, hS, -, -⟩ := overdrawnFork_hereditarilyProductive
  exact ⟨hC, hTd, hTu, hS, overdrawn_inevMax.2.2.2.2.1,
    fun h => dropped_inevitable.2.2.2 h.inev.inevitable⟩

/-- **Injectivity cannot be dropped from `Embeds.cyclicProductive_iff`.**  The
ray embeds into the one-state `loop` (every ray edge is the loop edge, the loop
edge out of the image of `n` is represented by `n → n + 1`, no targets on either
side), the map is not injective, (AE°) holds at the table state `0` (vacuously:
the ray has no cycle) and fails at its image. -/
theorem unroll_embeds :
    Embeds ray loop (fun _ => ()) ∧ ¬ Function.Injective (fun _ : ℕ => ()) ∧
      ray.CyclicProductive 0 ∧ ¬ loop.CyclicProductive () :=
  ⟨embeds_iff_refines.2 ⟨unroll_complete, unroll_soundEvery, fun _ h => h, fun _ h => h⟩,
    fun h => Nat.zero_ne_one (@h 0 1 rfl), unroll_cyclicProductive.1, unroll_cyclicProductive.2⟩

/-- **A finite quotient path need not extend to an infinite one.**  `false → true`
is a path of `step2`, and `step2` has no infinite path at all.  So the
hypothesis `hq` of `SoundEvery.prefixLift` excludes this finite path, and
`SoundEvery.prefixLift_finite` covers it. -/
theorem step2_no_infinite_path :
    step2.child false true ∧ ¬ ∃ q : ℕ → Bool, step2.IsPath q := by
  refine ⟨⟨rfl, rfl⟩, ?_⟩
  rintro ⟨q, hq⟩
  have h1 := (hq 0).2
  have h2 := (hq 1).1
  rw [h1] at h2
  exact Bool.noConfusion h2

/-- **Finite branching cannot be dropped from `exists_lift_of_finite_sources`.**
On `fan` with the one source `none`: the root has infinitely many children
(`fan_root_infinite`), `{none}` is finite, every prefix of the ray path
`0, 1, 2, …` lifts from `none` (`fan_liftsPrefixes`), and the whole path lifts
from no source in `{none}` (`fan_no_lift`). -/
theorem fan_finite_sources_no_lift :
    ¬ {c | fan.child none c}.Finite ∧ ({none} : Set (Option (ℕ × ℕ))).Finite ∧
      (∀ n, ∃ x ∈ ({none} : Set (Option (ℕ × ℕ))), PrefixLift fan fanProj (fun n => n) n x 0) ∧
      ¬ ∃ x ∈ ({none} : Set (Option (ℕ × ℕ))), ∃ p : ℕ → Option (ℕ × ℕ),
        p 0 = x ∧ fan.IsPath p ∧ ∀ n, fanProj (p n) = n := by
  refine ⟨fan_root_infinite, Set.finite_singleton _,
    fun n => ⟨none, rfl, fan_liftsPrefixes (fun n => n) rfl (fun _ => rfl) n⟩, ?_⟩
  rintro ⟨x, rfl, p, hp0, hp, -⟩
  exact fan_no_lift.2.2.2.1 ⟨p, hp0, hp⟩

/-- **`chains`**: one chain `(n, 0) → (n, 1) → ⋯ → (n, n)` for every `n`, and no
target.  Every state has at most one child. -/
def chains : ChildGraph (ℕ × ℕ) where
  child a b := a.2 < a.1 ∧ b = (a.1, a.2 + 1)
  target _ := False

/-- **A finite set of sources cannot be dropped from
`exists_lift_of_finite_sources`.**  `chains`, projected onto the ray by the
second coordinate: every state has finitely many (at most one) children, the
projection is complete, the set `{x | x.2 = 0}` of chain starts is infinite,
every prefix of the ray path `0, 1, 2, …` lifts from some chain start (the start
of the chain of that length), and the whole path lifts from no chain start,
because every chain is finite. -/
theorem chains_finite_sources_no_lift :
    (∀ a, {c | chains.child a c}.Finite) ∧ Complete chains ray Prod.snd ∧
      ¬ {x : ℕ × ℕ | x.2 = 0}.Finite ∧
      (∀ n, ∃ x ∈ {x : ℕ × ℕ | x.2 = 0}, PrefixLift chains Prod.snd (fun n => n) n x 0) ∧
      ¬ ∃ x ∈ {x : ℕ × ℕ | x.2 = 0}, ∃ p : ℕ → ℕ × ℕ,
        p 0 = x ∧ chains.IsPath p ∧ ∀ n, Prod.snd (p n) = n := by
  refine ⟨fun a => (Set.finite_singleton (a.1, a.2 + 1)).subset fun _ h => h.2, ?_,
    Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n, 0))
      (fun i j hij => by simpa using hij) (fun _ => rfl),
    fun n => ⟨(n, 0), rfl, fun i => (n, i), rfl, fun i hi => ⟨hi, rfl⟩, fun i _ => by simp⟩, ?_⟩
  · rintro a _ ⟨-, rfl⟩
    rfl
  · rintro ⟨x, -, p, -, hp, -⟩
    have key : ∀ i, (p i).1 = (p 0).1 ∧ (p i).2 = (p 0).2 + i := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        obtain ⟨-, h⟩ := hp i
        rw [h]
        exact ⟨ih.1, by simp [ih.2]; omega⟩
    obtain ⟨hlt, -⟩ := hp (p 0).1
    have := key (p 0).1
    omega

end Psc.GraphRefinement

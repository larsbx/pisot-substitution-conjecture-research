import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Finite signed tile-chain certificates

The forward edges are `00`, `01`, `11`, `12`, `20`, numbered `0` through `4`.
Edges `5` through `9` are their reversals.  A forward edge leaving `a` has
output `e_a`; its reverse has the negative output.  The control graph has
three labels, while the accumulated output lies in the infinite group `Z^3`.

This file constructs a literal finite edge word for every integer displacement
and terminal label.  It proves replay semantics by finite induction.  It does
not assert that an accepted word is a legal substitution word or supply any
realization, topology, zero-fibre forcing, or spectral conclusion.
-/

set_option autoImplicit false

namespace Psc.C4FiniteTileAutomaton

abbrev Label := Fin 3
abbrev Edge := Fin 10
abbrev Vector := Label → ℤ

def basis (a : Label) : Vector := fun i => if i = a then 1 else 0

def source (e : Edge) : Label :=
  match e.val with
  | 0 => 0 | 1 => 0 | 2 => 1 | 3 => 1 | 4 => 2
  | 5 => 0 | 6 => 1 | 7 => 1 | 8 => 2 | _ => 0

def target (e : Edge) : Label :=
  match e.val with
  | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 2 | 4 => 0
  | 5 => 0 | 6 => 0 | 7 => 1 | 8 => 1 | _ => 2

def edgeOutput (e : Edge) : Vector :=
  if e.val < 5 then basis (source e) else -basis (target e)

def inverse (e : Edge) : Edge :=
  if h : e.val < 5 then ⟨e.val + 5, by omega⟩ else ⟨e.val - 5, by omega⟩

@[simp] theorem inverse_source (e : Edge) : source (inverse e) = target e := by
  fin_cases e <;> rfl

@[simp] theorem inverse_target (e : Edge) : target (inverse e) = source e := by
  fin_cases e <;> rfl

@[simp] theorem inverse_inverse (e : Edge) : inverse (inverse e) = e := by
  fin_cases e <;> rfl

@[simp] theorem inverse_output (e : Edge) : edgeOutput (inverse e) = -edgeOutput e := by
  fin_cases e <;> simp [inverse, edgeOutput, source, target]

/-- Native DFA state order: label `1`, label `0`, label `2`, rejecting sink. -/
def controlCode (a : Label) : Fin 4 :=
  match a.val with | 0 => 1 | 1 => 0 | _ => 2

def controlLabel (s : Fin 4) : Option Label :=
  match s.val with | 0 => some 1 | 1 => some 0 | 2 => some 2 | _ => none

def controlStep (s : Fin 4) (e : Edge) : Fin 4 :=
  match controlLabel s with
  | none => 3
  | some a => if a = source e then controlCode (target e) else 3

@[simp] theorem controlLabel_code (a : Label) : controlLabel (controlCode a) = some a := by
  fin_cases a <;> rfl

@[simp] theorem controlStep_code (a : Label) (e : Edge) :
    controlStep (controlCode a) e =
      if a = source e then controlCode (target e) else 3 := by
  simp [controlStep]

@[simp] theorem controlStep_reject (e : Edge) : controlStep 3 e = 3 := rfl

/-- Row-major table matched against the actual vendored-DFA construction. -/
def controlTable : List ℕ :=
  (List.ofFn fun s : Fin 4 => List.ofFn fun e : Edge => (controlStep s e).val).flatten

theorem control_table_exact : controlTable = [
    3, 3, 0, 2, 3, 3, 1, 0, 3, 3,
    1, 0, 3, 3, 3, 1, 3, 3, 3, 2,
    3, 3, 3, 3, 1, 3, 3, 3, 0, 3,
    3, 3, 3, 3, 3, 3, 3, 3, 3, 3] := by decide

/-- Row-major exact output table: ten edges, three integer coordinates. -/
def outputTable : List ℤ :=
  (List.ofFn fun e : Edge => List.ofFn fun a : Label => edgeOutput e a).flatten

theorem output_table_exact : outputTable = [
    1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 1,
    -1, 0, 0, -1, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, -1] := by decide

def controlRun (s : Fin 4) : List Edge → Fin 4
  | [] => s
  | e :: es => controlRun (controlStep s e) es

/-- Exact replay. An edge whose source is not the current label is rejected. -/
def replay (a : Label) : List Edge → Option (Label × Vector)
  | [] => some (a, 0)
  | e :: es =>
    if a = source e then
      match replay (target e) es with
      | none => none
      | some (b, v) => some (b, edgeOutput e + v)
    else none

/-- A finite, composable path with its complete edge word and exact output. -/
inductive Walk : Label → List Edge → Label → Vector → Prop
  | nil (a : Label) : Walk a [] a 0
  | cons (e : Edge) {es : List Edge} {b : Label} {v : Vector}
      (rest : Walk (target e) es b v) :
      Walk (source e) (e :: es) b (edgeOutput e + v)

theorem Walk.replay_eq {a b : Label} {w : List Edge} {v : Vector}
    (h : Walk a w b v) : replay a w = some (b, v) := by
  induction h with
  | nil => rfl
  | cons e rest ih => simp [replay, ih]

theorem Walk.control {a b : Label} {w : List Edge} {v : Vector}
    (h : Walk a w b v) : controlRun (controlCode a) w = controlCode b := by
  induction h with
  | nil => rfl
  | cons e rest ih => simpa [controlRun] using ih

theorem replay_walk {a b : Label} {w : List Edge} {v : Vector}
    (h : replay a w = some (b, v)) : Walk a w b v := by
  induction w generalizing a v with
  | nil =>
      simp only [replay, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact Walk.nil _
  | cons e es ih =>
      by_cases ha : a = source e
      · subst a
        cases hr : replay (target e) es with
        | none => simp [replay, hr] at h
        | some result =>
            rcases result with ⟨c, z⟩
            simp [replay, hr] at h
            rcases h with ⟨rfl, rfl⟩
            exact Walk.cons e (ih hr)
      · simp [replay, ha] at h

theorem replay_iff_walk (a b : Label) (w : List Edge) (v : Vector) :
    replay a w = some (b, v) ↔ Walk a w b v :=
  ⟨replay_walk, Walk.replay_eq⟩

theorem Walk.append {a b c : Label} {u w : List Edge} {v z : Vector}
    (hu : Walk a u b v) (hw : Walk b w c z) : Walk a (u ++ w) c (v + z) := by
  induction hu with
  | nil => simpa using hw
  | cons e rest ih => simpa [add_assoc] using Walk.cons e (ih hw)

theorem single_edge (e : Edge) : Walk (source e) [e] (target e) (edgeOutput e) := by
  simpa using Walk.cons e (Walk.nil (target e))

def reverseWord (w : List Edge) : List Edge := w.reverse.map inverse

theorem Walk.reverse {a b : Label} {w : List Edge} {v : Vector}
    (h : Walk a w b v) : Walk b (reverseWord w) a (-v) := by
  induction h with
  | nil => simpa [reverseWord] using Walk.nil _
  | cons e rest ih =>
      have he : Walk (target e) [inverse e] (source e) (-edgeOutput e) := by
        simpa using single_edge (inverse e)
      have hx := ih.append he
      simpa [reverseWord, List.reverse_cons, List.map_append, neg_add, add_comm] using hx

/-- Concatenation repeated a specified finite number of times. -/
def repeatWord (w : List Edge) : ℕ → List Edge
  | 0 => []
  | n + 1 => w ++ repeatWord w n

theorem Walk.repeat {a : Label} {w : List Edge} {v : Vector}
    (h : Walk a w a v) (n : ℕ) : Walk a (repeatWord w n) a (n • v) := by
  induction n with
  | zero => simpa [repeatWord] using Walk.nil a
  | succ n ih => simpa only [repeatWord, succ_nsmul, add_comm] using h.append ih

/-- Negative coefficients reverse the repeated loop; no search is used. -/
def signedRepeat (w : List Edge) : ℤ → List Edge
  | .ofNat n => repeatWord w n
  | .negSucc n => reverseWord (repeatWord w (n + 1))

theorem Walk.signed_repeat {a : Label} {w : List Edge} {v : Vector}
    (h : Walk a w a v) (z : ℤ) : Walk a (signedRepeat w z) a (z • v) := by
  cases z with
  | ofNat n => simpa only [signedRepeat, Int.ofNat_eq_natCast, natCast_zsmul] using h.repeat n
  | negSucc n => simpa only [signedRepeat, negSucc_zsmul] using (h.repeat (n+1)).reverse

def loop0 : List Edge := [6, 0, 1]
def loop1 : List Edge := [2]
def loop2 : List Edge := [3, 4, 1]

theorem loop0_walk : Walk 1 loop0 1 (basis 0) := by
  apply replay_walk
  simp [loop0, replay, source, target, edgeOutput]

theorem loop1_walk : Walk 1 loop1 1 (basis 1) := by
  apply replay_walk
  simp [loop1, replay, source, target, edgeOutput]

theorem loop2_walk : Walk 1 loop2 1 (basis 0 + basis 1 + basis 2) := by
  apply replay_walk
  simp [loop2, replay, source, target, edgeOutput, add_comm, add_left_comm]

/-- The integer coefficients of the three concrete anchor loops. -/
def anchorWord (v : Vector) : List Edge :=
  signedRepeat loop0 (v 0 - v 2) ++
    signedRepeat loop1 (v 1 - v 2) ++ signedRepeat loop2 (v 2)

theorem loop_decomposition (v : Vector) :
    (v 0 - v 2) • basis 0 + (v 1 - v 2) • basis 1 +
      v 2 • (basis 0 + basis 1 + basis 2) = v := by
  funext i
  fin_cases i <;> simp [basis]

/-- A literal finite loop at label `1` realizes every integer displacement. -/
theorem anchorWord_walk (v : Vector) : Walk 1 (anchorWord v) 1 v := by
  have h := ((loop0_walk.signed_repeat (v 0 - v 2)).append
    (loop1_walk.signed_repeat (v 1 - v 2))).append (loop2_walk.signed_repeat (v 2))
  simpa only [anchorWord, loop_decomposition] using h

/-- Fixed zero-output terminal paths: `loop0; inverse(01)`, empty, `inverse(11);12`. -/
def terminalWord (b : Label) : List Edge :=
  match b.val with
  | 0 => loop0 ++ [6]
  | 1 => []
  | _ => [7, 3]

theorem terminalWord_walk (b : Label) : Walk 1 (terminalWord b) b 0 := by
  apply replay_walk
  fin_cases b <;> simp [terminalWord, loop0, replay, source, target, edgeOutput]

/-- Explicit certificate, finite for each input even though the input group is infinite. -/
def certificate (v : Vector) (b : Label) : List Edge := anchorWord v ++ terminalWord b

/-- Every target label and integer displacement has an explicit finite signed walk. -/
theorem certificate_walk (v : Vector) (b : Label) : Walk 1 (certificate v b) b v := by
  simpa [certificate] using (anchorWord_walk v).append (terminalWord_walk b)

/-- End-to-end certificate correctness for the executable replay semantics. -/
theorem certificate_replay (v : Vector) (b : Label) :
    replay 1 (certificate v b) = some (b, v) := (certificate_walk v b).replay_eq

/-- The output-bearing certificate follows the finite table's control transitions. -/
theorem certificate_control (v : Vector) (b : Label) :
    controlRun 0 (certificate v b) = controlCode b := (certificate_walk v b).control

theorem exists_signed_walk (v : Vector) (b : Label) :
    ∃ w : List Edge, replay 1 w = some (b, v) := ⟨certificate v b, certificate_replay v b⟩

/-- A discontinuous edge word fails replay. -/
theorem disconnected_rejected : replay 1 [0] = none := by
  simp [replay, source]

/-- Reversing `11` outputs `-e₁`, so the positive-output forgery is rejected. -/
theorem reversed_sign_rejected : replay 1 [7] ≠ some (1, basis 1) := by
  intro h
  have hv : -basis 1 = basis 1 := by
    simpa [replay, source, target, edgeOutput] using h
  have hi := congrFun hv 1
  norm_num [basis] at hi

/-- Removing `00` and its inverse preserves control connectivity but loses output rank. -/
def ReducedEdge (e : Edge) : Prop := e ≠ 0 ∧ e ≠ 5

def reducedPotential (a : Label) : ℤ := if a = 0 then -1 else 0

theorem reduced_edge_coboundary (e : Edge) (h : ReducedEdge e) :
    edgeOutput e 0 - edgeOutput e 2 =
      reducedPotential (target e) - reducedPotential (source e) := by
  fin_cases e <;> norm_num [ReducedEdge, edgeOutput, basis, source, target, reducedPotential] at *

/-- Exact telescoping on arbitrary finite walks of the weakened graph. -/
theorem Walk.reduced_coboundary {a b : Label} {w : List Edge} {v : Vector}
    (h : Walk a w b v) (hr : ∀ e ∈ w, ReducedEdge e) :
    v 0 - v 2 = reducedPotential b - reducedPotential a := by
  induction h with
  | nil => simp
  | cons e rest ih =>
      have he := reduced_edge_coboundary e (hr e (by simp))
      have ht := ih (by
        intro f hf
        exact hr f (by simp [hf]))
      simp only [Pi.add_apply]
      omega

theorem reduced_based_loop_constraint {w : List Edge} {v : Vector}
    (h : Walk 1 w 1 v) (hr : ∀ e ∈ w, ReducedEdge e) : v 0 = v 2 := by
  have hv := h.reduced_coboundary hr
  simp only [sub_self] at hv
  exact sub_eq_zero.mp hv

/-- A connected control graph alone does not imply every integer output is reachable. -/
theorem reduced_basis0_impossible :
    ¬ ∃ w : List Edge, Walk 1 w 1 (basis 0) ∧ (∀ e ∈ w, ReducedEdge e) := by
  rintro ⟨w, h, hr⟩
  have hv := reduced_based_loop_constraint h hr
  norm_num [basis] at hv

end Psc.C4FiniteTileAutomaton

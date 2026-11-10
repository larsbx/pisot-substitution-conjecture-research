/-
# The packet certificate (v1 record)

Layer D of the packet square (roadmap immediate-sequence item 2;
`docs/packet-square-stop-go-2026-11-10.md`): an exported packet table is a `Table α`, a
`Bool` checker `Table.check` re-derives every exported field from `Psc.Reduction.red` and the
definitions of `Psc.OccurrenceGraph`, and an accepted table is read as a set of literal
occurrence pairs `Occ` (`Table.decode`, `Table.occAt`).  The checker is a conjunction of
eleven clauses, evaluated by one `decide +kernel` per table: ten structural clauses and
`seedsOK` (every normalised swap seed is a listed state); `Table.check_iff` unpacks it into the
structure `Table.Accepted`.  On
an accepted table (`t.check = true`):

* `Table.check_sound` (`[Fintype α] [LinearOrder α]`): every row decodes, to `occAt`; `occAt`
  is injective; every decoded pair is `Occ.Valid`; the decoded star of every row is the literal
  star `occStar` (one list equation, children and splits, in order); both addresses, both
  letters, the residual, the `interior` and `success` bits are their literal values; every row
  is reachable in `t.graph` from a root row;
* `Table.iso` (`[Fintype α] [LinearOrder α]`): `occAt` is an isomorphism of `t.graph` onto the
  induced subgraph of `occGraph t.s` on the child-closed set `Set.range t.occAt`, with the
  coincidence target (`t.graph`) and the packet-success target (`t.graphSuccess`);
* `Table.range_eq_reach` (no order hypothesis, no injectivity): `Set.range t.occAt` is exactly
  the set of literal occurrence pairs reachable in `occGraph t.s` from the root pairs
  `⟨T, P, Q, none⟩` of the noncoincident listed states;
* `Table.roots`, `Table.hubs_sound`, `Table.hubs_rows`, `Table.closed_range`, `Table.seed_mem`
  (no order hypothesis); `Table.seeds_listed` and `Table.bpaStatesNC_listed` (linear order):
  every seed of `Psc.Descendants.seeds`, and every vertex of `bpaStatesNC t.s`, is a listed
  state or the swap of one;
* `Table.graph_sound`, `Table.graph_complete`, `Table.targets` (no order hypothesis): the three
  fields of `Psc.GraphRefinement.Embeds t.graph (occGraph t.s) t.occAt` (declared in the module
  `PscVerif.GraphEmbedding`; and of the success variant), stated without importing that
  module; the bundle `Table.embeds` belongs to the composite layer.

Every headline theorem takes the table explicitly, `(t : Table α) (h : t.check = true)`; the
`Table.Accepted.*` lemmas take `h : t.Accepted` and leave `t`
implicit.

**Which word points which way**.  Here the table is the source side: "every
listed edge is a literal edge" (`graph_sound`) is `Complete t.graph (occGraph t.s) t.occAt`,
and "full child stars" (`graph_complete`) is `SoundEvery t.graph (occGraph t.s) t.occAt`.

**Order hypothesis**.  The clauses are stated with `[LT α] [DecidableLT α]`;
injectivity of `occAt` needs `[LinearOrder α]`.  With an arbitrary `<`, `isNormal` may accept
both orientations of a noncoincident state, two rows with distinct keys then decode to one
occurrence pair, and injectivity is false: `weird` (at the end
of this module) is Fibonacci over the two-letter type `EmptyOrderLetter` whose `<` is empty,
with 19 rows; it is accepted (`weird_accepted`), its rows 9 and 18 have distinct key codes
and decode to one occurrence pair (`weird_rows_collide`), and `occAt` is not injective
(`weird_not_injective`).  The same rows over `Fin 2` with its order are refused
(`weirdFin_refused`).  Under a linear order an irreducible noncoincident block has distinct
first letters (`heads_ne`), so exactly one orientation is normalised (`not_isNormal_both`); a
factor row is the only row of its `(parent, ordinal)` (`factor_rows`, `ordinals`); hence
decoding is injective on keys (`decode_inj`), and distinct rows have distinct key codes
(`keyCode_inj`, from `keysOK`).  A `Fin 3` data module elaborated with the default instances
is covered (`fin3_occAt_injective`).

## The record (`packet-square-v1`, Lean emission)

The Mojo exporter (`kernel/psc/packet_square_export.mojo`, `packet_square_lean`) prints one
`def table : Table (Fin 3) where …` and one `theorem accepted : table.check = true := by
decide +kernel`.  Fields, in this order:

* `letters : List α`: the residual coordinate order (`lettersOK`: every letter once).
* `s : α → List α`: the substitution (`![σ 0, σ 1, σ 2]`).
* `target : Option α`: `none` (any diagonal) or `some c` (the diagonal `c/c`).
* `states : List (List α × List α)`: the states, each an irreducible block in normalised
  orientation (`isNormal`, Mojo `normalise` on equal-length pairs), without repetition
  (`statesOK`); every
  normalised seed `([a, b], [b, a])`, `a < b`, of `letters` listed (`seedsOK`).
* `factors : List FactorRow`, `⟨parent, ordinal, child, sign, start, stop, total⟩`: for each
  noncoincident state `i`, the rows with `parent = i`, in list order, are the blocks
  `k = 0, 1, …` of `red (σ T.1) (σ T.2)`: `child` the index of the block's normalised
  orientation, `sign = isNormal` of the raw block, `ordinal = k`, `start`/`stop` the block's
  `blockStart` bounds, `total = |σ T.1|`; no row under a coincidence state (`factorsOK`).
* `packets : List (PacketRow α)`, `⟨state, sign, top, bot, factor, topAddr, botAddr, letters,
  residual, interior, success, birth⟩`.  A root row has `factor = none`, `sign = true`,
  `topAddr = botAddr = none`, `birth = none`, and reads `⟨T, top, bot, none⟩`; the root rows,
  in list order, are `(i, true, P, Q)` for the noncoincident states `i` in order and `P, Q`
  row-major (`rootsOK`).  A non-root row has `factor = some f` with `factors[f].child = state`
  and reads `⟨orient T sign, top, bot, some ⟨orient P (sign == factors[f].sign),
  factors[f].ordinal⟩⟩` (`P = states[factors[f].parent]`); with `P'` that oriented parent
  and `g = blockStart (red (σ P'.1) (σ P'.2)) ordinal + top`, `topAddr = some ((cutAddr s P'.1
  g).1, (cutAddr s P'.1 g).2, g, top)` (`Occ.topAddr`), and `botAddr` likewise with `P'.2`
  and `bot`; `letters`, `residual` (over `letters`), `interior`, `success` are the literal
  values (`packetOK`); `birth = some (j, d, e)` with `j < i` and `.child d e i` in the star
  of `j` (`birthOK`): some incoming edge from an earlier row, not necessarily the first (the
  Mojo exporter emits the first; `fibExtra_birth_not_first` is accepted with another one).
* `stars : List (List StarRow)`: one per row (`stars.length = packets.length`), the full digit
  star row-major in `(d, e)`, `.child d e dst` or `.split d e kTop kBot`, the list `occStar`
  of the decoded row (`starOK`; in particular empty at a coincidence row).
* `keyOrder : List ℕ`: the row indices sorted by `Table.keyCode` (strictly increasing,
  `keysOK`), `keyCode = ((((state·2 + [sign])·B + top)·B + bot)·F + (0 | f + 1))`,
  `B = 1 + max |T.1|`, `F = 1 + |factors|`.
* `hubs : List HubRow`, `⟨state, hub, bits⟩` (may be empty): at most one row per
  `(state, hub)`; `state` indexes a noncoincident listed state and `hub` a listed letter; `bits`
  is `factorHub` over the factor rows of `state`, slot by slot, `none` exactly where Mojo's
  `factor_hub_residual` returns `-1` (`hubsOK`).

The data modules are emitted by `cd kernel && pixi run --locked mojo run -I .
packet_square_export.mojo --sigma KEY --target any --format lean --module
PscVerif.PacketSquareData.NAME --hub-rows`, and `kernel/check_packet_square.sh` regenerates them
and compares bytes.  The planned modules `PscVerif.PacketSquareData.{Tribonacci, RealSecondary,
NonPisot, GfActual}` (keys `01/02/0`, `1/02/202`, `1/012/1`, `1/2/021`) are not part of this
module; each carries its own receipt, a theorem `accepted : table.check = true`.

## Calibration in this module

`fibTable`: Fibonacci `0 ↦ 01, 1 ↦ 0` (`fibSubst`; binary, so outside the three-letter census
corpus), 2 states, 2 factor rows, 14 rows, accepted (`fib_accepted`); packet 2 decodes to the
literal dead end `fibDead` (`fib_rows`).  The mutation controls state the full clause vector
of the mutated table (`Table.clauses`, `Table.check_eq_clauses`), so the refusing layer is
part of each statement: dropped split, dropped child, wrong split account, out-of-range
destination, truncation (stars); side swap (keys, rows, stars); wrong residual, interior bit,
global position (rows); wrong block end (factors); wrong ordinal (factors, rows, stars);
duplicated row that no star names (keys, births); coerced and missing hub bits, a hub row
for an out-of-range state, for a coincidence state, and a repeated hub row (hubs); the empty
table (seeds only: `seedsOK` is not implied by the other clauses).  `fibDuplicate` copies
row 4 as row 14, born from row 10: it is refused by the key clause alone
(`fib_duplicate_isolated`), and its `occAt` is not injective
(`fib_duplicate_not_injective`), so `keysOK` is the only clause that refuses it.

`fibExtra` lists the extra irreducible block `(001, 100)`, which is not a vertex of
`bpaStatesNC fibSubst`, and is accepted (`fibExtra_accepted`, `fibExtra_state_unreached`):
`Table.bpaStatesNC_listed` is one inclusion only.  `fibExtraForged b` adds one row whose
decoded pair is valid and whose fields and star are literal, born through the mirrored
orientation `(100, 001)` of the extra state; that pair lies outside `Set.range fibExtra.occAt`,
hence is not reachable in `occGraph fibSubst` from the root pair of any noncoincident listed
state (`fibExtra_forged_outside`, `fibExtra_forged_not_reached`).  The row is refused by the
birth clause alone, with no birth, a birth whose edge is not in the source star, and a birth
from a later index (`fibExtra_forged_unreachable`).  A birth that is a later incoming edge
than the first is accepted (`fibExtra_birth_not_first`).

Not proved here: that the listed states are reachable from the seeds (the converse of
`Table.bpaStatesNC_listed`; `fibExtra` shows the checker does not imply it, and the clause
that the listed states are exactly the normalised `bpaStatesNC` is not checked); anything about
states that are not
listed, or about literal occurrence pairs outside `Set.range t.occAt` (descendants of a split
or of a coincidence, frames other than the normalised root frame); any statement about
absolute occurrences in the iterates `σⁿ(T₀)`, about `Psc.GraphRefinement.Embeds` or
`Refines` as bundles, or about the composite square (`Table.embeds`, `packet_square`, the
covered universe), which belong to other modules; that any particular exported table is
accepted (each data module decides that for its own table) or that the Mojo exporter is
correct; that a birth is the first incoming edge; that every noncoincident state or every
letter has a hub row; that the hub bits mean more than equality with `factorHub`; any
productive, inevitable or realised reading of any packet; anything about the PIP status, which
the checker does not read.  Nothing here advances C4, G1, #84, #138, #139 or the Pisot substitution
conjecture.
-/
import PscVerif.OccurrenceGraph

namespace Psc.PacketCertificate

open Psc.Binomial Psc.Reduction Psc.Descendants Psc.Incidence
open Psc.QuantifierInterface Psc.QuantifierBinding Psc.OccurrenceGraph Psc.OccurrenceAddress

variable {α : Type} [DecidableEq α]

/-! ### The v1 record -/

/-- One factor row = one block of the literal ordered factorisation of a normalised state. -/
structure FactorRow where
  parent : ℕ
  ordinal : ℕ
  child : ℕ
  /-- `true`: the raw block is the normalised state `child` (always `true` at a coincidence). -/
  sign : Bool
  start : ℕ
  stop : ℕ
  total : ℕ
  deriving DecidableEq, Repr

/-- One packet row: key `(state, sign, top, bot, factor)` and carried fields. -/
structure PacketRow (α : Type) where
  state : ℕ
  sign : Bool
  top : ℕ
  bot : ℕ
  factor : Option ℕ
  topAddr : Option (ℕ × ℕ × ℕ × ℕ)
  botAddr : Option (ℕ × ℕ × ℕ × ℕ)
  letters : α × α
  residual : List ℤ
  interior : Bool
  success : Bool
  /-- `(source, top digit, bottom digit)` of an incoming edge from an earlier row (`birthOK`;
  the Mojo exporter emits the first, the checker accepts any); `none` at a root. -/
  birth : Option (ℕ × ℕ × ℕ)
  deriving DecidableEq, Repr

/-- One entry of a packet's full digit star, row-major in `(d, e)`. -/
inductive StarRow where
  | child (d e dst : ℕ)
  | split (d e kTop kBot : ℕ)
  deriving DecidableEq, Repr

/-- Optional ordered hub row of a state: one entry per factor row, `none` = undefined. -/
structure HubRow where
  state : ℕ
  hub : ℕ
  bits : List (Option Bool)
  deriving DecidableEq, Repr

/-- An exported packet table (schema `packet-square-v1`). -/
structure Table (α : Type) where
  letters : List α
  s : α → List α
  target : Option α
  states : List (List α × List α)
  factors : List FactorRow
  packets : List (PacketRow α)
  stars : List (List StarRow)
  keyOrder : List ℕ
  hubs : List HubRow

/-- A state in orientation `sign` (`true`: as listed, `false`: side-swapped). -/
def orient (T : List α × List α) (sign : Bool) : List α × List α := if sign then T else T.swap

/-- Mojo `normalise`: the first differing letter of the top track is the smaller one. -/
def isNormal [LT α] [DecidableLT α] : List α → List α → Bool
  | a :: u, b :: v => if a < b then true else if b < a then false else isNormal u v
  | _, _ => true

/-- The literal occurrence pair a packet row names (`none`: the row names none). -/
def Table.decode (t : Table α) (p : PacketRow α) : Option (Occ α) :=
  match t.states[p.state]? with
  | none => none
  | some T =>
    match p.factor with
    | none => if p.sign then some ⟨T, p.top, p.bot, none⟩ else none
    | some f =>
      match t.factors[f]? with
      | none => none
      | some fr =>
        match t.states[fr.parent]? with
        | none => none
        | some P =>
          if fr.child = p.state then
            some ⟨orient T p.sign, p.top, p.bot, some ⟨orient P (p.sign == fr.sign), fr.ordinal⟩⟩
          else none

/-- The literal occurrence pair of row `i` (`none` beyond the last row). -/
def Table.decodeAt (t : Table α) (i : ℕ) : Option (Occ α) := t.packets[i]? >>= t.decode

/-- The literal occurrence pair of packet `i` (a default value only off an accepted table). -/
def Table.occAt (t : Table α) (i : Fin t.packets.length) : Occ α :=
  (t.decodeAt i.val).getD ⟨([], []), 0, 0, none⟩

/-- The literal ordered factorisation of a state, one entry per block of
`red (σ T.1) (σ T.2)`: (normalised child, sign, ordinal, start, stop, total length). -/
def literalFactors [LT α] [DecidableLT α] (s : α → List α) (T : List α × List α) :
    List (Option (List α × List α) × Bool × ℕ × ℕ × ℕ × ℕ) :=
  let bs := red (subst s T.1) (subst s T.2)
  (List.range bs.length).map fun k =>
    let U := bs.getD k ([], [])
    (some (orient U (isNormal U.1 U.2)), isNormal U.1 U.2, k, blockStart bs k,
      blockStart bs (k + 1), (subst s T.1).length)

/-- The residual coordinates are a listing of the alphabet without repetition. -/
def Table.lettersOK [Fintype α] (t : Table α) : Bool :=
  decide t.letters.Nodup && decide (∀ a, a ∈ t.letters)

/-- Every state is an irreducible block in normalised orientation; no repetition. -/
def Table.statesOK [Fintype α] [LT α] [DecidableLT α] (t : Table α) : Bool :=
  decide t.states.Nodup && t.states.all fun T => decide (IsBlock T) && isNormal T.1 T.2

/-- **Seeds**: every normalised seed `([a, b], [b, a])`, `a < b`, of the listed
alphabet is a listed state (Mojo `_prepare`). -/
def Table.seedsOK [LT α] [DecidableLT α] (t : Table α) : Bool :=
  t.letters.all fun a => t.letters.all fun b =>
    !decide (a < b) || decide (([a, b], [b, a]) ∈ t.states)

/-- Per noncoincident state, the factor rows are the literal ordered factorisation; no row
under a coincidence. -/
def Table.factorsOK [LT α] [DecidableLT α] (t : Table α) : Bool :=
  t.factors.all (fun f => decide (f.parent < t.states.length)) &&
  (List.range t.states.length).all fun i =>
    match t.states[i]? with
    | none => false
    | some T =>
      let rows := t.factors.filter fun f => f.parent = i
      if T.1 = T.2 then rows.isEmpty
      else decide (rows.map (fun f => (t.states[f.child]?, f.sign, f.ordinal, f.start, f.stop,
        f.total)) = literalFactors t.s T)

/-- The decoded row is a valid occurrence pair and every carried field is its literal value. -/
def Table.packetOK [Fintype α] (t : Table α) (p : PacketRow α) : Bool :=
  match t.decode p with
  | none => false
  | some x =>
    decide (x.Valid t.s) &&
    decide (p.topAddr = x.topAddr t.s) && decide (p.botAddr = x.botAddr t.s) &&
    decide (x.block.1[x.top]? = some p.letters.1) &&
    decide (x.block.2[x.bot]? = some p.letters.2) &&
    decide (p.residual = t.letters.map x.residual) &&
    decide (p.interior = decide x.Interior) && decide (p.success = decide (x.SuccessFor t.target))

/-- A star entry as a digit pair with an outcome (`none` for an out-of-range destination). -/
def Table.decodeEntry (t : Table α) : StarRow → ℕ × ℕ × Option (Outcome α)
  | .child d e dst => (d, e, (t.decodeAt dst).map Outcome.child)
  | .split d e k k' => (d, e, some (.split k k'))

/-- **The star equation**: the decoded star is the literal star `occStar` of the decoded row,
in order, children and splits together. -/
def Table.starOK (t : Table α) (p : PacketRow α) (star : List StarRow) : Bool :=
  match t.decode p with
  | none => false
  | some x =>
    decide (star.map t.decodeEntry = (occStar t.s x).map fun r => (r.1, r.2.1, some r.2.2))

/-- Key code; distinct codes give distinct keys (no injectivity of the code is needed). -/
def Table.keyCode (t : Table α) (p : PacketRow α) : ℕ :=
  let B := (t.states.map (·.1.length)).foldl max 0 + 1
  let F := t.factors.length + 1
  ((((p.state * 2 + (if p.sign then 1 else 0)) * B + p.top) * B + p.bot) * F +
    (match p.factor with | none => 0 | some f => f + 1))

/-- A list of defined values, strictly increasing. -/
def increasing : List (Option ℕ) → Bool
  | some a :: some b :: rest => decide (a < b) && increasing (some b :: rest)
  | [some _] => true
  | [] => true
  | _ => false

/-- Keys pairwise distinct, by a supplied order of strictly increasing key codes (linear in
the kernel; `List.Nodup` of the keys is quadratic). -/
def Table.keysOK (t : Table α) : Bool :=
  decide (t.keyOrder.length = t.packets.length) &&
    increasing (t.keyOrder.map fun i => t.packets[i]?.map t.keyCode)

/-- The root rows are exactly `(state, +, P, Q)` for every noncoincident state and every
position pair, in order. -/
def Table.rootsOK (t : Table α) : Bool :=
  decide ((t.packets.filter fun p => p.factor.isNone).map
      (fun p => (p.state, p.sign, p.top, p.bot)) =
    (List.range t.states.length).flatMap fun i =>
      match t.states[i]? with
      | none => []
      | some T =>
        if T.1 = T.2 then [] else
          (List.range T.1.length).flatMap fun P =>
            (List.range T.2.length).map fun Q => (i, true, P, Q))

/-- Every non-root row names an earlier row and a digit pair whose star entry is this row. -/
def Table.birthOK (t : Table α) : Bool :=
  (List.range t.packets.length).all fun i =>
    match t.packets[i]? with
    | none => false
    | some p =>
      match p.factor, p.birth with
      | none, none => true
      | some _, some (j, d, e) => decide (j < i) && (t.stars.getD j []).contains (.child d e i)
      | _, _ => false

/-- Mojo `hub_side`: `some false` if the top first letter is the hub, `some true` if the bottom
one is, `none` on a diagonal first pair or without the hub. -/
def hubSide (T : List α × List α) (h : α) : Option Bool :=
  match T.1.head?, T.2.head? with
  | some a, some b => if a = b then none else if a = h then some false
      else if b = h then some true else none
  | _, _ => none

/-- Mojo `factor_hub_residual`: parent xor child xor (sign = -1); `none` if either is undefined. -/
def Table.factorHub (t : Table α) (f : FactorRow) (h : α) : Option Bool := do
  let P ← t.states[f.parent]?
  let C ← t.states[f.child]?
  let a ← hubSide P h
  let b ← hubSide C h
  pure (xor (xor a b) (!f.sign))

/-- Hub rows: at most one per `(state, hub)`; each names a noncoincident listed state and a
listed letter, and its bits are `factorHub` over the factor rows of the state, slot by slot.
Undefined bits must be exported as `none`: a coerced `0/1` is refused, and so is `none` at a
defined slot. -/
def Table.hubsOK (t : Table α) : Bool :=
  decide (t.hubs.map fun r => (r.state, r.hub)).Nodup &&
  t.hubs.all fun r =>
    match t.states[r.state]?, t.letters[r.hub]? with
    | some T, some h => !decide (T.1 = T.2) &&
        decide (r.bits = (t.factors.filter (·.parent = r.state)).map (t.factorHub · h))
    | _, _ => false

/-- **The checker**: eleven clauses (ten structural clauses and `seedsOK`). -/
def Table.check [Fintype α] [LT α] [DecidableLT α] (t : Table α) : Bool :=
  t.lettersOK && t.statesOK && t.seedsOK && t.factorsOK && t.keysOK && t.rootsOK &&
    t.birthOK && decide (t.stars.length = t.packets.length) &&
    t.packets.all t.packetOK &&
    (t.packets.zip t.stars).all (fun ps => t.starOK ps.1 ps.2) &&
    t.hubsOK

/-- The packet graph of a table, with the coincidence-state target. -/
def Table.graph (t : Table α) : ChildGraph (Fin t.packets.length) where
  child i j := ∃ d e, StarRow.child d e j.val ∈ t.stars.getD i.val []
  target i := ∀ T, t.states[(t.packets[i]).state]? = some T → T.1 = T.2

/-- The packet graph of a table, with the exported `success` bit as target. -/
def Table.graphSuccess (t : Table α) : ChildGraph (Fin t.packets.length) where
  child := t.graph.child
  target i := (t.packets[i]).success = true

/-! ### The clauses of an accepted table -/

/-- The eleven clauses of `Table.check`, one field each. -/
structure Table.Accepted [Fintype α] [LT α] [DecidableLT α] (t : Table α) : Prop where
  lettersOK : t.lettersOK = true
  statesOK : t.statesOK = true
  seedsOK : t.seedsOK = true
  factorsOK : t.factorsOK = true
  keysOK : t.keysOK = true
  rootsOK : t.rootsOK = true
  birthOK : t.birthOK = true
  length : t.stars.length = t.packets.length
  packetsOK : t.packets.all t.packetOK = true
  starsOK : (t.packets.zip t.stars).all (fun ps => t.starOK ps.1 ps.2) = true
  hubsOK : t.hubsOK = true

section Accepted

variable [Fintype α] [LT α] [DecidableLT α]

/-- `Table.check` is the conjunction of the eleven clauses. -/
theorem Table.check_iff (t : Table α) : t.check = true ↔ t.Accepted := by
  constructor
  · intro h
    simp only [Table.check, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · intro h
    simp only [Table.check, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.lettersOK, h.statesOK⟩, h.seedsOK⟩, h.factorsOK⟩, h.keysOK⟩, h.rootsOK⟩,
      h.birthOK⟩, h.length⟩, h.packetsOK⟩, h.starsOK⟩, h.hubsOK⟩

end Accepted

/-! ### Decoding -/

omit [DecidableEq α] in
/-- What a decoded row is: a root reading `⟨T, top, bot, none⟩` of its state in listed
orientation, or the reading of its state in orientation `sign` born through its factor row. -/
theorem Table.decode_some {t : Table α} {p : PacketRow α} {x : Occ α}
    (h : t.decode p = some x) :
    ∃ T, t.states[p.state]? = some T ∧
      ((p.factor = none ∧ p.sign = true ∧ x = ⟨T, p.top, p.bot, none⟩) ∨
        ∃ f fr P, p.factor = some f ∧ t.factors[f]? = some fr ∧ t.states[fr.parent]? = some P ∧
          fr.child = p.state ∧
          x = ⟨orient T p.sign, p.top, p.bot,
            some ⟨orient P (p.sign == fr.sign), fr.ordinal⟩⟩) := by
  unfold Table.decode at h
  split at h
  · exact absurd h (by simp)
  · rename_i T hT
    refine ⟨T, hT, ?_⟩
    split at h
    · rename_i hf
      split_ifs at h with hs
      exact Or.inl ⟨hf, hs, (Option.some.inj h).symm⟩
    · rename_i f hf
      split at h
      · exact absurd h (by simp)
      · rename_i fr hfr
        split at h
        · exact absurd h (by simp)
        · rename_i P hP
          split_ifs at h with hc
          exact Or.inr ⟨f, fr, P, hf, hfr, hP, hc, (Option.some.inj h).symm⟩

omit [DecidableEq α] in
/-- The block of a decoded row is its state in the row's orientation. -/
theorem Table.decode_block {t : Table α} {p : PacketRow α} {x : Occ α}
    (h : t.decode p = some x) :
    ∃ T, t.states[p.state]? = some T ∧ x.block = orient T p.sign := by
  obtain ⟨T, hT, ⟨-, hs, rfl⟩ | ⟨f, fr, P, -, -, -, -, rfl⟩⟩ := Table.decode_some h
  · exact ⟨T, hT, by simp [orient, hs]⟩
  · exact ⟨T, hT, rfl⟩

omit [DecidableEq α] in
/-- An oriented state is a coincidence iff the state is. -/
theorem orient_coincident (T : List α × List α) (b : Bool) :
    (orient T b).1 = (orient T b).2 ↔ T.1 = T.2 := by
  cases b <;> simp [orient, eq_comm]

omit [DecidableEq α] in
/-- `decodeAt` is `some` only on a row. -/
theorem Table.lt_of_decodeAt {t : Table α} {j : ℕ} {y : Occ α} (h : t.decodeAt j = some y) :
    j < t.packets.length := by
  by_contra hj
  rw [Table.decodeAt, List.getElem?_eq_none (by omega)] at h
  exact absurd h (by simp)

omit [DecidableEq α] in
/-- `decodeAt` on a row index is `decode` of the row. -/
theorem Table.decodeAt_eq_decode (t : Table α) (i : Fin t.packets.length) :
    t.decodeAt i.val = t.decode t.packets[i] := by
  simp [Table.decodeAt]

/-! ### The row clause -/

section Accepted

variable [Fintype α]

/-- What `packetOK` says about a row. -/
theorem Table.packetOK_spec {t : Table α} {p : PacketRow α} (h : t.packetOK p = true) :
    ∃ x, t.decode p = some x ∧ x.Valid t.s ∧ p.topAddr = x.topAddr t.s ∧
      p.botAddr = x.botAddr t.s ∧ x.block.1[x.top]? = some p.letters.1 ∧
      x.block.2[x.bot]? = some p.letters.2 ∧ p.residual = t.letters.map x.residual ∧
      (p.interior = true ↔ x.Interior) ∧ (p.success = true ↔ x.SuccessFor t.target) := by
  unfold Table.packetOK at h
  cases hd : t.decode p with
  | none => rw [hd] at h; exact absurd h (by simp)
  | some x =>
    rw [hd] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hv, ha⟩, hb⟩, hl1⟩, hl2⟩, hr⟩, hi⟩, hs⟩ := h
    exact ⟨x, rfl, hv, ha, hb, hl1, hl2, hr, by rw [hi]; simp, by rw [hs]; simp⟩

variable [LT α] [DecidableLT α]

/-- The row clause of every row. -/
theorem Table.Accepted.packetOK {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    t.packetOK t.packets[i] = true :=
  List.all_eq_true.1 h.packetsOK _ (List.getElem_mem _)

/-- On an accepted table every row decodes, to `occAt`. -/
theorem Table.Accepted.decodeAt_eq {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    t.decodeAt i.val = some (t.occAt i) := by
  obtain ⟨x, hx, -⟩ := Table.packetOK_spec (h.packetOK i)
  unfold Table.occAt
  rw [Table.decodeAt_eq_decode, hx]
  rfl

/-- On an accepted table every row decodes, to `occAt` (row form). -/
theorem Table.Accepted.decode_eq {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    t.decode t.packets[i] = some (t.occAt i) := by
  rw [← Table.decodeAt_eq_decode]
  exact h.decodeAt_eq i

/-- A destination that decodes is a row, and decodes to that row's occurrence pair. -/
theorem Table.Accepted.decodeAt_some {t : Table α} (h : t.Accepted) {j : ℕ} {y : Occ α}
    (hj : t.decodeAt j = some y) : ∃ k : Fin t.packets.length, k.val = j ∧ t.occAt k = y := by
  refine ⟨⟨j, Table.lt_of_decodeAt hj⟩, rfl, ?_⟩
  have := h.decodeAt_eq ⟨j, Table.lt_of_decodeAt hj⟩
  rw [hj] at this
  exact (Option.some.inj this).symm

/-- The carried fields of every row are the literal fields of its occurrence pair. -/
theorem Table.Accepted.fields {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    (t.occAt i).Valid t.s ∧
    (t.packets[i]).topAddr = (t.occAt i).topAddr t.s ∧
    (t.packets[i]).botAddr = (t.occAt i).botAddr t.s ∧
    (t.occAt i).block.1[(t.occAt i).top]? = some (t.packets[i]).letters.1 ∧
    (t.occAt i).block.2[(t.occAt i).bot]? = some (t.packets[i]).letters.2 ∧
    (t.packets[i]).residual = t.letters.map (t.occAt i).residual ∧
    ((t.packets[i]).interior = true ↔ (t.occAt i).Interior) ∧
    ((t.packets[i]).success = true ↔ (t.occAt i).SuccessFor t.target) := by
  obtain ⟨x, hx, hrest⟩ := Table.packetOK_spec (h.packetOK i)
  rw [h.decode_eq i] at hx
  obtain rfl := Option.some.inj hx
  exact hrest

end Accepted

/-! ### The star clause -/

section Stars

variable [Fintype α] [LT α] [DecidableLT α]

/-- The star clause of every row, with the row's star read by `getD`. -/
theorem Table.Accepted.starOK {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    t.starOK t.packets[i] (t.stars.getD i.val []) = true := by
  have hi : i.val < t.stars.length := by rw [h.length]; exact i.isLt
  have hz : i.val < (t.packets.zip t.stars).length := by simp [h.length]
  have hmem : (t.packets.zip t.stars)[i.val] ∈ t.packets.zip t.stars := List.getElem_mem hz
  have := List.all_eq_true.1 h.starsOK _ hmem
  rw [List.getElem_zip] at this
  rw [List.getD_eq_getElem _ _ hi]
  exact this

/-- **The star equation of every row.** -/
theorem Table.Accepted.star_eq {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    (t.stars.getD i.val []).map t.decodeEntry =
      (occStar t.s (t.occAt i)).map fun r => (r.1, r.2.1, some r.2.2) := by
  have := h.starOK i
  unfold Table.starOK at this
  rw [h.decode_eq i] at this
  simpa using this

omit [DecidableEq α] [Fintype α] [LT α] [DecidableLT α] in
/-- Reading a star entry with its outcome under `some`. -/
theorem mem_map_some {L : List (ℕ × ℕ × Outcome α)} {d e : ℕ} {o : Outcome α} :
    (d, e, some o) ∈ L.map (fun r => (r.1, r.2.1, some r.2.2)) ↔ (d, e, o) ∈ L := by
  simp only [List.mem_map, Prod.mk.injEq, Option.some.injEq]
  constructor
  · rintro ⟨⟨d', e', o'⟩, hm, rfl, rfl, rfl⟩
    exact hm
  · intro hm
    exact ⟨(d, e, o), hm, rfl, rfl, rfl⟩

/-- A child entry of a row's star is a literal digit pair of the row with a child outcome, and
conversely every literal child outcome is listed, by a destination that decodes to it. -/
theorem Table.Accepted.child_entry_iff {t : Table α} (h : t.Accepted) (i : Fin t.packets.length)
    (d e : ℕ) (y : Occ α) :
    (∃ dst, StarRow.child d e dst ∈ t.stars.getD i.val [] ∧ t.decodeAt dst = some y) ↔
      (d, e, Outcome.child y) ∈ occStar t.s (t.occAt i) := by
  rw [← mem_map_some, ← h.star_eq i]
  constructor
  · rintro ⟨dst, hm, hd⟩
    refine List.mem_map.2 ⟨_, hm, ?_⟩
    simp [Table.decodeEntry, hd]
  · intro hm
    obtain ⟨r, hr, hre⟩ := List.mem_map.1 hm
    cases r with
    | child d' e' dst =>
      simp only [Table.decodeEntry, Prod.mk.injEq] at hre
      obtain ⟨rfl, rfl, hd⟩ := hre
      obtain ⟨y', hy', hyy⟩ := Option.map_eq_some_iff.1 hd
      cases hyy
      exact ⟨dst, hr, hy'⟩
    | split d' e' k k' =>
      simp [Table.decodeEntry] at hre

/-- **Every listed edge is a literal edge** (`Embeds.sound` in the shape of
`Psc.GraphRefinement.Embeds`, module `PscVerif.GraphEmbedding`). -/
theorem Table.Accepted.graph_sound {t : Table α} (h : t.Accepted) {i j : Fin t.packets.length}
    (hij : t.graph.child i j) : occChild t.s (t.occAt i) (t.occAt j) := by
  obtain ⟨d, e, hm⟩ := hij
  have := (h.child_entry_iff i d e (t.occAt j)).1 ⟨j.val, hm, h.decodeAt_eq j⟩
  exact (mem_occStar.1 this).elim fun hne hs => ⟨hne, d, e, hs⟩

/-- **Full child stars**: every literal child of a row's occurrence pair is the occurrence
pair of a listed child (`Embeds.complete` in the shape of `Psc.GraphRefinement.Embeds`). -/
theorem Table.Accepted.graph_complete {t : Table α} (h : t.Accepted) (i : Fin t.packets.length)
    {y : Occ α} (hy : occChild t.s (t.occAt i) y) :
    ∃ j, t.graph.child i j ∧ t.occAt j = y := by
  obtain ⟨hne, d, e, hs⟩ := hy
  obtain ⟨dst, hm, hd⟩ := (h.child_entry_iff i d e y).2 (mem_occStar.2 ⟨hne, hs⟩)
  obtain ⟨k, rfl, hk⟩ := h.decodeAt_some hd
  exact ⟨k, ⟨d, e, hm⟩, hk⟩

/-- The range of `occAt` is child-closed in the literal occurrence graph. -/
theorem Table.Accepted.closed_range {t : Table α} (h : t.Accepted) :
    (occGraph t.s).Closed (Set.range t.occAt) := by
  rintro _ y ⟨i, rfl⟩ hy
  obtain ⟨j, -, hj⟩ := h.graph_complete i hy
  exact ⟨j, hj⟩

/-- The coincidence-state target of the packet graph is the target of `occGraph`. -/
theorem Table.Accepted.target_iff {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    t.graph.target i ↔ (t.occAt i).Coincident := by
  obtain ⟨T, hT, hb⟩ := Table.decode_block (h.decode_eq i)
  show (∀ T' : List α × List α, _ = some T' → T'.1 = T'.2) ↔
    (t.occAt i).block.1 = (t.occAt i).block.2
  rw [hb, orient_coincident]
  constructor
  · intro hc
    exact hc T hT
  · intro hc T' hT'
    rw [hT] at hT'
    obtain rfl := Option.some.inj hT'
    exact hc

/-- The exported `success` bit is the packet success of `occGraphFor`. -/
theorem Table.Accepted.success_iff {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    t.graphSuccess.target i ↔ (t.occAt i).SuccessFor t.target :=
  (h.fields i).2.2.2.2.2.2.2

end Stars

/-! ### Roots, births, hubs, seeds -/

section Rows

variable [Fintype α] [LT α] [DecidableLT α]

/-- Every position pair of every noncoincident listed state is a root row. -/
theorem Table.Accepted.roots {t : Table α} (h : t.Accepted) {k : ℕ} {T : List α × List α}
    (hT : t.states[k]? = some T) (hnc : T.1 ≠ T.2) {P Q : ℕ} (hP : P < T.1.length)
    (hQ : Q < T.2.length) :
    ∃ i : Fin t.packets.length, (t.packets[i]).factor = none ∧ t.occAt i = ⟨T, P, Q, none⟩ := by
  have hr := h.rootsOK
  unfold Table.rootsOK at hr
  rw [decide_eq_true_eq] at hr
  have hk : k < t.states.length := (List.getElem?_eq_some_iff.1 hT).1
  have hmem : (k, true, P, Q) ∈ (t.packets.filter fun p => p.factor.isNone).map
      (fun p => (p.state, p.sign, p.top, p.bot)) := by
    rw [hr, List.mem_flatMap]
    refine ⟨k, List.mem_range.2 hk, ?_⟩
    rw [hT]
    simp [hnc, hP, hQ]
  obtain ⟨p, hp, hpk⟩ := List.mem_map.1 hmem
  obtain ⟨hp, hfn⟩ := List.mem_filter.1 hp
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
  simp only [Prod.mk.injEq] at hpk
  obtain ⟨hs, hsg, htop, hbot⟩ := hpk
  have hf : (t.packets[i]).factor = none := Option.isNone_iff_eq_none.1 hfn
  refine ⟨⟨i, hi⟩, hf, ?_⟩
  have hd := h.decode_eq ⟨i, hi⟩
  have hd' : t.decode t.packets[i] = some ⟨T, P, Q, none⟩ := by
    unfold Table.decode
    rw [hs, hT, hf]
    simp [hsg, htop, hbot]
  exact Option.some.inj (hd.symm.trans hd')

/-- A root row reads a position pair of a noncoincident listed state, at the root. -/
theorem Table.Accepted.root_spec {t : Table α} (h : t.Accepted) (i : Fin t.packets.length)
    (hf : (t.packets[i]).factor = none) :
    ∃ T, t.states[(t.packets[i]).state]? = some T ∧ T.1 ≠ T.2 ∧
      (t.packets[i]).top < T.1.length ∧ (t.packets[i]).bot < T.2.length ∧
      t.occAt i = ⟨T, (t.packets[i]).top, (t.packets[i]).bot, none⟩ := by
  obtain ⟨T, hT, ⟨-, -, hx⟩ | ⟨f, -, -, hf', -⟩⟩ := Table.decode_some (h.decode_eq i)
  · have hv := (h.fields i).1
    rw [hx] at hv
    obtain ⟨-, hP, hQ, -⟩ := hv
    refine ⟨T, hT, ?_, hP, hQ, hx⟩
    have hr := h.rootsOK
    unfold Table.rootsOK at hr
    rw [decide_eq_true_eq] at hr
    have hmem : ((t.packets[i]).state, (t.packets[i]).sign, (t.packets[i]).top,
        (t.packets[i]).bot) ∈ (t.packets.filter fun p => p.factor.isNone).map
          (fun p => (p.state, p.sign, p.top, p.bot)) :=
      List.mem_map.2 ⟨_, List.mem_filter.2 ⟨List.getElem_mem _,
        Option.isNone_iff_eq_none.2 hf⟩, rfl⟩
    rw [hr, List.mem_flatMap] at hmem
    obtain ⟨k, -, hk⟩ := hmem
    split at hk
    · simp at hk
    · rename_i T' hT'
      split_ifs at hk with hc
      · simp at hk
      · simp only [List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq] at hk
        obtain ⟨-, -, -, -, rfl, -⟩ := hk
        rw [hT] at hT'
        obtain rfl := Option.some.inj hT'
        exact hc
  · rw [hf] at hf'
    exact absurd hf' (by simp)

/-- **Reachability from roots** (`birthOK`, by strong induction on the row index). -/
theorem Table.Accepted.reach_root {t : Table α} (h : t.Accepted) (i : Fin t.packets.length) :
    ∃ r : Fin t.packets.length, (t.packets[r]).factor = none ∧ t.graph.Reach r i := by
  suffices H : ∀ n (i : Fin t.packets.length), i.val = n →
      ∃ r : Fin t.packets.length, (t.packets[r]).factor = none ∧ t.graph.Reach r i from
    H _ i rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i hi
    have hb := List.all_eq_true.1 h.birthOK i.val (List.mem_range.2 i.isLt)
    rw [List.getElem?_eq_getElem i.isLt] at hb
    simp only at hb
    split at hb
    · rename_i hf _
      exact ⟨i, hf, .refl⟩
    · rename_i f j d e hf _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨hj, hc⟩ := hb
      have hjn : j < t.packets.length := lt_trans hj i.isLt
      obtain ⟨r, hr, hreach⟩ := ih j (hi ▸ hj) ⟨j, hjn⟩ rfl
      exact ⟨r, hr, hreach.tail ⟨d, e, List.contains_iff_mem.1 hc⟩⟩
    · exact absurd hb (by simp)

/-- Hub rows: each names a noncoincident listed state and a listed letter, and its bits are
`factorHub` slot by slot (defined exactly where the literal hub residual is defined). -/
theorem Table.Accepted.hubs_spec {t : Table α} (h : t.Accepted) {r : HubRow} (hr : r ∈ t.hubs) :
    ∃ T hub, t.states[r.state]? = some T ∧ T.1 ≠ T.2 ∧ t.letters[r.hub]? = some hub ∧
      r.bits = (t.factors.filter (·.parent = r.state)).map (t.factorHub · hub) := by
  have hh := h.hubsOK
  simp only [Table.hubsOK, Bool.and_eq_true] at hh
  have := List.all_eq_true.1 hh.2 r hr
  split at this
  · rename_i T hub hT hhub
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at this
    exact ⟨T, hub, hT, this.1, hhub, this.2⟩
  · exact absurd this (by simp)

/-- At most one hub row per `(state, hub)`. -/
theorem Table.Accepted.hubs_nodup {t : Table α} (h : t.Accepted) :
    (t.hubs.map fun r => (r.state, r.hub)).Nodup := by
  have hh := h.hubsOK
  simp only [Table.hubsOK, Bool.and_eq_true] at hh
  exact of_decide_eq_true hh.1

/-- Every normalised seed `([a, b], [b, a])`, `a < b`, is a listed state. -/
theorem Table.Accepted.seed_mem {t : Table α} (h : t.Accepted) {a b : α} (hab : a < b) :
    ([a, b], [b, a]) ∈ t.states := by
  have hl := h.lettersOK
  simp only [Table.lettersOK, Bool.and_eq_true, decide_eq_true_eq] at hl
  have := List.all_eq_true.1 (List.all_eq_true.1 h.seedsOK a (hl.2 a)) b (hl.2 b)
  simpa [hab] using this

/-- The factor rows of a listed noncoincident state are its literal ordered factorisation. -/
theorem Table.Accepted.factor_rows {t : Table α} (h : t.Accepted) {i : ℕ} {T : List α × List α}
    (hT : t.states[i]? = some T) (hnc : T.1 ≠ T.2) :
    (t.factors.filter fun f => f.parent = i).map
        (fun f => (t.states[f.child]?, f.sign, f.ordinal, f.start, f.stop, f.total)) =
      literalFactors t.s T := by
  have hf := h.factorsOK
  simp only [Table.factorsOK, Bool.and_eq_true] at hf
  have hi : i < t.states.length := (List.getElem?_eq_some_iff.1 hT).1
  have := List.all_eq_true.1 hf.2 i (List.mem_range.2 hi)
  rw [hT] at this
  simp only [hnc, ite_false, decide_eq_true_eq] at this
  exact this

/-- No factor row hangs under a coincidence: the parent of every factor row is noncoincident. -/
theorem Table.Accepted.parent_nc {t : Table α} (h : t.Accepted) {f : ℕ} {fr : FactorRow}
    (hfr : t.factors[f]? = some fr) {P : List α × List α} (hP : t.states[fr.parent]? = some P) :
    P.1 ≠ P.2 := by
  intro hc
  have hf := h.factorsOK
  simp only [Table.factorsOK, Bool.and_eq_true] at hf
  have hi : fr.parent < t.states.length := (List.getElem?_eq_some_iff.1 hP).1
  have := List.all_eq_true.1 hf.2 fr.parent (List.mem_range.2 hi)
  rw [hP] at this
  simp only [hc, ite_true, List.isEmpty_iff] at this
  have hm : fr ∈ t.factors.filter fun f => f.parent = fr.parent :=
    List.mem_filter.2 ⟨List.mem_of_getElem? hfr, by simp⟩
  rw [this] at hm
  exact absurd hm (by simp)

/-- The ordinals of the factor rows of a noncoincident listed state are `0, 1, …` in order. -/
theorem Table.Accepted.ordinals {t : Table α} (h : t.Accepted) {i : ℕ} {T : List α × List α}
    (hT : t.states[i]? = some T) (hnc : T.1 ≠ T.2) :
    (t.factors.filter fun f => f.parent = i).map (·.ordinal) =
      List.range (red (subst t.s T.1) (subst t.s T.2)).length := by
  have := congrArg (List.map fun r => r.2.2.1) (h.factor_rows hT hnc)
  rw [List.map_map] at this
  simpa [literalFactors, List.map_map, Function.comp_def] using this

/-- States are listed without repetition. -/
theorem Table.Accepted.state_index_inj {t : Table α} (h : t.Accepted) {k k' : ℕ}
    {T : List α × List α} (hk : t.states[k]? = some T) (hk' : t.states[k']? = some T) :
    k = k' := by
  have hs := h.statesOK
  simp only [Table.statesOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨hk1, hk2⟩ := List.getElem?_eq_some_iff.1 hk
  obtain ⟨hk1', hk2'⟩ := List.getElem?_eq_some_iff.1 hk'
  exact (hs.1.getElem_inj_iff (hi := hk1) (hj := hk1')).1 (hk2.trans hk2'.symm)

/-- Every listed state is an irreducible block in normalised orientation. -/
theorem Table.Accepted.state_spec {t : Table α} (h : t.Accepted) {T : List α × List α}
    (hT : T ∈ t.states) : IsBlock T ∧ isNormal T.1 T.2 = true := by
  have hs := h.statesOK
  simp only [Table.statesOK, Bool.and_eq_true, decide_eq_true_eq] at hs
  have := List.all_eq_true.1 hs.2 T hT
  simpa using this

/-- **The listed states are child-closed up to orientation** (`factorsOK`): every block of the
reduction of the image of a noncoincident listed state is a listed state or the swap of one. -/
theorem Table.Accepted.child_listed {t : Table α} (h : t.Accepted) {T U : List α × List α}
    (hT : T ∈ t.states) (hnc : T.1 ≠ T.2) (hU : U ∈ red (subst t.s T.1) (subst t.s T.2)) :
    U ∈ t.states ∨ U.swap ∈ t.states := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hT
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hU
  have hmem : ((red (subst t.s T.1) (subst t.s T.2)).length > j) := hj
  have hx : (some (orient (red (subst t.s T.1) (subst t.s T.2))[j]
      (isNormal (red (subst t.s T.1) (subst t.s T.2))[j].1
        (red (subst t.s T.1) (subst t.s T.2))[j].2)), isNormal
          (red (subst t.s T.1) (subst t.s T.2))[j].1 (red (subst t.s T.1) (subst t.s T.2))[j].2,
      j, blockStart (red (subst t.s T.1) (subst t.s T.2)) j,
      blockStart (red (subst t.s T.1) (subst t.s T.2)) (j + 1), (subst t.s T.1).length) ∈
        literalFactors t.s T := by
    unfold literalFactors
    exact List.mem_map.2 ⟨j, List.mem_range.2 hmem, by simp [List.getElem?_eq_getElem hj]⟩
  rw [← h.factor_rows hk hnc] at hx
  obtain ⟨f, -, hf⟩ := List.mem_map.1 hx
  have h1 := congrArg Prod.fst hf
  simp only at h1
  have hm := List.mem_of_getElem? h1
  cases hb : isNormal (red (subst t.s T.1) (subst t.s T.2))[j].1
      (red (subst t.s T.1) (subst t.s T.2))[j].2
  · rw [hb] at hm
    exact Or.inr hm
  · rw [hb] at hm
    exact Or.inl hm

end Rows

/-! ### Key codes -/

/-- Every entry after the head of an increasing list is a defined, larger value. -/
theorem increasing_cons_lt : ∀ {a : ℕ} {rest : List (Option ℕ)},
    increasing (some a :: rest) = true → ∀ o ∈ rest, ∃ b, o = some b ∧ a < b
  | _, [], _ => by simp
  | a, none :: rest, h => by simp [increasing] at h
  | a, some b :: rest, h => by
    simp only [increasing, Bool.and_eq_true, decide_eq_true_eq] at h
    intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · exact ⟨b, rfl, h.1⟩
    · obtain ⟨c, rfl, hc⟩ := increasing_cons_lt h.2 o ho
      exact ⟨c, rfl, lt_trans h.1 hc⟩

/-- An increasing list has no repetition and only defined entries. -/
theorem increasing_spec : ∀ {l : List (Option ℕ)}, increasing l = true →
    l.Nodup ∧ ∀ o ∈ l, o.isSome
  | [], _ => by simp
  | none :: rest, h => by simp [increasing] at h
  | some a :: rest, h => by
    have hlt := increasing_cons_lt h
    have htail : increasing rest = true := by
      match rest, h with
      | [], _ => rfl
      | none :: _, h => simp [increasing] at h
      | some _ :: _, h =>
        simp only [increasing, Bool.and_eq_true] at h
        exact h.2
    obtain ⟨hnd, hsome⟩ := increasing_spec htail
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, ?_⟩
    · obtain ⟨b, hb, hab⟩ := hlt _ hm
      cases hb
      exact lt_irrefl _ hab
    · intro o ho
      rcases List.mem_cons.1 ho with rfl | ho
      · rfl
      · exact hsome o ho

section Keys

variable [Fintype α] [LT α] [DecidableLT α]

/-- **Distinct rows have distinct key codes** (`keysOK`: the supplied order is a permutation of
the rows along which the codes strictly increase). -/
theorem Table.Accepted.keyCode_inj {t : Table α} (h : t.Accepted) {i j : Fin t.packets.length}
    (hk : t.keyCode t.packets[i] = t.keyCode t.packets[j]) : i = j := by
  have hK := h.keysOK
  simp only [Table.keysOK, Bool.and_eq_true, decide_eq_true_eq] at hK
  obtain ⟨hlen, hinc⟩ := hK
  obtain ⟨hnd, hsome⟩ := increasing_spec hinc
  have hnd' : t.keyOrder.Nodup := hnd.of_map _
  have hlt : ∀ k ∈ t.keyOrder, k < t.packets.length := by
    intro k hk
    have := hsome _ (List.mem_map_of_mem hk)
    by_contra hge
    rw [List.getElem?_eq_none (by omega)] at this
    exact absurd this (by simp)
  have hall : ∀ k < t.packets.length, k ∈ t.keyOrder := by
    have hsub : t.keyOrder.toFinset ⊆ Finset.range t.packets.length := by
      intro k hk
      exact Finset.mem_range.2 (hlt k (List.mem_toFinset.1 hk))
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [List.toFinset_card_of_nodup hnd', hlen, Finset.card_range])
    intro k hk
    have : k ∈ t.keyOrder.toFinset := by rw [heq]; exact Finset.mem_range.2 hk
    exact List.mem_toFinset.1 this
  apply Fin.ext
  refine List.inj_on_of_nodup_map hnd (hall _ i.isLt) (hall _ j.isLt) ?_
  simp only [List.getElem?_eq_getElem i.isLt, List.getElem?_eq_getElem j.isLt, Option.map_some]
  exact congrArg some hk

end Keys

/-! ### Injectivity of `occAt` (needs a linear order on the letters) -/

/-- Two distinct indices of a list whose filtered images are distinct have distinct images. -/
theorem filter_map_inj {β γ : Type*} : ∀ {l : List β} {q : β → Bool} {g : β → γ},
    ((l.filter q).map g).Nodup → ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length),
      q l[i] = true → q l[j] = true → g l[i] = g l[j] → i = j
  | [], _, _, _, _, _, hi, _, _, _, _ => absurd hi (by simp)
  | a :: l, q, g, hnd, i, j, hi, hj, hqi, hqj, hg => by
    have hsub : ((l.filter q).map g).Nodup :=
      hnd.sublist (((List.sublist_cons_self a l).filter q).map g)
    match i, j, hi, hj, hqi, hqj, hg with
    | 0, 0, _, _, _, _, _ => rfl
    | 0, j + 1, _, hj, hqi, hqj, hg =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hqi hqj hg
      rw [List.filter_cons_of_pos hqi, List.map_cons, List.nodup_cons] at hnd
      exact absurd (List.mem_map.2 ⟨l[j]'(by simpa using hj),
        List.mem_filter.2 ⟨List.getElem_mem _, hqj⟩, hg.symm⟩)
        hnd.1
    | i + 1, 0, hi, _, hqi, hqj, hg =>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at hqi hqj hg
      rw [List.filter_cons_of_pos hqj, List.map_cons, List.nodup_cons] at hnd
      exact absurd (List.mem_map.2 ⟨l[i]'(by simpa using hi),
        List.mem_filter.2 ⟨List.getElem_mem _, hqi⟩, hg⟩)
        hnd.1
    | i + 1, j + 1, hi, hj, hqi, hqj, hg =>
      simp only [List.getElem_cons_succ] at hqi hqj hg
      have := filter_map_inj hsub (by simpa using hi) (by simpa using hj) hqi hqj hg
      omega

section Linear

variable [Fintype α] [LinearOrder α]

omit [DecidableEq α] [Fintype α] in
/-- Under a linear order, exactly one orientation of a pair with distinct first letters is
normalised. -/
theorem isNormal_cons_ne {a b : α} (hab : a ≠ b) (u v : List α) :
    isNormal (a :: u) (b :: v) = !isNormal (b :: v) (a :: u) := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · simp [isNormal, hlt, not_lt_of_gt hlt]
  · simp [isNormal, hlt, not_lt_of_gt hlt]

omit [Fintype α] in
/-- A noncoincident irreducible block and its swap are not both normalised. -/
theorem not_isNormal_both {P : List α × List α} (hB : IsBlock P) (hnc : P.1 ≠ P.2)
    (h1 : isNormal P.1 P.2 = true) (h2 : isNormal P.2 P.1 = true) : False := by
  obtain ⟨u, v⟩ := P
  obtain ⟨hu, hbal, hirr⟩ := hB
  match u, v, hu, hbal.length_eq with
  | a :: u', b :: v', _, _ =>
    have hab : a ≠ b := heads_ne hbal hirr hnc
    rw [isNormal_cons_ne hab] at h1
    simp_all
  | [], _, hu, _ => exact hu rfl
  | _ :: _, [], _, hl => simp at hl

/-- An oriented listed noncoincident state determines the state and the orientation. -/
theorem Table.Accepted.orient_inj {t : Table α} (h : t.Accepted) {P P' : List α × List α}
    (hP : P ∈ t.states) (hP' : P' ∈ t.states) (hnc : P.1 ≠ P.2) {b b' : Bool}
    (he : orient P b = orient P' b') : P = P' ∧ b = b' := by
  obtain ⟨hB, hn⟩ := h.state_spec hP
  obtain ⟨-, hn'⟩ := h.state_spec hP'
  rcases b with _ | _ <;> rcases b' with _ | _ <;>
    simp only [orient, Bool.false_eq_true, ite_false, ite_true] at he
  · exact ⟨Prod.swap_injective he, rfl⟩
  · subst he
    exact (not_isNormal_both hB hnc hn hn').elim
  · subst he
    exact (not_isNormal_both hB hnc hn hn').elim
  · exact ⟨he, rfl⟩

/-- **Decoding is injective on keys**: two rows of an accepted table that decode to the same
occurrence pair have the same key `(state, sign, top, bot, factor)`. -/
theorem Table.Accepted.decode_inj {t : Table α} (h : t.Accepted) {p p' : PacketRow α}
    {x : Occ α} (hp : t.decode p = some x) (hp' : t.decode p' = some x) :
    p.state = p'.state ∧ p.sign = p'.sign ∧ p.top = p'.top ∧ p.bot = p'.bot ∧
      p.factor = p'.factor := by
  obtain ⟨T, hT, ⟨hf, hs, rfl⟩ | ⟨f, fr, P, hf, hfr, hP, hch, rfl⟩⟩ := Table.decode_some hp <;>
    obtain ⟨T', hT', ⟨hf', hs', hx⟩ | ⟨f', fr', P', hf', hfr', hP', hch', hx⟩⟩ :=
      Table.decode_some hp'
  · simp only [Occ.mk.injEq] at hx
    obtain ⟨rfl, htop, hbot, -⟩ := hx
    exact ⟨h.state_index_inj hT hT', hs.trans hs'.symm, htop, hbot, hf.trans hf'.symm⟩
  · exact absurd (congrArg Occ.birth hx) (by simp)
  · exact absurd (congrArg Occ.birth hx) (by simp)
  · simp only [Occ.mk.injEq, Option.some.injEq, Birth.mk.injEq] at hx
    obtain ⟨hTT, htop, hbot, hPP, hord⟩ := hx
    have hnc : P.1 ≠ P.2 := h.parent_nc hfr hP
    obtain ⟨rfl, hsg⟩ := h.orient_inj (List.mem_of_getElem? hP) (List.mem_of_getElem? hP') hnc
      hPP
    have hpar : fr.parent = fr'.parent := h.state_index_inj hP hP'
    obtain ⟨hf1, hf2⟩ := List.getElem?_eq_some_iff.1 hfr
    obtain ⟨hf1', hf2'⟩ := List.getElem?_eq_some_iff.1 hfr'
    have hnd : ((t.factors.filter fun g => g.parent = fr.parent).map (·.ordinal)).Nodup := by
      rw [h.ordinals hP hnc]
      exact List.nodup_range
    have hff : f = f' := filter_map_inj hnd hf1 hf1' (by simp [hf2]) (by simp [hf2', hpar])
      (by rw [hf2, hf2']; exact hord)
    subst hff
    rw [hfr] at hfr'
    obtain rfl := Option.some.inj hfr'
    refine ⟨hch.symm.trans hch', ?_, htop, hbot, hf.trans hf'.symm⟩
    cases hp1 : p.sign <;> cases hp2 : p'.sign <;> cases hfs : fr.sign <;>
      simp_all

/-- **Injectivity of `occAt`** on an accepted table over a linearly ordered alphabet. -/
theorem Table.Accepted.occAt_injective {t : Table α} (h : t.Accepted) :
    Function.Injective t.occAt := by
  intro i j hij
  have hi := h.decode_eq i
  have hj := h.decode_eq j
  rw [← hij] at hj
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.decode_inj hi hj
  apply h.keyCode_inj
  unfold Table.keyCode
  rw [h1, h2, h3, h4, h5]

end Linear

/-! ### What an accepted table is -/

section Headline

variable [Fintype α]

section Order

variable [LT α] [DecidableLT α]

/-- **Every listed edge is a literal edge** (no order hypothesis). -/
theorem Table.graph_sound (t : Table α) (h : t.check = true) {i j : Fin t.packets.length}
    (hij : t.graph.child i j) : (occGraph t.s).child (t.occAt i) (t.occAt j) :=
  ((Table.check_iff t).1 h).graph_sound hij

/-- **Full child stars**: every literal child of a row's occurrence pair is listed (no order
hypothesis). -/
theorem Table.graph_complete (t : Table α) (h : t.check = true) (i : Fin t.packets.length)
    {y : Occ α} (hy : (occGraph t.s).child (t.occAt i) y) :
    ∃ j, t.graph.child i j ∧ t.occAt j = y :=
  ((Table.check_iff t).1 h).graph_complete i hy

/-- Both targets agree with their literal definitions (no order hypothesis). -/
theorem Table.targets (t : Table α) (h : t.check = true) (i : Fin t.packets.length) :
    (t.graph.target i ↔ (occGraph t.s).target (t.occAt i)) ∧
      (t.graphSuccess.target i ↔ (occGraphFor t.s t.target).target (t.occAt i)) :=
  ⟨((Table.check_iff t).1 h).target_iff i, ((Table.check_iff t).1 h).success_iff i⟩

/-- Every position pair of every noncoincident state is a root packet. -/
theorem Table.roots (t : Table α) (h : t.check = true) {k : ℕ} {T : List α × List α}
    (hT : t.states[k]? = some T) (hnc : T.1 ≠ T.2) {P Q : ℕ} (hP : P < T.1.length)
    (hQ : Q < T.2.length) : ∃ i, t.occAt i = ⟨T, P, Q, none⟩ := by
  obtain ⟨i, -, hi⟩ := ((Table.check_iff t).1 h).roots hT hnc hP hQ
  exact ⟨i, hi⟩

/-- Hub rows: defined exactly where the literal hub residual is defined. -/
theorem Table.hubs_sound (t : Table α) (h : t.check = true) {r : HubRow} (hr : r ∈ t.hubs) :
    ∃ hub, t.letters[r.hub]? = some hub ∧
      r.bits = (t.factors.filter (·.parent = r.state)).map (t.factorHub · hub) := by
  obtain ⟨-, hub, -, -, hh, hb⟩ := ((Table.check_iff t).1 h).hubs_spec hr
  exact ⟨hub, hh, hb⟩

/-- Hub rows: at most one per `(state, hub)`, each at a noncoincident listed state. -/
theorem Table.hubs_rows (t : Table α) (h : t.check = true) :
    (t.hubs.map fun r => (r.state, r.hub)).Nodup ∧
      ∀ r ∈ t.hubs, ∃ T, t.states[r.state]? = some T ∧ T.1 ≠ T.2 := by
  have hA := (Table.check_iff t).1 h
  refine ⟨hA.hubs_nodup, fun r hr => ?_⟩
  obtain ⟨T, -, hT, hnc, -⟩ := hA.hubs_spec hr
  exact ⟨T, hT, hnc⟩

/-- The range of `occAt` is child-closed in the literal occurrence graph. -/
theorem Table.closed_range (t : Table α) (h : t.check = true) :
    (occGraph t.s).Closed (Set.range t.occAt) :=
  ((Table.check_iff t).1 h).closed_range

/-- **Completeness relative to the root pairs, at the level of `O`**: an
accepted table is exactly the set of literal occurrence pairs reachable in `occGraph` from the
root pairs of its noncoincident states.  `⊆` by `birthOK` and `graph_sound`; `⊇` by
`Table.roots` and `closed_range`.  No order hypothesis and no injectivity. -/
theorem Table.range_eq_reach (t : Table α) (h : t.check = true) :
    Set.range t.occAt = {x | ∃ T ∈ t.states, T.1 ≠ T.2 ∧ ∃ P Q, P < T.1.length ∧
      Q < T.2.length ∧ (occGraph t.s).Reach ⟨T, P, Q, none⟩ x} := by
  have hA := (Table.check_iff t).1 h
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    obtain ⟨r, hr, hreach⟩ := hA.reach_root i
    obtain ⟨T, hT, hnc, hP, hQ, hx⟩ := hA.root_spec r hr
    refine ⟨T, List.mem_of_getElem? hT, hnc, _, _, hP, hQ, ?_⟩
    rw [← hx]
    induction hreach with
    | refl => exact .refl
    | tail _ hbc ih => exact ih.tail (hA.graph_sound hbc)
  · rintro ⟨T, hT, hnc, P, Q, hP, hQ, hreach⟩
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hT
    obtain ⟨r, -, hr⟩ := hA.roots hk hnc hP hQ
    exact hA.closed_range.reach ⟨r, hr⟩ hreach

/-- **Seeds** (`seedsOK`): every normalised seed `([a, b], [b, a])`, `a < b`, is a listed
state. -/
theorem Table.seed_mem (t : Table α) (h : t.check = true) {a b : α} (hab : a < b) :
    ([a, b], [b, a]) ∈ t.states :=
  ((Table.check_iff t).1 h).seed_mem hab

end Order

section Linear

variable [LinearOrder α]

/-- **Checker soundness, field by field**, over a linearly ordered alphabet (the
injectivity conjunct is false for an arbitrary `LT`). -/
theorem Table.check_sound (t : Table α) (h : t.check = true) :
    (∀ i : Fin t.packets.length, t.decodeAt i.val = some (t.occAt i)) ∧
    Function.Injective t.occAt ∧
    (∀ i, (t.occAt i).Valid t.s) ∧
    (∀ i : Fin t.packets.length, (t.stars.getD i.val []).map t.decodeEntry =
        (occStar t.s (t.occAt i)).map fun r => (r.1, r.2.1, some r.2.2)) ∧
    (∀ i : Fin t.packets.length,
        (t.packets[i]).topAddr = (t.occAt i).topAddr t.s ∧
        (t.packets[i]).botAddr = (t.occAt i).botAddr t.s ∧
        (t.occAt i).block.1[(t.occAt i).top]? = some (t.packets[i]).letters.1 ∧
        (t.occAt i).block.2[(t.occAt i).bot]? = some (t.packets[i]).letters.2 ∧
        (t.packets[i]).residual = t.letters.map (t.occAt i).residual ∧
        ((t.packets[i]).interior = true ↔ (t.occAt i).Interior) ∧
        ((t.packets[i]).success = true ↔ (t.occAt i).SuccessFor t.target)) ∧
    (∀ i : Fin t.packets.length, ∃ r : Fin t.packets.length,
        (t.packets[r]).factor = none ∧ t.graph.Reach r i) := by
  have hA := (Table.check_iff t).1 h
  exact ⟨hA.decodeAt_eq, hA.occAt_injective, fun i => (hA.fields i).1, hA.star_eq,
    fun i => (hA.fields i).2, hA.reach_root⟩

/-- **What an accepted table is**: `occAt` is an isomorphism of the packet graph onto the
induced subgraph of the literal occurrence graph on the child-closed set `Set.range t.occAt`,
both targets included. -/
theorem Table.iso (t : Table α) (h : t.check = true) :
    Function.Injective t.occAt ∧
      (∀ i j, t.graph.child i j ↔ occChild t.s (t.occAt i) (t.occAt j)) ∧
      (∀ i, t.graph.target i ↔ (t.occAt i).Coincident) ∧
      (∀ i, t.graphSuccess.target i ↔ (t.occAt i).SuccessFor t.target) ∧
      (occGraph t.s).Closed (Set.range t.occAt) := by
  have hA := (Table.check_iff t).1 h
  refine ⟨hA.occAt_injective, fun i j => ⟨hA.graph_sound, fun hij => ?_⟩, hA.target_iff,
    hA.success_iff, hA.closed_range⟩
  obtain ⟨j', hj', hjj⟩ := hA.graph_complete i hij
  rwa [hA.occAt_injective hjj] at hj'

/-- **Seeds in both orientations**: every seed `(ab, ba)` of `Psc.Descendants.seeds` is a listed
state or the swap of one. -/
theorem Table.seeds_listed (t : Table α) (h : t.check = true) {T : List α × List α}
    (hT : T ∈ seeds) : T ∈ t.states ∨ T.swap ∈ t.states := by
  obtain ⟨a, b, hab, rfl⟩ := mem_seeds.1 hT
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · exact Or.inl (Table.seed_mem t h hlt)
  · exact Or.inr (Table.seed_mem t h hlt)

/-- **The listed states contain the seed closure, up to orientation** (`seedsOK` and the child
closure of `factorsOK`): every vertex of the balanced-pair automaton `bpaStatesNC` (the states
reachable from the seeds `(ab, ba)` through noncoincident children) is a listed state or the
swap of one.  The converse is not implied by the checker (`fibExtra_accepted`). -/
theorem Table.bpaStatesNC_listed (t : Table α) (h : t.check = true) :
    bpaStatesNC t.s ⊆ {T | T ∈ t.states ∨ T.swap ∈ t.states} := by
  have hA := (Table.check_iff t).1 h
  refine bpaStatesNC_subset _ (fun T hT => Table.seeds_listed t h hT) ?_
  rintro T (hT | hT) hne U hU
  · exact hA.child_listed hT hne hU
  · have hU' : U.swap ∈ red (subst t.s T.swap.1) (subst t.s T.swap.2) := by
      show U.swap ∈ red (subst t.s T.2) (subst t.s T.1)
      rw [red_swap]
      exact List.mem_map_of_mem hU
    rcases hA.child_listed hT (fun h' => hne h'.symm) hU' with h' | h'
    · exact Or.inr h'
    · rw [Prod.swap_swap] at h'
      exact Or.inl h'

end Linear

end Headline

/-- The repaired generality applies to a `Fin 3` table elaborated with the default `Fin`
instances, as a generated data module is. -/
theorem fin3_occAt_injective (t : Table (Fin 3)) (h : t.check = true) :
    Function.Injective t.occAt :=
  (Table.check_sound t h).2.1

/-! ### The clause vector -/

/-- The eleven clauses of `Table.check`, in order: letters, states, seeds, factors, keys,
roots, births, star count, rows, stars, hubs.  A control states its full clause vector, so the
layer at which it is refused is part of the statement. -/
def Table.clauses [Fintype α] [LT α] [DecidableLT α] (t : Table α) : List Bool :=
  [t.lettersOK, t.statesOK, t.seedsOK, t.factorsOK, t.keysOK, t.rootsOK, t.birthOK,
    decide (t.stars.length = t.packets.length), t.packets.all t.packetOK,
    (t.packets.zip t.stars).all (fun ps => t.starOK ps.1 ps.2), t.hubsOK]

theorem Table.check_eq_clauses [Fintype α] [LT α] [DecidableLT α] (t : Table α) :
    t.check = t.clauses.all id := by
  simp [Table.check, Table.clauses, Bool.and_assoc]

/-! ### Calibration: a Fibonacci table, accepted, and mutation controls -/

/-- Fibonacci `0 ↦ 01, 1 ↦ 0` (`Psc.Descendants.fibSubst`), any diagonal as target: the two
normalised states `(01, 10)` and `(0, 0)`, the two factor rows of `(01, 10)`, 14 packets
(4 roots), 15 child entries and 12 split entries.  Written by a scratch generator with the
Mojo conventions (roots first, breadth-first in id order, first incoming edge as birth); the
Mojo exporter is alphabet-3 only. -/
def fibTable : Table (Fin 2) where
  letters := [0, 1]
  s := fibSubst
  target := none
  states := [([0, 1], [1, 0]), ([0], [0])]
  factors := [⟨0, 0, 1, true, 0, 1, 3⟩, ⟨0, 1, 0, false, 1, 3, 3⟩]
  packets := [⟨0, true, 0, 0, none, none, none, (0, 1), [0, 0], false, false, none⟩,
    ⟨0, true, 0, 1, none, none, none, (0, 0), [0, -1], false, false, none⟩,
    ⟨0, true, 1, 0, none, none, none, (1, 1), [1, 0], false, false, none⟩,
    ⟨0, true, 1, 1, none, none, none, (1, 0), [1, -1], false, false, none⟩,
    ⟨1, true, 0, 0, some 0, some (0, 0, 0, 0), some (0, 0, 0, 0), (0, 0), [0, 0], false, false,
      some (0, 0, 0)⟩,
    ⟨0, false, 0, 0, some 1, some (0, 1, 1, 0), some (1, 0, 1, 0), (1, 0), [0, 0], true, false,
      some (1, 1, 0)⟩,
    ⟨0, false, 0, 1, some 1, some (0, 1, 1, 0), some (1, 1, 2, 1), (1, 1), [-1, 0], false, false,
      some (1, 1, 1)⟩,
    ⟨0, false, 1, 0, some 1, some (1, 0, 2, 1), some (1, 0, 1, 0), (0, 0), [0, 1], false, false,
      some (3, 0, 0)⟩,
    ⟨0, false, 1, 1, some 1, some (1, 0, 2, 1), some (1, 1, 2, 1), (0, 1), [-1, 1], false, false,
      some (3, 0, 1)⟩,
    ⟨1, false, 0, 0, some 0, some (0, 0, 0, 0), some (0, 0, 0, 0), (0, 0), [0, 0], false, false,
      some (5, 0, 0)⟩,
    ⟨0, true, 0, 0, some 1, some (1, 0, 1, 0), some (0, 1, 1, 0), (0, 1), [0, 0], true, false,
      some (7, 0, 1)⟩,
    ⟨0, true, 1, 0, some 1, some (1, 1, 2, 1), some (0, 1, 1, 0), (1, 1), [1, 0], false, false,
      some (7, 1, 1)⟩,
    ⟨0, true, 0, 1, some 1, some (1, 0, 1, 0), some (1, 0, 2, 1), (0, 0), [0, -1], false, false,
      some (8, 0, 0)⟩,
    ⟨0, true, 1, 1, some 1, some (1, 1, 2, 1), some (1, 0, 2, 1), (1, 0), [1, -1], false, false,
      some (8, 1, 0)⟩]
  stars := [[.child 0 0 4, .split 1 0 1 0],
    [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 5, .child 1 1 6],
    [.split 0 0 1 0],
    [.child 0 0 7, .child 0 1 8],
    [],
    [.child 0 0 9, .split 0 1 0 1],
    [.split 0 0 0 1],
    [.split 0 0 1 0, .child 0 1 10, .split 1 0 1 0, .child 1 1 11],
    [.child 0 0 12, .child 1 0 13],
    [],
    [.child 0 0 4, .split 1 0 1 0],
    [.split 0 0 1 0],
    [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 5, .child 1 1 6],
    [.child 0 0 7, .child 0 1 8]]
  keyOrder := [5, 6, 7, 8, 0, 10, 1, 12, 2, 11, 3, 13, 9, 4]
  hubs := [⟨0, 0, [none, some true]⟩, ⟨0, 1, [none, some true]⟩]

/-- The Fibonacci table is accepted (one kernel evaluation). -/
theorem fib_accepted : fibTable.check = true := by decide +kernel

/-- Calibration of the decoding on two rows: packet 2 is the literal dead end `fibDead` of
`Psc.OccurrenceGraph` (its star is one split, as `fibDead_star` says), and packet 5 is the
strictly interior reading at `(0, 0)` of the block `(10, 01)`, born as ordinal 1 of the root
block `(01, 10)` (its exported `interior` bit is `true`). -/
theorem fib_rows :
    fibTable.decodeAt 2 = some fibDead ∧ fibTable.stars.getD 2 [] = [.split 0 0 1 0] ∧
      fibTable.decodeAt 5 = some ⟨([1, 0], [0, 1]), 0, 0, some ⟨([0, 1], [1, 0]), 1⟩⟩ ∧
      (fibTable.packets[5]?.map (·.interior)) = some true := by
  decide

/-- The seed closure of Fibonacci is listed (`Table.bpaStatesNC_listed` on `fibTable`). -/
theorem fib_seed_closure :
    bpaStatesNC fibSubst ⊆ {T | T ∈ fibTable.states ∨ T.swap ∈ fibTable.states} :=
  Table.bpaStatesNC_listed fibTable fib_accepted

/-! #### Mutation controls on `fibTable`

Each control states the full clause vector of the mutated table (`Table.clauses`, in the order
letters, states, seeds, factors, keys, roots, births, star count, rows, stars, hubs), so the
statement records every layer that refuses it, and `Table.check = false`. -/

/-- A dropped split descendant (the split of packet 0) is refused by the star clause only. -/
theorem fib_dropped_split :
    let t : Table (Fin 2) := { fibTable with stars := fibTable.stars.set 0 [.child 0 0 4] }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, false, true] := by
  decide +kernel

/-- A dropped child edge (packet 10's edge to packet 4, not a birth edge) is refused by the star
clause only. -/
theorem fib_dropped_child :
    let t : Table (Fin 2) := { fibTable with stars := fibTable.stars.set 10 [.split 1 0 1 0] }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, false, true] := by
  decide +kernel

/-- A wrong split account (the two ordinals of a split exchanged) is refused by the star
clause only. -/
theorem fib_wrong_split :
    let t : Table (Fin 2) :=
      { fibTable with stars := fibTable.stars.set 0 [.child 0 0 4, .split 1 0 0 1] }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, false, true] := by
  decide +kernel

/-- An out-of-range destination is refused, never reduced modulo the row count (`18 ≡ 4`
mod 14): the star clause only. -/
theorem fib_bad_destination :
    let t : Table (Fin 2) :=
      { fibTable with stars := fibTable.stars.set 10 [.child 0 0 18, .split 1 0 1 0] }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, false, true] := by
  decide +kernel

/-- A truncated table (the last row, its star and its key dropped) is refused: an earlier star
names the missing row. -/
theorem fib_truncated :
    let t : Table (Fin 2) :=
      { fibTable with packets := fibTable.packets.take 13, stars := fibTable.stars.take 13,
                      keyOrder := fibTable.keyOrder.erase 13 }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, false, true] := by
  decide +kernel

/-- A side-swapped row (packet 6 with the other orientation) is refused by the key order, by
its row clause (letters, residual, addresses) and by the parent's star. -/
theorem fib_side_swapped :
    let t : Table (Fin 2) :=
      { fibTable with packets := fibTable.packets.modify 6 fun p => { p with sign := true } }
    t.check = false ∧
      t.clauses = [true, true, true, true, false, true, true, true, false, false, true] := by
  decide +kernel

/-- A wrong residual is refused by the row clause only. -/
theorem fib_wrong_residual :
    let t : Table (Fin 2) :=
      { fibTable with packets := fibTable.packets.modify 7 fun p => { p with residual := [0, 0] } }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, false, true, true] := by
  decide +kernel

/-- A wrong interior bit is refused by the row clause only. -/
theorem fib_wrong_interior :
    let t : Table (Fin 2) :=
      { fibTable with packets := fibTable.packets.modify 7 fun p => { p with interior := true } }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, false, true, true] := by
  decide +kernel

/-- A wrong global position in an address is refused by the row clause only. -/
theorem fib_wrong_global :
    let t : Table (Fin 2) :=
      { fibTable with packets := fibTable.packets.modify 5 fun p =>
          { p with topAddr := p.topAddr.map fun (a, b, _, d) => (a, b, 2, d) } }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, false, true, true] := by
  decide +kernel

/-- A wrong block end in a factor row is refused by the factor clause only. -/
theorem fib_wrong_stop :
    let t : Table (Fin 2) :=
      { fibTable with factors := fibTable.factors.modify 0 fun f => { f with stop := 2 } }
    t.check = false ∧
      t.clauses = [true, true, true, false, true, true, true, true, true, true, true] := by
  decide +kernel

/-- A wrong ordinal in a factor row is refused by the factor clause, and the rows born through
it then carry the wrong birth record (row and star clauses). -/
theorem fib_wrong_ordinal :
    let t : Table (Fin 2) :=
      { fibTable with factors := fibTable.factors.modify 1 fun f => { f with ordinal := 0 } }
    t.check = false ∧
      t.clauses = [true, true, true, false, true, true, true, true, false, false, true] := by
  decide +kernel

/-- A duplicated row (a copy of packet 5, its star, and a key-order entry) is refused by the
key order and by the births; its row and star clauses are literal.  `fib_duplicate_isolated`
isolates the key clause. -/
theorem fib_duplicate_key :
    let t : Table (Fin 2) :=
      { fibTable with packets := fibTable.packets ++ (fibTable.packets.drop 5).take 1,
                      stars := fibTable.stars ++ [fibTable.stars.getD 5 []],
                      keyOrder := fibTable.keyOrder ++ [14] }
    t.check = false ∧
      t.clauses = [true, true, true, true, false, true, false, true, true, true, true] := by
  decide +kernel

/-- An undefined hub bit coerced to `0` is refused by the hub clause only. -/
theorem fib_hub_coerced :
    let t : Table (Fin 2) :=
      { fibTable with hubs := fibTable.hubs.modify 0 fun r =>
          { r with bits := r.bits.map fun b => some (b.getD false) } }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, true, false] := by
  decide +kernel

/-- `none` at a defined hub slot is refused by the hub clause only. -/
theorem fib_hub_undefined :
    let t : Table (Fin 2) :=
      { fibTable with hubs := fibTable.hubs.modify 0 fun r => { r with bits := [none, none] } }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, true, false] := by
  decide +kernel

/-- A hub row for a state that does not exist (index 9 of 2), with the empty bit list that
the filter over its (absent) factor rows would give, is refused by the hub clause only. -/
theorem fib_hub_state_oob :
    let t : Table (Fin 2) := { fibTable with hubs := fibTable.hubs ++ [⟨9, 0, []⟩] }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, true, false] := by
  decide +kernel

/-- A hub row for the coincidence state `(0, 0)` (no factor rows, so the bit list `[]` is
literal) is refused by the hub clause only. -/
theorem fib_hub_coincident :
    let t : Table (Fin 2) := { fibTable with hubs := fibTable.hubs ++ [⟨1, 0, []⟩] }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, true, false] := by
  decide +kernel

/-- A repeated hub row (a literal copy of the first) is refused by the hub clause only. -/
theorem fib_hub_duplicate :
    let t : Table (Fin 2) := { fibTable with hubs := fibTable.hubs ++ fibTable.hubs.take 1 }
    t.check = false ∧
      t.clauses = [true, true, true, true, true, true, true, true, true, true, false] := by
  decide +kernel

/-- `fibTable` with a duplicated row: row 4 (`(0, 0)` born as ordinal 0 of the root block)
copied as row 14, born from row 10, whose `(0, 0)` child entry is repointed to row 14; row
14's star is the literal empty star of a coincidence. -/
def fibDuplicate : Table (Fin 2) :=
  { fibTable with
    packets := fibTable.packets ++
      [⟨1, true, 0, 0, some 0, some (0, 0, 0, 0), some (0, 0, 0, 0), (0, 0), [0, 0], false, false,
        some (10, 0, 0)⟩],
    stars := fibTable.stars.set 10 [.child 0 0 14, .split 1 0 1 0] ++ [[]],
    keyOrder := fibTable.keyOrder ++ [14] }

/-- **The duplicated row is refused by the key clause alone**: every other clause, the star
and birth clauses included, accepts it. -/
theorem fib_duplicate_isolated :
    fibDuplicate.check = false ∧
      fibDuplicate.clauses = [true, true, true, true, false, true, true, true, true, true, true] :=
  by decide +kernel

/-- Rows 4 and 14 of `fibDuplicate` decode to one occurrence pair. -/
theorem fib_duplicate_collide :
    fibDuplicate.decodeAt 4 = fibDuplicate.decodeAt 14 ∧ (fibDuplicate.decodeAt 4).isSome = true :=
  by decide +kernel

/-- **Without `keysOK`, `occAt` is not injective**: on `fibDuplicate`, which passes the other
ten clauses, rows 4 and 14 have the same occurrence pair. -/
theorem fib_duplicate_not_injective : ¬ Function.Injective fibDuplicate.occAt := by
  intro h
  have h414 : fibDuplicate.occAt ⟨4, by decide⟩ = fibDuplicate.occAt ⟨14, by decide⟩ := by
    unfold Table.occAt
    rw [fib_duplicate_collide.1]
  exact absurd (congrArg Fin.val (h h414)) (by decide)

/-- **`seedsOK` is not implied by the other ten clauses**: the empty Fibonacci table passes
all of them and is refused by the seed clause alone. -/
theorem fib_no_seed :
    let t : Table (Fin 2) :=
      { letters := [0, 1], s := fibSubst, target := none, states := [], factors := [],
        packets := [], stars := [], keyOrder := [], hubs := [] }
    t.check = false ∧
      t.clauses = [true, true, false, true, true, true, true, true, true, true, true] := by
  decide +kernel

/-! #### The listed states may exceed the seed closure

`Table.bpaStatesNC_listed` is one inclusion only.  `fibExtra` is `fibTable` with the
irreducible normalised block `(001, 100)` listed as an extra state (with its three factor
rows, its nine root rows and their descendants, 32 rows in all): accepted, although
`(001, 100)` is not reached from the seeds in either orientation (`fib_bpaStatesNC`).  So an
accepted table says nothing about which of its states are seed-reachable; that converse would
need a further clause (the listed states are exactly the normalised `bpaStatesNC`), not
written here. -/

/-- `fibTable` with the extra state `(001, 100)` (generated as `fibTable`). -/
def fibExtra : Table (Fin 2) where
  letters := [0, 1]
  s := fibSubst
  target := none
  states := [([0, 1], [1, 0]), ([0, 0, 1], [1, 0, 0]), ([0], [0])]
  factors := [⟨0, 0, 2, true, 0, 1, 3⟩, ⟨0, 1, 0, false, 1, 3, 3⟩, ⟨1, 0, 2, true, 0, 1, 5⟩,
    ⟨1, 1, 0, false, 1, 3, 5⟩, ⟨1, 2, 0, false, 3, 5, 5⟩]
  packets := [⟨0, true, 0, 0, none, none, none, (0, 1), [0, 0], false, false, none⟩,
    ⟨0, true, 0, 1, none, none, none, (0, 0), [0, -1], false, false, none⟩,
    ⟨0, true, 1, 0, none, none, none, (1, 1), [1, 0], false, false, none⟩,
    ⟨0, true, 1, 1, none, none, none, (1, 0), [1, -1], false, false, none⟩,
    ⟨1, true, 0, 0, none, none, none, (0, 1), [0, 0], false, false, none⟩,
    ⟨1, true, 0, 1, none, none, none, (0, 0), [0, -1], false, false, none⟩,
    ⟨1, true, 0, 2, none, none, none, (0, 0), [-1, -1], false, false, none⟩,
    ⟨1, true, 1, 0, none, none, none, (0, 1), [1, 0], false, false, none⟩,
    ⟨1, true, 1, 1, none, none, none, (0, 0), [1, -1], false, false, none⟩,
    ⟨1, true, 1, 2, none, none, none, (0, 0), [0, -1], false, false, none⟩,
    ⟨1, true, 2, 0, none, none, none, (1, 1), [2, 0], false, false, none⟩,
    ⟨1, true, 2, 1, none, none, none, (1, 0), [2, -1], false, false, none⟩,
    ⟨1, true, 2, 2, none, none, none, (1, 0), [1, -1], false, false, none⟩,
    ⟨2, true, 0, 0, some 0, some (0, 0, 0, 0), some (0, 0, 0, 0), (0, 0), [0, 0], false, false,
      some (0, 0, 0)⟩,
    ⟨0, false, 0, 0, some 1, some (0, 1, 1, 0), some (1, 0, 1, 0), (1, 0), [0, 0], true, false,
      some (1, 1, 0)⟩,
    ⟨0, false, 0, 1, some 1, some (0, 1, 1, 0), some (1, 1, 2, 1), (1, 1), [-1, 0], false, false,
      some (1, 1, 1)⟩,
    ⟨0, false, 1, 0, some 1, some (1, 0, 2, 1), some (1, 0, 1, 0), (0, 0), [0, 1], false, false,
      some (3, 0, 0)⟩,
    ⟨0, false, 1, 1, some 1, some (1, 0, 2, 1), some (1, 1, 2, 1), (0, 1), [-1, 1], false, false,
      some (3, 0, 1)⟩,
    ⟨2, true, 0, 0, some 2, some (0, 0, 0, 0), some (0, 0, 0, 0), (0, 0), [0, 0], false, false,
      some (4, 0, 0)⟩,
    ⟨0, false, 0, 0, some 3, some (0, 1, 1, 0), some (1, 0, 1, 0), (1, 0), [0, 0], true, false,
      some (5, 1, 0)⟩,
    ⟨0, false, 0, 1, some 3, some (0, 1, 1, 0), some (1, 1, 2, 1), (1, 1), [-1, 0], false, false,
      some (5, 1, 1)⟩,
    ⟨0, false, 1, 0, some 3, some (1, 0, 2, 1), some (1, 0, 1, 0), (0, 0), [0, 1], false, false,
      some (8, 0, 0)⟩,
    ⟨0, false, 1, 1, some 3, some (1, 0, 2, 1), some (1, 1, 2, 1), (0, 1), [-1, 1], false, false,
      some (8, 0, 1)⟩,
    ⟨0, false, 0, 0, some 4, some (1, 1, 3, 0), some (2, 0, 3, 0), (1, 0), [0, 0], true, false,
      some (9, 1, 0)⟩,
    ⟨0, false, 0, 1, some 4, some (1, 1, 3, 0), some (2, 1, 4, 1), (1, 1), [-1, 0], false, false,
      some (9, 1, 1)⟩,
    ⟨0, false, 1, 0, some 4, some (2, 0, 4, 1), some (2, 0, 3, 0), (0, 0), [0, 1], false, false,
      some (12, 0, 0)⟩,
    ⟨0, false, 1, 1, some 4, some (2, 0, 4, 1), some (2, 1, 4, 1), (0, 1), [-1, 1], false, false,
      some (12, 0, 1)⟩,
    ⟨2, false, 0, 0, some 0, some (0, 0, 0, 0), some (0, 0, 0, 0), (0, 0), [0, 0], false, false,
      some (14, 0, 0)⟩,
    ⟨0, true, 0, 0, some 1, some (1, 0, 1, 0), some (0, 1, 1, 0), (0, 1), [0, 0], true, false,
      some (16, 0, 1)⟩,
    ⟨0, true, 1, 0, some 1, some (1, 1, 2, 1), some (0, 1, 1, 0), (1, 1), [1, 0], false, false,
      some (16, 1, 1)⟩,
    ⟨0, true, 0, 1, some 1, some (1, 0, 1, 0), some (1, 0, 2, 1), (0, 0), [0, -1], false, false,
      some (17, 0, 0)⟩,
    ⟨0, true, 1, 1, some 1, some (1, 1, 2, 1), some (1, 0, 2, 1), (1, 0), [1, -1], false, false,
      some (17, 1, 0)⟩]
  stars := [[.child 0 0 13, .split 1 0 1 0],
    [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 14, .child 1 1 15],
    [.split 0 0 1 0],
    [.child 0 0 16, .child 0 1 17],
    [.child 0 0 18, .split 1 0 1 0],
    [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 19, .child 1 1 20],
    [.split 0 0 0 2, .split 0 1 0 2, .split 1 0 1 2, .split 1 1 1 2],
    [.split 0 0 1 0, .split 1 0 2 0],
    [.child 0 0 21, .child 0 1 22, .split 1 0 2 1, .split 1 1 2 1],
    [.split 0 0 1 2, .split 0 1 1 2, .child 1 0 23, .child 1 1 24],
    [.split 0 0 2 0],
    [.split 0 0 2 1, .split 0 1 2 1],
    [.child 0 0 25, .child 0 1 26],
    [],
    [.child 0 0 27, .split 0 1 0 1],
    [.split 0 0 0 1],
    [.split 0 0 1 0, .child 0 1 28, .split 1 0 1 0, .child 1 1 29],
    [.child 0 0 30, .child 1 0 31],
    [],
    [.child 0 0 27, .split 0 1 0 1],
    [.split 0 0 0 1],
    [.split 0 0 1 0, .child 0 1 28, .split 1 0 1 0, .child 1 1 29],
    [.child 0 0 30, .child 1 0 31],
    [.child 0 0 27, .split 0 1 0 1],
    [.split 0 0 0 1],
    [.split 0 0 1 0, .child 0 1 28, .split 1 0 1 0, .child 1 1 29],
    [.child 0 0 30, .child 1 0 31],
    [],
    [.child 0 0 13, .split 1 0 1 0],
    [.split 0 0 1 0],
    [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 14, .child 1 1 15],
    [.child 0 0 16, .child 0 1 17]]
  keyOrder := [14, 19, 23, 15, 20, 24, 16, 21, 25, 17, 22, 26, 0, 28, 1, 30, 2, 29, 3, 31, 4, 5,
    6, 7, 8, 9, 10, 11, 12, 27, 13, 18]
  hubs := [⟨0, 0, [none, some true]⟩, ⟨0, 1, [none, some true]⟩,
    ⟨1, 0, [none, some true, some true]⟩, ⟨1, 1, [none, some true, some true]⟩]

/-- The table with the extra, unreached state is accepted. -/
theorem fibExtra_accepted : fibExtra.check = true := by decide +kernel

/-- The extra state is listed and is not a vertex of the balanced-pair automaton, in either
orientation. -/
theorem fibExtra_state_unreached :
    ([0, 0, 1], [1, 0, 0]) ∈ fibExtra.states ∧
      ([0, 0, 1], [1, 0, 0]) ∉ bpaStatesNC fibSubst ∧
      ([1, 0, 0], [0, 0, 1]) ∉ bpaStatesNC fibSubst := by
  rw [fib_bpaStatesNC]
  decide

/-- **The birth need not be the first incoming edge**: row 27 of `fibExtra` (the coincidence
`(0, 0)` in the swapped orientation) has incoming edges from rows 14, 19 and 23; with its
birth moved from `(14, 0, 0)` to `(19, 0, 0)` the table is still accepted. -/
theorem fibExtra_birth_not_first :
    let t : Table (Fin 2) :=
      { fibExtra with
        packets := fibExtra.packets.modify 27 fun p => { p with birth := some (19, 0, 0) } }
    t.check = true := by
  decide +kernel

/-! #### A forged row outside the reachable set

The mirror keys `(state 0, +, P, Q, factor 3)` are absent from `fibExtra`: factor row 3 is
ordinal 1 of the extra state `(001, 100)`, and the listed rows through it read the parent in
the listed orientation.  `fibExtraForged b` adds the row `(0, +, 0, 0, factor 3)`, which reads
`(01, 10)` at `(0, 0)` born as ordinal 1 of the mirrored parent `(100, 001)`, with its literal
fields, its literal star, a correct key order and the birth record `b`. -/

/-- The occurrence pair of the forged row. -/
def forgedPair : Occ (Fin 2) := ⟨([0, 1], [1, 0]), 0, 0, some ⟨([1, 0, 0], [0, 0, 1]), 1⟩⟩

/-- `fibExtra` with the forged row 32 and the birth record `b`. -/
def fibExtraForged (b : Option (ℕ × ℕ × ℕ)) : Table (Fin 2) :=
  { fibExtra with
    packets := fibExtra.packets ++
      [⟨0, true, 0, 0, some 3, some (1, 0, 1, 0), some (0, 1, 1, 0), (0, 1), [0, 0], true, false,
        b⟩],
    stars := fibExtra.stars ++ [[.child 0 0 13, .split 1 0 1 0]],
    keyOrder := [14, 19, 23, 15, 20, 24, 16, 21, 25, 17, 22, 26, 0, 28, 32, 1, 30, 2, 29, 3, 31,
      4, 5, 6, 7, 8, 9, 10, 11, 12, 27, 13, 18] }

/-- The forged row decodes to `forgedPair`, a valid occurrence pair, and `forgedPair` is not the
occurrence pair of any row of the accepted table `fibExtra`. -/
theorem fibExtra_forged_outside :
    (fibExtraForged none).decodeAt 32 = some forgedPair ∧ forgedPair.Valid fibSubst ∧
      ∀ i, fibExtra.occAt i ≠ forgedPair := by
  decide +kernel

/-- **The forged pair is not reachable** in `occGraph fibSubst` from any root pair of a
noncoincident listed state of `fibExtra` (`Table.range_eq_reach` and
`fibExtra_forged_outside`). -/
theorem fibExtra_forged_not_reached :
    ¬ ∃ T ∈ fibExtra.states, T.1 ≠ T.2 ∧ ∃ P Q, P < T.1.length ∧ Q < T.2.length ∧
      (occGraph fibSubst).Reach ⟨T, P, Q, none⟩ forgedPair := by
  intro hx
  have hmem : forgedPair ∈ Set.range fibExtra.occAt := by
    rw [Table.range_eq_reach fibExtra fibExtra_accepted]
    exact hx
  obtain ⟨i, hi⟩ := hmem
  exact fibExtra_forged_outside.2.2 i hi

/-- **The forged unreachable row is refused by the birth clause alone**, with no birth, with
a birth edge that is not in the source star, and with a birth from a later index: every other
clause, the row and star clauses included, accepts it. -/
theorem fibExtra_forged_unreachable :
    ∀ b ∈ [none, some (0, 0, 0), some (33, 0, 0)], (fibExtraForged b).check = false ∧
      (fibExtraForged b).clauses =
        [true, true, true, true, true, true, false, true, true, true, true] := by
  decide +kernel

/-! ### The order hypothesis is needed

`EmptyOrderLetter` is a two-letter alphabet whose `<` is empty, so `isNormal` accepts both
orientations of every pair.  `weird` is Fibonacci `a ↦ ab, b ↦ a` over it, listing the seed
`(ab, ba)` and its swap `(ba, ab)` as two states (and `(a, a)`), with 4 factor rows and 19
rows: it passes all eleven clauses, and rows 9 (`(state 1, +, 0, 0, factor 1)`) and 18
(`(state 0, -, 0, 0, factor 3)`) have distinct keys and decode to one occurrence pair, so
`occAt` is not injective.  This is why `Table.check_sound`, `Table.iso` and the injectivity
lemmas assume `[LinearOrder α]`.  The same rows over `Fin 2`, with its linear order, are
refused by the state and factor clauses (`weirdFin_refused`). -/

/-- A two-letter alphabet, to be given the empty order. -/
inductive EmptyOrderLetter
  | a
  | b
  deriving DecidableEq, Repr

instance : Fintype EmptyOrderLetter := ⟨{.a, .b}, by intro x; cases x <;> decide⟩

/-- The empty order: no letter is smaller than another. -/
instance : LT EmptyOrderLetter := ⟨fun _ _ => False⟩

instance : DecidableRel (α := EmptyOrderLetter) (· < ·) := fun _ _ => isFalse id

/-- Fibonacci `a ↦ ab, b ↦ a` on `EmptyOrderLetter`. -/
def weirdS : EmptyOrderLetter → List EmptyOrderLetter
  | .a => [.a, .b]
  | .b => [.a]

/-- Fibonacci over `EmptyOrderLetter`, with both orientations of the seed listed as states. -/
def weird : Table EmptyOrderLetter where
  letters := [.a, .b]
  s := weirdS
  target := none
  states := [([.a, .b], [.b, .a]), ([.b, .a], [.a, .b]), ([.a], [.a])]
  factors := [⟨0, 0, 2, true, 0, 1, 3⟩, ⟨0, 1, 1, true, 1, 3, 3⟩, ⟨1, 0, 2, true, 0, 1, 3⟩,
    ⟨1, 1, 0, true, 1, 3, 3⟩]
  packets := [⟨0, true, 0, 0, none, none, none, (.a, .b), [0, 0], false, false, none⟩,
    ⟨0, true, 0, 1, none, none, none, (.a, .a), [0, -1], false, false, none⟩,
    ⟨0, true, 1, 0, none, none, none, (.b, .b), [1, 0], false, false, none⟩,
    ⟨0, true, 1, 1, none, none, none, (.b, .a), [1, -1], false, false, none⟩,
    ⟨1, true, 0, 0, none, none, none, (.b, .a), [0, 0], false, false, none⟩,
    ⟨1, true, 0, 1, none, none, none, (.b, .b), [-1, 0], false, false, none⟩,
    ⟨1, true, 1, 0, none, none, none, (.a, .a), [0, 1], false, false, none⟩,
    ⟨1, true, 1, 1, none, none, none, (.a, .b), [-1, 1], false, false, none⟩,
    ⟨2, true, 0, 0, some 0, some (0, 0, 0, 0), some (0, 0, 0, 0), (.a, .a), [0, 0], false, false,
      some (0, 0, 0)⟩,
    ⟨1, true, 0, 0, some 1, some (0, 1, 1, 0), some (1, 0, 1, 0), (.b, .a), [0, 0], true, false,
      some (1, 1, 0)⟩,
    ⟨1, true, 0, 1, some 1, some (0, 1, 1, 0), some (1, 1, 2, 1), (.b, .b), [-1, 0], false, false,
      some (1, 1, 1)⟩,
    ⟨1, true, 1, 0, some 1, some (1, 0, 2, 1), some (1, 0, 1, 0), (.a, .a), [0, 1], false, false,
      some (3, 0, 0)⟩,
    ⟨1, true, 1, 1, some 1, some (1, 0, 2, 1), some (1, 1, 2, 1), (.a, .b), [-1, 1], false, false,
      some (3, 0, 1)⟩,
    ⟨2, true, 0, 0, some 2, some (0, 0, 0, 0), some (0, 0, 0, 0), (.a, .a), [0, 0], false, false,
      some (4, 0, 0)⟩,
    ⟨0, true, 0, 0, some 3, some (1, 0, 1, 0), some (0, 1, 1, 0), (.a, .b), [0, 0], true, false,
      some (6, 0, 1)⟩,
    ⟨0, true, 1, 0, some 3, some (1, 1, 2, 1), some (0, 1, 1, 0), (.b, .b), [1, 0], false, false,
      some (6, 1, 1)⟩,
    ⟨0, true, 0, 1, some 3, some (1, 0, 1, 0), some (1, 0, 2, 1), (.a, .a), [0, -1], false, false,
      some (7, 0, 0)⟩,
    ⟨0, true, 1, 1, some 3, some (1, 1, 2, 1), some (1, 0, 2, 1), (.b, .a), [1, -1], false, false,
      some (7, 1, 0)⟩,
    ⟨0, false, 0, 0, some 3, some (0, 1, 1, 0), some (1, 0, 1, 0), (.b, .a), [0, 0], true, false,
      some (16, 1, 0)⟩]
  stars := [[.child 0 0 8, .split 1 0 1 0],
    [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 9, .child 1 1 10],
    [.split 0 0 1 0],
    [.child 0 0 11, .child 0 1 12],
    [.child 0 0 13, .split 0 1 0 1],
    [.split 0 0 0 1],
    [.split 0 0 1 0, .child 0 1 14, .split 1 0 1 0, .child 1 1 15],
    [.child 0 0 16, .child 1 0 17],
    [],
    [.child 0 0 13, .split 0 1 0 1],
    [.split 0 0 0 1],
    [.split 0 0 1 0, .child 0 1 14, .split 1 0 1 0, .child 1 1 15],
    [.child 0 0 16, .child 1 0 17],
    [],
    [.child 0 0 8, .split 1 0 1 0],
    [.split 0 0 1 0],
    [.split 0 0 0 1, .split 0 1 0 1, .child 1 0 18, .child 1 1 10],
    [.child 0 0 11, .child 0 1 12],
    [.child 0 0 13, .split 0 1 0 1]]
  keyOrder := [18, 0, 14, 1, 16, 2, 15, 3, 17, 4, 9, 5, 10, 6, 11, 7, 12, 8, 13]
  hubs := []

/-- **`weird` is accepted** under the empty order. -/
theorem weird_accepted : weird.check = true := by decide +kernel

/-- Rows 9 and 18 of `weird` decode to one occurrence pair, and their key codes differ. -/
theorem weird_rows_collide :
    weird.decodeAt 9 = weird.decodeAt 18 ∧ (weird.decodeAt 9).isSome = true ∧
      (weird.packets[9]?).map weird.keyCode ≠ (weird.packets[18]?).map weird.keyCode := by
  decide +kernel

/-- **Injectivity fails without a linear order**: `weird` is accepted and `occAt` is not
injective on it. -/
theorem weird_not_injective : ¬ Function.Injective weird.occAt := by
  intro h
  have h918 : weird.occAt ⟨9, by decide⟩ = weird.occAt ⟨18, by decide⟩ := by
    unfold Table.occAt
    rw [weird_rows_collide.1]
  exact absurd (congrArg Fin.val (h h918)) (by decide)

/-- The letters of `EmptyOrderLetter` as `Fin 2`. -/
def EmptyOrderLetter.toFin : EmptyOrderLetter → Fin 2
  | .a => 0
  | .b => 1

/-- The rows of `weird` transported to `Fin 2` (Fibonacci `fibSubst`, the order of `Fin 2`). -/
def weirdFin : Table (Fin 2) where
  letters := [0, 1]
  s := fibSubst
  target := none
  states := weird.states.map fun T =>
    (T.1.map EmptyOrderLetter.toFin, T.2.map EmptyOrderLetter.toFin)
  factors := weird.factors
  packets := weird.packets.map fun p =>
    { p with letters := (EmptyOrderLetter.toFin p.letters.1, EmptyOrderLetter.toFin p.letters.2) }
  stars := weird.stars
  keyOrder := weird.keyOrder
  hubs := []

/-- Under the linear order of `Fin 2` the same rows are refused, by the state clause (the swap
`(10, 01)` is not normalised) and the factor clause. -/
theorem weirdFin_refused :
    weirdFin.check = false ∧
      weirdFin.clauses = [true, false, true, false, true, true, true, true, true, true, true] := by
  decide +kernel

end Psc.PacketCertificate

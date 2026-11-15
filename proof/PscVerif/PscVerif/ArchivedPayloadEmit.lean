import PscVerif.ArchivedPayload

/-!
Runtime emission of the exact data checked by the kernel.  The independent
oracle compares every original addressed record and every auxiliary packed
row/search-tree node.  This emitter is an acceptance control, not a proof
of refinement by itself.
-/

namespace Psc.ArchivedPayload

open Psc.OccurrenceTransport Psc.NamedPrefixCompact

def Lookup.emit : Lookup → Nat → Nat → IO Unit
  | .empty, _, _ => pure ()
  | .node key id left right, fixture, path => do
      IO.println s!"lookup {fixture} {path} {key} {id}"
      left.emit fixture (2 * path)
      right.emit fixture (2 * path + 1)

/-- Print the original full-address packet, followed by every packed row
and the complete lookup tree in deterministic preorder. -/
def Packet.emit (p : Packet) : IO Unit := do
  let f := p.fixture.val
  IO.println s!"graph {f} {p.power} {p.boxX} {p.boxY} {p.direction} {p.count} {p.edges} {p.residueRejections} {p.boxRejections} {p.swapped} {p.repeated} {p.maxDepth} {p.sweeps} {p.minimumGap}"
  for a in List.finRange 3 do
    let word := substitution p.fixture a
    let letters := word.foldl (fun text c => text ++ s!" {c.val}") ""
    IO.println s!"image {f} {a.val} {word.length}{letters}"
  for k in List.finRange 15 do
    let d := NamedArchivedDigits.digit p.fixture k
    let prefixVec := parikhZ d.2.before
    IO.println s!"digit {f} {k.val} {d.2.letter.val} {d.1.val} {d.2.index} {prefixVec 0} {prefixVec 1} {prefixVec 2} {NamedArchivedDigits.outerIndex k} {NamedArchivedDigits.localIndex k}"
  for i in [:p.count] do
    let r := p.record i
    let state := p.state i
    let birthParent : Int := (r.birthParent : Int) - 1
    let birthSlot : Int := (r.birthSlot : Int) - 1
    IO.println s!"node {f} {i} {state.top.val} {state.bottom.val} {state.delta 0} {state.delta 1} {state.delta 2} {r.weight} {birthParent} {birthSlot} {r.depth}"
    IO.println s!"row {f} {i} {r.slots.length}"
    for (slot, ordinal) in r.slots.zipIdx do
      let swapped := if slot.swapped then 1 else 0
      IO.println s!"slot {f} {i} {ordinal} {slot.target} {slot.topID} {slot.bottomID} {swapped}"
  for i in [:p.count] do
    IO.println s!"packed {f} {i} {p.raw i}"
  p.index.emit f 1

end Psc.ArchivedPayload

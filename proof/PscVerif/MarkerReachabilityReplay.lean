import PscVerif.PeriodicPartnerMarkerFamily
import PscVerif.PeriodicPartnerMarkerReachability

/-! Evaluate the existing Lean register on every single-track transition of
three literal inputs. Both positions are tested, with the other track empty. -/

open Psc.PeriodicPartnerMarkerReachability

private def iterateEndpoint (f : Nat → Nat) : Nat → Nat → Nat
  | 0, a => a
  | k + 1, a => iterateEndpoint f k (f a)

private def trace (tag : String) (images : List (List Nat)) (a₀ b₀ : Nat) : IO Unit := do
  let σ := fun a => images[a]?.getD []
  let first := fun a => (σ a).head?.getD 3
  let last := fun a => (σ a).getLast?.getD 3
  let mark := fun (j : Int) x y =>
    let k := 6 + (j % 6).toNat
    iterateEndpoint last k x == a₀ && iterateEndpoint first k y == b₀
  let priors := List.range images.length ++ [3]
  for phase in List.range 6 do
    for a in List.range images.length do
      for d in List.range (σ a).length do
        for prior in priors do
          for parity in List.range 2 do
            let prev := if prior == 3 then none else some prior
            let x := advance σ mark phase last ⟨prev, none, parity⟩ ((σ a).take d) []
            let y := advance σ mark phase last ⟨none, prev, parity⟩ [] ((σ a).take d)
            IO.println s!"{tag} {phase} {a} {d} {prior} {parity} {x.topLast.getD 3} {x.bottomLast.getD 3} {x.parity.val} {y.topLast.getD 3} {y.bottomLast.getD 3} {y.parity.val}"

def main : IO Unit := do
  let family := (List.finRange 3).map fun a =>
    (Psc.PeriodicPartnerMarkerFamily.sigma 0 a).map Fin.val
  trace "family" family 0 0
  trace "cycling" [[0, 1], [1, 1, 2], [0, 2, 1]] 1 0
  trace "thue-morse" [[0, 1], [1, 0]] 0 0

#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

(cd "$root/kernel" && pixi run --locked mojo build -I . target_aware_bpa.mojo -o "$work/export")
cd "$root/proof/PscVerif"
lake build +PscVerif.ForwardCarrier +PscVerif.NamedFiniteProductivity

for spec in '021 0' '012 1'; do
    read -r order fixture <<< "$spec"
    packet="$work/Carrier$order.lean"
    "$work/export" --sigma "1/$order/001" --state-cap 20000 --length-cap 40000 \
        --forward-carrier-lean > "$packet.raw"
    {
        echo 'import PscVerif.NamedFiniteProductivity'
        cat "$packet.raw"
        cat <<LEAN

set_option maxRecDepth 2048
set_option maxHeartbeats 0
open Psc.NamedPrefixCompact Psc.Descendants Psc.StrictSystem

theorem checkedCarrier : check (substitution $fixture) carrier = true := by decide +kernel

theorem finiteCarrier : (bpaStatesNC (substitution $fixture)).Finite :=
  finite_of_check checkedCarrier

theorem seedTermination (p : Psc.ArchivedPayload.Packet) (hp : p.Valid)
    (hf : p.fixture = $fixture) {T : Pair} (hT : T ∈ (seeds : Finset Pair)) :
    TerminatesWithCoincidence (substitution p.fixture) T :=
  p.seed_terminates_of_finite_reachable hp hT (hf.symm ▸ finite_from_seed_of_check checkedCarrier hT)

#print axioms finiteCarrier
#print axioms seedTermination
LEAN
    } > "$packet"
    sha256sum "$packet.raw"
    lake env lean "$packet"
done

for budget in '--state-cap 1' '--length-cap 1'; do
    read -r option value <<< "$budget"
    if "$work/export" --sigma 1/012/001 "$option" "$value" \
        --forward-carrier-lean > "$work/capped" 2> "$work/capped-error"; then
        echo "exhausted budget was accepted" >&2
        exit 1
    fi
    test ! -s "$work/capped"
    grep -q 'BPA budget exhausted' "$work/capped-error"
done

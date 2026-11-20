# Homoclinic winding for the even-determinant C4 reduction

The [even-determinant stack argument](c4-even-stack-residue-2026-11-19.md#the-grouped-square-forces-a-homoclinic-winding-on-the-base)
uses a pair whose two tails lift to opposite sheets of a two-sheet cover.
The Lean proof derives odd winding from the phase conditions on those
seams. See the [source decision](c4-homoclinic-winding-stop-go-2026-11-20.md)
for the published covering and cohomology inputs.

## Assumptions and hypotheses

Use the additive circle `ℝ/ℤ`. A homoclinic phase is a continuous phase
path on `ℝ` tending to zero at both infinities. In the grouped square,
write `z_uv(t)` for the phase along the orbit of the group `(u,v)`.
The nonzero grouped entry at `(0,0)` comes from a finite matrix of seam
weights with zero row and column sums. Across the support of each original
row, phase differences tend to zero on the left. Across each original
column, they tend to zero on the right. The phases `z_01` and `z_10` have
the same double at every time and differ by a half-turn at zero.

## Derivation

1. At the positive end of a path tending to zero, choose a point after
   which the path stays in the target of the circle chart at zero. Lift
   the whole real line through `ℝ → ℝ/ℤ`, choosing the chart value at that
   point. On the connected tail the lift agrees with the chart section,
   so it tends to zero. Reflection gives the negative end. Two normalized
   lifts agree where both lie in one real period interval, then agree
   everywhere by uniqueness of lifts.
2. The normalized lift difference at time zero projects to zero, so it
   is an integer. This is the winding. Adding phase paths adds their
   normalized lifts and windings. A continuous real lift tending to zero
   at both ends gives winding zero.
3. The original row and column crossing lemmas give the left limit of
   `z_00 − z_01` and the right limit of `z_00 − z_10`. These two paths have
   the same double. Their real normalized lifts `l` and `r` differ by an
   integer plus a half-turn at zero. Consequently the winding of the
   doubled path is `2(l(0) − r(0))`, which is odd.
4. Doubling a single homoclinic phase doubles its winding. The odd
   winding therefore rules out a continuous half-phase that tends to
   zero on both tails. In the written stack construction the doubled
   phase is the difference of the descended sheet phase along the two
   base orbits.

## Evidence and replay

| Lean endpoint | Statement |
| --- | --- |
| `exists_tailLift_atTop`, `exists_tailLift_atBot`, `IsTailLift.unique` | Existence and uniqueness of normalized real lifts |
| `HomoclinicPhase.winding_add`, `HomoclinicPhase.winding_eq_zero_of_lift` | Additivity and zero winding for a common normalized real lift |
| `HomoclinicPhase.odd_winding_of_deck_switch` | Odd winding for a double with opposite-sheet normalized half-phases |
| `odd_winding_of_grouped_seams` | The existing seam crossing lemmas yield the two required limits |
| `HomoclinicPhase.no_homoclinic_half_of_odd` | An odd winding obstructs a homoclinic half-phase |

The endpoints are in
[`PeriodicPartnerWinding.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerWinding.lean)
and [`PeriodicPartnerWindingSeams.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerWindingSeams.lean).
The winding proof uses the existing cycle and crossing lemmas from
[`PeriodicPartnerSeamCycles.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerSeamCycles.lean).

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

## Controls and remaining obligations

`winding_one_control` projects the real ramp `max 0 (min 1 t)` to the
circle. Its left lift is the ramp and its right lift is the ramp minus
one. The path is zero outside the unit interval and has winding one.
The [period-doubling control](c4-even-stack-residue-2026-11-19.md#negative-controls)
realizes odd winding in a degree-one substitution. Both controls leave
room for a cubic argument using the geometry of the original ternary
hull. The geometric transfer of the seam phase conditions and the cubic
obstruction remain open as Lean obligations. Independent human review is
pending. Universal C4 and PSC remain open.

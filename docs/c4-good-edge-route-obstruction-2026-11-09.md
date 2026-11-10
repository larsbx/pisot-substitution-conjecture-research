# C4: a productive forced overlap without a left-aligned good edge

## Literature and scope

[Sirvent–Solomyak](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/4BC0FD9DBA6ECA027A32568F9E5C1D12/S0008439500017537a.pdf/pure_discrete_spectrum_for_onedimensional_substitution_systems_of_pisot_type.pdf)
and [Akiyama–Lee](https://arxiv.org/abs/1003.2898) study
coincidence via paths of actual overlaps.
[Barge–Diamond](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
supplies the separate notion of a witnessed left-aligned good edge.
Those results do not require a productivity path to visit a specified
good edge. The earlier [forced-overlap controls](c4-forced-overlap-routes-2026-11-04.md)
showed that a visit can make a shortest route longer. Here the question
is whether a literal first physical crossing, with a witnessed good
edge and a complete flat one-step factor row, must reach the
left-aligned good edge at all. Proceed with an exact finite negative control. The proposed
shortcut has weaker hypotheses than the fully strict child-closed
problem in [#461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

## Literal source and physical crossing

Take `sigma = 1/02/002`. Its incidence columns are
`(0,1,0), (1,0,1), (2,0,1)`. The fourth power is positive.
The characteristic polynomial is `x^3 - x^2 - x - 1`, with
no rational root and discriminant -44. Its sole real root
`beta` lies between 1 and 2. The product of the other two roots
is `1/beta`, so the complex pair is inside the unit circle.

Use hub 0. The complementary good pair is `{1,2}), since
both images begin with 0. The prefix map exchanges 0 and 1,
so it never synchronizes the source's first-letter pair.

In the balanced-pair graph, following the first factor twice
from `(01,10)` gives `(102,021)` and then `T=(0210,1002)`.
The two words of `T` occur in `sigma^4(2)` at positions 2 and 0
respectively, with zero-based indexing. Its entire first child row
is the single noncoincident pair `(1002021,0211002)`, so that row
is flat with the hub changing tracks. The next complete row
contains diagonal factors `(0,0)` and `(2,2)`.

Let `ell` be the positive left Perron row, and put
`E = p(top prefix) - p(bottom prefix)`. The second bottom hub
at source index 2 starts at `ell_1 + ell_0`, after the first
top hub completes and before the second top hub starts.
It starts strictly inside the top letter 2 at source index 1,
since `M(e_2-e_1)=e_0` implies `ell_2 > ell_1`.
This is the first negative completed-hub event. The two preceding
prefixes have one hub each, and `E=(0,-1,0)`. The signed hub
completion area is `ell_1-ell_2 < 0`, the sum of the two
bottom-minus-top differences of matched hub start positions.

## Complete graph and shortest witness

Starting from `(2,0,-e_1)`, the exact overlap graph closes
at 54 states and 94 ordered child occurrences. Its aligned
pairs are exactly `00, 22, 01, 10, 02, 20`. Neither orientation
of `{1,2}` appears. The graph uses absorbing diagonals.
Inflating an aligned diagonal only produces aligned diagonals
among actual strict-interior child overlaps, so absorbing them
does not hide a later route to a noncoincident aligned pair.

The first child occurrence is uniquely `(2,0)`. A shortest
path to a diagonal has eight steps, with ordered digit pairs

```text
(2,0), (2,1), (2,0), (1,0), (0,0), (1,0), (2,1), (1,0)
```

The addressed transport of [#467](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/467)
puts the first diagonal along this marked path in parent
`(100202021,020211002)`. Its local interior cut 5 is `Sync_+`.
This depth eight is the minimum for the specified overlap.
The full word pair already has diagonals in its second inflation.

Right alignment behaves differently. The first right-aligned
`{1,2}` occurs at depth seven, at state `(1,2,e_2-e_1)`,
via the digit pairs `(2,0),(2,1),(2,0),(2,0),(2,1),(0,2),(0,2)`.
The images `02` and `002` have common suffix `02`. From
that state, the next digits `(0,1)` give the aligned diagonal
`0/0` at the start of that suffix. The route via
this right alignment also attains depth eight.

## Replay and boundary

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_forced_overlap_routes.mojo)
python -m pytest -q tests/test_c4_forced_overlap_routes_oracle.py
```

The canonical test uses the exact cubic-field overlap graph and the
addressed-newborn checker. The independent oracle constructs every
child from integer prefix vectors, certifies endpoints by incidence
lifting, and replays the complete words to the cut. The graph cap
is 128 states and the independent sign budget is 32 lifts. A capped
graph supplies no absence certificate. The complete graph in this
control establishes that transport through the original left-aligned
good edge can fail even when the crossing is literal and productive. Strict
child closure and uniform productivity in a hypothetical strict flat
component remain separate obligations.

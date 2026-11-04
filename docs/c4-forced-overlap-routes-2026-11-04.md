# C4 forced overlap routes

The uniform physical crossing gives a real source overlap at hub-zero defect.
Before exploring its child graph, compare [Sirvent–Solomyak](https://web.math.pmf.unizg.hr/~sonja/PDS-final.pdf)
and [Akiyama–Lee](https://arxiv.org/abs/1003.2898) for actual overlap refinement
and [Barge–Diamond](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
for the separate aligned good-pair condition. The repository already has
an exact seed-overlap graph and shortest-depth reader. Proceed on the
literal source overlaps from #466 with two specific questions. Can a
productivity path stay in the hub-zero defect plane? Can it transfer
through the original aligned good edge before hitting a diagonal?
The result is scoped to the completed source graphs.

## Exact first-step obstruction

Write an actual source overlap as `(x,y,E)`, with `E` the top
start minus the bottom start in Parikh coordinates. Ordered
child digits `(i,j)` give the exact update
```text
E' = M E + p(sigma(x)[:i]) - p(sigma(y)[:j]).
```
For hub `h`, let `q_h(x)` be the largest number of hubs in
a proper prefix of `sigma(x)`, including the empty prefix.
As the digit increases, the hub count starts at zero and
changes by zero or one. It attains every integer from zero to
`q_h(x)). Thus over the complete Cartesian product of digits,
`E'_h` attains every integer in
```text
[(M E)_h - q_h(y), (M E)_h + q_h(x)].
```
If this interval omits zero, **every actual overlap child
leaves the hub-zero plane**, regardless of the geometry filter.
If it contains zero, the candidate digits still have to be
checked for strict interior overlap. This criterion places no
restriction on whether a later child returns to the plane.

In both physical crossing controls from [PR #466](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/466),
the root is `(2,1,-e_0)) and the hub is 1. Each `sigma(0)`
contains exactly one hub, and no proper prefix of `sigma(2)`
contains a hub. Therefore the upper endpoint of the interval
is -1. This proves that every route to a diagonal from either
root must leave the hub-zero plane at its first step.

## Complete routes in the two controls

The canonical [seed-overlap graph](../kernel/psc/overlap_seed_patch.mojo)
enumerates every actual ordered child, retaining repeated
occurrences. Diagonals are absorbing targets. The independent
oracle uses integer prefix differences and certifies strict
endpoint order by the signs of lifted integer columns. It
raises on an exhausted 32-step sign budget or a vertex cap.
Both graphs close within 128 vertices.

| Substitution | Vertices / ordered edges | Direct diagonal | Left-aligned good edge | Diagonal via a left-aligned good edge | Maximum diagonal depth over all vertices |
| --- | ---: | ---: | ---: | ---: | ---: |
| `1/02/220` | 39 / 80 | 3 | 3 | 7 | 5 |
| `01/12/021` | 68 / 146 | 3 | 4 | 5 | 6 |

The good-edge target is the actual left-aligned pair `0/2`
in either orientation. The route-via depth minimizes the
distance from the root to that target plus the distance from
that vertex to a diagonal. This is a calculation about the
specific Barge–Diamond good edge, whose eventual witness was
checked in the preceding controls. A diagonal terminal does
not count as an intermediate good edge.

| Substitution | Actual first digit pairs | Remaining shortest diagonal depths |
| --- | --- | --- |
| `1/02/220` | `(0,0),(0,1),(1,1)` | `4,5,2` |
| `01/12/021` | `(1,0),(2,0),(2,1)` | `4,3,2` |

The depth-three routes from #466 are shortest. In the first
case the route is `(1,1),(0,0),(0,1)` and in the second it
is `(2,1),(1,0),(2,1)`. Neither route visits an aligned
good-edge state. In both graphs every reachable vertex is
productive, including every actual first choice. These
facts distinguish actual transport from a reduction that
keeps the defect in the hub-zero plane or that requires the
original good edge as an intermediate state.

## Replay and scope

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_forced_overlap_routes.mojo)
python -m pytest -q tests/test_c4_forced_overlap_routes_oracle.py
```

The first-step criterion is an integer derivation. The two
completed graphs and their route minima are finite results
for the supplied productive controls. General productivity
of the overlap forced by strict flatness and the one-step
C4 Sync conclusion remain open. No governed claim changes.

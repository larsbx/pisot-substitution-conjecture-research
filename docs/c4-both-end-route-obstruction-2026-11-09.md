# C4: a productive crossing with neither good-edge alignment

## Literature and scope

[Sirvent–Solomyak](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/4BC0FD9DBA6ECA027A32568F9E5C1D12/S0008439500017537a.pdf/pure_discrete_spectrum_for_onedimensional_substitution_systems_of_pisot_type.pdf)
and [Akiyama–Lee](https://arxiv.org/abs/1003.2898) use routes to actual
diagonals. [Barge–Diamond](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
gives the prefix witness for an aligned good pair. Reflection gives a
separate suffix criterion. Neither criterion asserts that a route must
visit an endpoint alignment of a specified pair. The earlier
[control](c4-good-edge-route-obstruction-2026-11-09.md) lacks the left
alignment but reaches the right one. Proceed with the narrower question
of whether a literal first crossing, with two complete flat generations
and a good pair witnessed on both ends, must reach either alignment.

## Literal source

Take `sigma=01/20/200` and hub 0. The incidence columns are
`(1,1,0), (1,0,1), (2,0,1)`. Its fourth power is positive.
The characteristic polynomial `x^3-2x^2-1` has no rational root,
discriminant -59 and real root `beta` in (2,3). The complex pair
has squared modulus `1/beta`, so the source is primitive irreducible
Pisot. The complementary pair `{1,2}` has common initial 2 and
common terminal 0 in its images `20` and `200`.

The sole child of `(02,20)` is `T=(01200,20001)`. Both words
occur in `sigma^3(2)`, at positions 7 and 0 respectively. The complete
first factor generation of T is `(01202000101,20001010120)`.
Its complete next row is

```text
(0120200012000101,2000101012001200), (012,120), (00120,20001).
```

All factors in these two generations are noncoincident and begin
with hub 0 on top only. The first factor in the second generation
has diagonal children in the third generation, so the finite cone
does not supply strict child closure.

Write `ell` for positive Perron lengths. The matched hub starts
on top are `0, ell_0+ell_1+ell_2, 2ell_0+ell_1+ell_2`.
On bottom they are `ell_2, ell_2+ell_0, ell_2+2ell_0`.
The bottom second hub completes before the top second hub, while
the top first hub completes first. At the start of the bottom
second hub the top source is letter 2. Both source indices are 2,
and each preceding prefix contains one hub. The Parikh defect
(top minus bottom) is `E=e_1-e_2`. In fact
`M E=-e_0`, and `M(E+e_2)=(1,0,1)`. Thus
`-ell_2 < ell E < 0`. The signed completion area is
`ell_2-2ell_1 < 0`, since `M(e_2-2e_1)=-e_2`.

## Complete graph and addressed witness

The strict-interior occurrence graph from `(2,0,E)` closes at
73 states and 152 ordered edges. The letter pairs with either
left or right alignment are exactly `00,01,02,10,20` in this graph.
Hence neither track order of the good pair is reached on either end.
Diagonal states can be made absorbing because their actual child
overlaps are diagonal too.

The shortest diagonal has depth five, with ordered digits

```text
(0,0), (2,1), (1,0), (0,0), (2,1).
```

These digits lift to the actual parent `(012001202000,202000120001)`
and local cut 6, with `Sync_+`. The factor ordinals are
`(0,0,6,0,1)`. The positive control `1/02/002` also replays its
right-aligned route, yielding a distinct `Sync_+` cut 15 of the same
parent where its other shortest path yields cut 5.

## Replay and boundary

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_forced_overlap_routes.mojo)
python -m pytest -q tests/test_c4_forced_overlap_routes_oracle.py
```

The native replay uses exact cubic-field endpoint signs and actual
digit choices. The independent oracle reconstructs integer offsets,
enumerates every occurrence and refactors the addressed words.
The graph cap is 128 states and the oracle allows 32 incidence lifts
per sign. A partial graph supplies no absence certificate.

This excludes a local rule requiring either alignment of the nominated
good pair before proving productivity, even when both endpoint
witnesses exist and two complete generations are flat. The
orientation-safe transfer remains valid when an appropriate alignment
is available. Uniform productivity in a fully strict child-closed
component remains open under [#461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

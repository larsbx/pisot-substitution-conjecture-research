# C4 periodic rays with an ordered hub phase

**Status:** repository-proved per-source criterion; independent human review pending.

Continuation of [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)
and the [periodic-ray criterion](c4-periodic-ray-decision-2026-11-14.md).
See the [pre-code source review](c4-phase-aligned-ray-stop-go-2026-11-14.md).

## Criterion

Let a primitive irreducible ternary Pisot substitution have a genuinely
left eventually coincident pair of letters. Denote the complementary hub
by `h`. Orient each noncoincident balanced block with first hub on top
whenever its first pair contains exactly one hub. Fix a proposed phase
`q ∈ {0,1}`: at every actual child occurrence, the hub side must stay
unchanged for `q=0` and flip for `q=1`. A finite strict system is
nonempty, consists of irreducible noncoincident balanced blocks, and
contains every child up to track interchange.

For each ordered cyclic first-letter root `(a,b,0)` containing exactly
one hub, use its complete reachable overlap graph. Attach to the root the
actual hub side `s₀` (top is 0 and bottom 1). Each edge toggles this label
by `q`, including an edge returning to an already visited geometric
type. Write `sₙ=s₀ xor ((n mod 2)q)` at depth `n`.

**Theorem (flat periodic-ray criterion).** A finite strict system of phase
`q` for the witnessed hub exists exactly when at least one cyclic root meets
all three tests:

1. No reachable overlap is diagonal.
2. Every reachable overlap has a descendant with a common start or end.
3. Every reachable zero-shift overlap has its hub on the attached side.

The first two tests are the ordinary periodic-ray criterion. Under test 1,
the two labels at a common start are always distinct, so test 3 requires
exactly one hub. A common right endpoint serves test 2. Its terminal letters
do not serve test 3.

### Necessity

Pass to the finite ordered swap closure and follow the first literal child
until a state repeats. The ordinary periodic-ray argument places the cycle
state `(u,v)` at the start of a pair of periodic rays. By complete closure
every factor of the full level-`n` image of that state has its first hub on
side `sₙ`. This induction uses all actual children and also works if a
parent is physically the swap of its hub-top representative.

Every graph path of depth `n` from the cyclic first-letter pair realizes
its addressed occurrences inside the first images `σⁿ(a),σⁿ(b)`, hence
inside `σⁿ(u),σⁿ(v)`. A common start is a balanced cut by rational
independence of the positive Perron lengths. It is not the final exterior
boundary because both letters start there. It therefore starts a literal
factor of the full reduction. Its hub is on side `sₙ`. The absence of
diagonals and the common-endpoint reachability follow from the ordinary
criterion via the bounded gaps supplied by the finite strict system.

### Sufficiency

Choose a positive common period `m` of the cyclic first letters, doubled if
needed so that `mq` is even. Tests 1 and 2 give tile-disjoint periodic rays
and an explicit bound on consecutive common vertices. Let `C₀` consist of
all complete blocks between consecutive common vertices. They occur in
sufficiently long prefix images of depths divisible by `m`. Test 3 thus
puts the hub on side `s₀` at every block in `C₀`. For each
`j=0,…,m-1`, take every depth-`j` factor of every block of `C₀`.
They are literal blocks of the phase-`j` images of the rays, inside prefixes
at depths `km+j` for sufficiently large `k`. Test 3 puts their hub on
side `s₀ xor ((j mod 2)q)`.

Every next-level occurrence flips its hub side by exactly `q`; at the last
phase this holds because the blown-up block decomposes within `C₀` and
`mq` is even. This also shows that taking the union across phases yields
complete one-step closure. Taking track swaps or hub-top representatives
does not change which children preserve or reverse the physical hub.
The union is finite and has no diagonal, giving the required flat system.

### A cycle obstruction for phase one

A reachable odd closed walk in the ordered overlap graph violates test 3
whenever the walk's base can reach any common start. One can traverse the
walk once or omit it before taking the same exit path, reaching the same
ordered common-start type with the two opposite expected hub sides. At least
one is forbidden. In particular a hypothetical strict flat phase-one SCC
has an ordered overlap carrier with **only even closed walks**. Indeed the
[whole-factor enclosure argument](c4-oriented-alignment-2026-11-04.md)
gives a path to an aligned start from each represented overlap of each
oriented component. This is an overlap-graph constraint. An odd closed walk
in a projected graph that forgets track order need not be an ordered walk.

## Literal paths and finite evidence

The native search authenticates the complementary good edge by exact
coincidence reachability. Its breadth-first search labels the visited
states by geometric overlap and expected side. The returned path is
replayed by regenerating the full ordered row at every traversed source
and locating the exact left and right occurrence digits. Diagonals are
terminal because their descendants are all diagonal. That terminalization
cannot erase a distinct forbidden common start. The inherited incidence
and graph caps fail closed. No source-size-independent bound is used.

| Substitution | Good edge | Hub | Phase | Cyclic root | First forbidden start | First root diagonal |
| --- | --- | ---: | ---: | --- | --- | ---: |
| `01/12/021` | `0,2` | 1 | 0 | `0,1` | depth 3, cut 7, `2/0` | 4 |
| `1/02/002` | `1,2` | 0 | 1 | `0,1` | depth 5, cut 11, `0/1` | 7 |

In the first row the forbidden start directly uses the witnessed good edge.
In the second it uses the wrong hub side at an odd depth. Its base swap
pair has earlier diagonal exits through a different overlap, so the
depth-five statement concerns the specified aligned letter root. The
independent replay exhaustively compares the Parikh prefixes of both
literal letter images through the reported depths, including all earlier
generations, and checks the exact signed path addresses. A control with
the wrong phase finds a spurious depth-one obstruction at the origin of
the swapping-hub root. The previous complete ordinary-ray tests and the
strict reducible refusal stay in the replay.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_periodic_rays.mojo) > /tmp/c4-periodic-rays.txt
PSC_PERIODIC_RAY_NATIVE=/tmp/c4-periodic-rays.txt python -m pytest tests/test_c4_periodic_rays_oracle.py
python tools/make_proof_bank.py --check
```

This identifies a third exact way to exclude a flat completion of a
candidate cyclic root. The remaining uniform step is to prove that every admissible ternary
Pisot root reaches a diagonal, reaches an overlap with no common-endpoint
descendant, or reaches a forbidden common start at its required phase. A wrong hub side alone does not supply
the one-step synchronizing newborn of #461. No general C4, G1, BH, A1′ or
PSC claim is changed.

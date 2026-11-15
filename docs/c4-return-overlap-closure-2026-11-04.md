# Complete two-track overlap closure for the return-word specimen

Date: 2026-11-04. Parent research lease: PR #487 at
`dec098d84f9faa52b67c55b4ef90ac5f7315218b`.

Status: exact finite computer-assisted specimen result with an independently
executed Python replay. Canonical Mojo source and complete parity workflow are
supplied, but native compilation/execution, full-repository governance and
hosted exact-head acceptance are not claimed. No governed PSC status changes.

## Stop/go and what is new here

The earlier 28-state one-track carrier is not itself a finite two-track model.
We now retain the complete integer prefix difference and impose **strict
physical overlap** at every actual child occurrence. For the fixed source
`01/121/012`, the resulting reachable graph exhausts its queue at 1,134
states. Every state has an occurrence-compatible path to coincidence within
five substitutions. This is a completed finite experiment, not a claim that
arbitrary legal exterior prefixes or arbitrary Pisot substitutions have the
same finite closure.

Finite overlap graphs and coincidence reachability are standard: see
Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine
tilings*, Advances in Mathematics 226 (2011), 2855--2883,
https://arxiv.org/abs/1003.2898 ; and Sirvent--Solomyak, *Pure Discrete Spectrum
for One-dimensional Substitution Systems of Pisot Type*, Canadian Mathematical
Bulletin 45 (2002), 697--710, https://doi.org/10.4153/CMB-2002-062-3 .
The scoped contribution is the exact return-boundary refinement, full
occurrence parity, concrete closure and shortest-depth certificate for this
already productive specimen. No general algorithmic or spectral novelty is
asserted, and no pure-discreteness theorem is imported or concluded here.

## Inputs, roots, and the exact admissibility test

Reuse the genuine return coding and the complete local carrier from
[c4-return-boundary-carrier-2026-11-04.md](c4-return-boundary-carrier-2026-11-04.md):

```
sigma=(01,121,012)
r=(01121121,012121121,012121,01121)
tau=(012,3212,322,02)
M=[[1,0,1],[1,2,1],[0,1,1]].
```

A local point is `(j,d)`, `0<=d<|r_j|`; there are 28. A two-track state is
`(s,t,delta)`, where `s,t` are these points and `delta` is the Parikh vector
of the **complete top prefix minus complete bottom prefix**. Let x and y
be the next physical letters. The two intervals, after translation, are

```
[ell.delta, ell.delta+ell[x]] and [0,ell[y]].
```

Here `beta` is the Perron root of `f(X)=X^3-4X^2+4X-2`, and
`ell=(1,beta-1,beta^2-3beta+2)`, with `ell M=beta ell`.
Strict overlap is exactly

```
ell.(delta-e_y)<0  and  ell.(delta+e_x)>0.
```

Endpoint contact is excluded. All signs are certified without floating point.
The native checker uses the rational bracket
`2839286/10^6 < beta < 2839287/10^6`. Its exact f numerators, with denominator
`10^18`, are `-4131286074344` and `1339065412903`. Uniqueness follows because
f' and f'' are positive on `[14/5,3]`. Outward intervals for the three lengths,
with denominator `10^6`, are `[1000000,1000000]`, `[1839286,1839287]`, and
`[1543683,1543693]`. An unresolved sign raises; it is never called disjoint.
The independent Python oracle instead bisects `[14/5,3]` sixty times using
`Fraction` and the monotonicity of `X^2-3X+2` there.

**Root scope:** overlay every ordered pair of the four return words with
their first zeros at the same origin. Test all 28-by-28 local pairs, with
`delta=Parikh(r_j[:d])-Parikh(r_k[:e])`. Exactly **118** decorated pairs
strictly overlap; they project to **11** physical triples `(x,y,delta)`.
No arbitrary exterior return-code prefixes or free translations are added.

## Complete child transport, not a guessed carry box

For every pair of actual child occurrences `(a,b)` in `sigma(x),sigma(y)`,
use the inherited local carrier edges and

```
delta'=M delta+Parikh(sigma(x)[:a])-Parikh(sigma(y)[:b]).
```

Retain the child if and only if its intervals strictly overlap. Preserve both
occurrence indices even when their target states agree. Substitution expands
physical lengths by beta, so a retained child is an actual positive-length
intersection within the inflated parent. Conversely every child-tile overlap
of the parent arises from one of the enumerated occurrence pairs. The local
return-state update preserves its original word occurrence and seam address.

The verifier interns every resulting state and processes the queue until no
unprocessed state remains. The cap 2,048 is a safety limit: hitting it raises
and produces **no closure verdict**. There is **no** depth cutoff and **no**
register-coordinate cutoff used to omit children. The separately verified
actual register range `[-2,2]^3` is an *output of complete closure*.

A second verification pass regenerates every ordered child row and requires
exact table equality. A removed occurrence, a duplicated edge, an unknown
child, or an altered distance is rejected. Thus finite closure is an exact
inductive certificate for all depths from precisely the stated root set:
initial states lie in the table and every genuine overlapping child stays
inside it. Queue provenance also shows every listed state is reachable,
not a synthetic necessary-condition packet.

## Exact closure and shortest coincidence witnesses

The independently reconstructed graph has:

| Quantity | Exact value |
|---|---:|
| Initial decorated overlaps | 118 |
| Reachable decorated states | 1,134 |
| Occurrence-labelled edges | 3,106 |
| Coincidence states | 120 |
| Physical quotient states | 87 |
| Physical quotient occurrence edges | 230 |
| Maximum minimum coincidence depth | 5 |
| Maximum absolute register coordinate | 2 |

Coincidence means `delta=0` **and** `x=y`; equal local labels alone do not
suffice. The shortest-distance distribution is:

| Distance | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---:|---:|---:|---:|---:|---:|
| Decorated states | 120 | 90 | 278 | 286 | 256 | 104 |
| Physical states | 3 | 6 | 16 | 28 | 26 | 8 |

For every noncoincidence state, the complete edge table supplies a child
with distance one smaller. Exact reverse-distance verification gives
`d(v)=1+min d(child)` and d=0 exactly at coincidences. Following decreasing
distances proves productivity in at most five generations, and the 104
states at distance five show that four is not a valid uniform bound for
this graph. This does not contradict the original depth-two simultaneous
**letter** coincidence: the present states include nonzero interior offsets.

The independent oracle checks an actual root occurrence for every state and
replays a shortest witness with literal next-letter descendants. Exterior
prefixes are transported exactly by `M^n delta`, not expanded into needlessly
huge strings; the descendant prefixes themselves are materialized. At the
terminal cut it verifies equal complete Parikh prefixes and equal letters.

The forgetful projection `(s,t,delta)->(x,y,delta)` maps onto the 87-state
physical graph. At each decorated state, its entire ordered child row maps
bijectively to the physical occurrence row with labels `(a,b)`. Therefore
every physical path lifts from every decorated state above its start.
Coincidence is preserved and reflected, and minimum distances are constant
on each fibre. This is an occurrence-compatible quotient, not only a matching
incidence matrix or an endpoint-mask heuristic.

## Why the unrestricted product is still infinite

Start with the identical physical letter 0 and equal prefixes. In the first
substitution choose child 1 on the top and child 0 on the bottom. The new
register is e0. Repeatedly choosing inherited cuts then yields `M^n e0`,
which grows without bound. The initial divergent child intervals have only
endpoint contact, so they are excluded by the genuine strict-overlap test.

Hence the finite closure here does **not** turn the full 28-by-28 affine
register system into a finite machine. It proves finiteness and productivity
only for this seeded, strict physical-overlap subsystem. General C4 still
needs a theorem transferring an arbitrary supplied strict carrier into an
appropriate complete productive overlap system; arbitrary exterior prefixes
have not been admitted, bounded, or excluded by this specimen computation.

## Reproducibility and acceptance

Canonical source: `kernel/psc/c4_return_overlap_closure.mojo`.
Native regression: `kernel/tests/test_c4_return_overlap_closure.mojo`.
Independent oracle: `tests/test_c4_return_overlap_closure_oracle.py`.
Exact-head workflow: `.github/workflows/c4-return-overlap-closure.yml`.

Locally executed: **16 Python tests passed** (seven new closure tests plus
nine predecessor carrier tests). The deterministic graph digest is
`ac438755b78e9407b1e3372286257a371651a9ca584b778ac7edcb62eac2e253`.
It hashes the ordered states, complete occurrence edges, distances and
initial-state count; it is a replay receipt, not a theorem oracle.

```
python -m pytest -q tests/test_c4_return_boundary_carrier_oracle.py tests/test_c4_return_overlap_closure_oracle.py
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_return_overlap_closure.mojo > /tmp/return-overlap-native.log)
python tests/test_c4_return_overlap_closure_oracle.py --native-log /tmp/return-overlap-native.log
python tools/make_proof_bank.py --check
```

The native test emits **every** state, edge occurrence and distance for the
independent oracle to compare, rather than comparing counts alone. Native
compilation and execution have not been performed in this runtime. Hosted
exact-head parity and full source-governance checks remain acceptance debt.
The existing mainline merge/Proof Bank reconciliation of #487 remains a
separate integration task; this increment does not overwrite either parent's
research ledger or generated inventory. No C4/G1/BH/A1-prime/PDS/PSC promotion.

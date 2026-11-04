# C4 cut contexts and additive boundary potentials

**Scope:** Conditional algebraic obstruction and exact finite controls for
[issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@772898054ea94f26c50d803b923b9bb99273814c` (merged #463).

## Targeted literature check

[Anderson–Putnam](https://doi.org/10.1017/S0143385798100457) use collared tiles
and an inverse limit to encode the substitution hierarchy.
[Barge–Diamond's one-dimensional construction](https://arxiv.org/abs/math/0702669)
gives a useful model for treating a tile as an edge with boundary vertices.
[Goodman–Strauss](https://annals.math.princeton.edu/articles/12903) constructs
matching rules in spatial dimension greater than one. That theorem supplies
no matching rule for these paired words. The
[Barge–Diamond coincidence theorem](https://doi.org/10.24033/bsmf.2433)
supplies a witnessed letter pair under its own Pisot hypotheses, and says
nothing about the potential tested here.

**Decision:** Use collaring to track actual cuts on both words. Test the
specific proposal that a single nonzero rational linear functional of the
common Parikh mass is an additive difference of boundary potentials. A
potential difference has zero sum around a closed path. The new point is to
test such closed paths across the same inflation hierarchy with their full
Parikh mass, using the existing
[two-generation rank argument](c4-two-generation-parikh-span-2026-11-02.md).
A general claim about all possible matching rules is outside this test.

## Repeated cut contexts force rank-three closed-path masses

Keep the two tracks in their physical order. A cut is an equal-prefix-Parikh
position in a balanced word pair. Its radius-`r` context records the last
`r` letters before and first `r` letters after the cut on **each** track.
Only cuts with complete contexts on both sides are used. A balanced block
between consecutive cuts has a common Parikh column `q`.

Suppose a supplied nonempty finite strict child-closed system of irreducible
balanced pairs has primitive, nonerasing substitution with rationally
irreducible cubic incidence matrix `M`. Fix any radius `r >= 1`.
A proposed potential is a single function `b` on these contexts and a fixed
rational row `f` satisfying, on every consecutive-cut block in the literal
inflations of the system,
```text
f q = b(right context) - b(left context).
```
Then `f = 0`.

**Proof.** Inflate any root pair. Primitivity and growth give arbitrarily long
words. For growth, some letter has image length at least two (a ternary
permutation matrix has eigenvalue 1), and some common iterate of every
letter contains it. Strict child closure and finiteness bound the length of
every irreducible factor by the longest supplied pair. Thus the number of
interior cuts with complete contexts eventually exceeds the finite number of
contexts. Choose two distinct cuts with the same context in a single
literal inflation. The intervening balanced block is nonempty, with common
mass `p`.

Both cuts persist after substitution. Indeed their top and bottom prefix
masses were equal, so the inflated prefix masses and hence their lengths
are equal. The context at each image cut is obtained by taking the last
`r` letters of the substituted left context and the first `r` of the
substituted right context on each track. Nonerasing substitution makes
these lengths available. Consequently the two endpoint contexts agree in
each of the next two literal inflations. The intervals have masses
`p, Mp, M²p`. Summing the proposed equation over every consecutive-cut
block in each interval telescopes to zero, so `f` annihilates all three
columns. If these columns were dependent, the span up to their first
dependence would be a nonzero proper rational invariant subspace of
`M`, contrary to irreducibility. Hence `f = 0`. ∎

The same proof applies to a finite refinement of the context labels if an
inherited cut's new label is a deterministic function of its old label.
The pigeonhole argument then uses the finite refined label set. Two full,
unbounded occurrence addresses are outside that hypothesis. In any concrete
certificate with determinant ±1 the telescoping obstruction holds over
every field, since the three columns remain independent after reduction.

## Exact controls

The parent `(0222022012,1220220220)` for `1/02/220` has equal radius-one
contexts `(01,22)` at newborn cuts 10 and 17 in its complete phase-one row.
Their right-side source addresses are `(4,0)/(4,1)` and `(7,0)/(7,1)`.
The literal interval is `(1220220,2022012)`. Its image cut positions and
total masses are

| Extra inflations | Cuts | Mass | Diagonal child ordinals within interval |
| --- | --- | --- | --- |
| 0 | 10, 17 | (2,1,4) | none |
| 1 | 23, 39 | (5,2,9) | none |
| 2 | 52, 88 | (11,5,20) | 5, 7 |

The determinant is +1. The radius-two contexts already distinguish the
original cuts. The inherited cuts retain identical radius-one contexts at
both extra levels. This is a productive control and a direct failure of
the potential equation on its complete interval. Its second extra
inflation includes diagonal factors, so this finite example does not refute
a potential restricted to strictly noncoincident blocks. The uniform
argument above uses strict closure to apply the equation on every block.

For the strict reducible control `10/102/211`, inflate `(102,210)` twice.
Cuts 11 and 19 have equal radius-two contexts `(0210,1021)`. Their three
successive masses are `(2,4,2), (6,10,6), (16,28,16)`. The determinant is
zero, the first two columns are independent, and `f=(1,0,-1)` annihilates
each column. All three intervals are diagonal-free. This calibrates the
irreducibility hypothesis.

For the productive Pisot control `01/12/021`, the complete depth-two image
of `(10,01)` has only one internal balanced cut, at 7. Full cone rank is
already three, but no repeated interior cut can be inferred at this depth.
The existing oracle verifies the later synchronizing newborn and diagonal
escape. Finding a repeated boundary context in the uniform proof uses
arbitrarily many actual cuts, rather than a fixed cone depth.

## Replay and open implication

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_recurrent_flat_exits.mojo)
python -m pytest -q tests/test_c4_recurrent_flat_exits_oracle.py \
  tests/test_c4_complete_cone_hub_audit_oracle.py \
  tests/test_c4_two_generation_rank_oracle.py
```

The replay checks fixed literal words and bounded integer arithmetic. The
uniform statement is the algebraic proof above. Issue #461 still requires
deriving a restriction from hub flatness and the genuinely good edge. In
particular the absence of a scalar boundary potential does not yield a
one-step interior `Sync_+` or `Sync_-` newborn. A matching rule using
ancestry or relative alignment remains possible. No C4, G1, or PSC claim
changes status.

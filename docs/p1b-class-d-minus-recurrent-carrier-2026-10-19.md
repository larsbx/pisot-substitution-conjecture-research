# Minus positive-b class D: cycle-sum reduction — 2026-10-19

**Status:** conditional reduction for issue #139. The earlier candidate premise
"every cyclic state lies in the sealed 145-label carrier" is **false** and is
superseded here. No class-D, #139, #84 or PSC theorem is promoted.

## 1. Inputs already on main

For the minus residual

```text
p = 3a+5+b,
q = 3a+6+b,
r = 2a+4+b,
a>=2, b>=1,
```

main contains:

1. **#287 algebraic selected-state descent.** Every non-target sealed label has
   valid occurrence-index formulas whose computed child state is another
   sealed label of strictly lower rank. Maximum rank is four.
2. **#288 conditional target geometry.** Whenever such a sealed source is a
   genuine overlap, its selected lower-rank target is also a genuine overlap;
   both target margins exceed `1/10`.

These facts make every genuine sealed-carrier state productive.

## 2. Why recurrent-carrier inclusion is false

The affine cycle analysis exposes four genuine recurrent candidates outside
the sealed carrier:

```text
U    = (y,c,-2, 4,-3)
Ubar = (c,y, 2,-4, 3)
V    = (y,c, 3,-6, 4)
Vbar = (c,y,-3, 6,-4).
```

The pair `U,Ubar` has an exact two-cycle whenever `b<=a`. The pair
`V,Vbar` has an exact two-cycle whenever `b<=a+1`. Hence the earlier
premise RC- ("every nonterminal cyclic state is sealed") must not be used.

This does **not** obstruct BH because all four states have productive exits.

## 3. Productive exceptional exits

### 3.1 The U pair

For

```text
U=(y,c,-2,4,-3)
```

choose top index `0` and bottom run index `b`. Exact affine replay gives

```text
U -> (c,y,2,-3,1),
```

which is sealed row 69, rank two.

The mirror choice gives

```text
Ubar -> (y,c,-2,3,-1),
```

sealed row 97, rank two.

These exits are valid for every `a>=2,b>=1`, whether or not the exceptional
two-cycle itself exists.

### 3.2 The V pair

Put

```text
A    = (y,y,-3, 5,-3),
Abar = (y,y, 3,-5, 3).
```

For every `a>=2,b>=1`:

```text
V -> A
```

by top run index `b` and bottom run index `a+2`; the mirror uses
`a+2` and `b`.

The geometric margins satisfy

```text
A lower = d + 3/beta - 2 > 0,
A upper = V lower.
```

Thus a real `V` produces a real `A`. The mirror statement is identical.

Now split only on `b=1` versus `b>=2`:

```text
b=1:
    A    -> sealed row 44, rank 2, FIRST/FIRST
    Abar -> sealed row 35, rank 2, FIRST/FIRST

b>=2:
    A    -> sealed row 69, rank 2, top FIRST / bottom run index b-1
    Abar -> sealed row 97, rank 2, top run index b-1 / bottom FIRST.
```

The carrier targets are uniformly real on the minus Perron box.

`kernel/psc/class_d_minus_exceptional_cycles.mojo` verifies all eight
occurrence edges and the corresponding geometric implications.

## 4. The remaining scalar premise

Write

```text
s(w) = wx+wc+wy,
m(w) = wx+wc,
tau(w) = wx-wc.
```

For one class-D child edge, the x/c endpoint structure gives

```text
m'   = 2s + eta,       eta in {-1,0,+1},
tau' = 2m - 2s + xi,  xi in {-2,-1,0,+1,+2}.
```

Therefore, on a directed cycle, the premise

```text
|s| <= 1
```

forces

```text
|m| <= 3,
|tau| <= 10.
```

This motivates the final open lemma.

> **CycleSum-.** Every genuine seed-reachable cyclic overlap in the minus
> positive-b residual satisfies `|wx+wc+wy|<=1`.

## 5. Exact guarded cycle superset

Assuming CycleSum-, every genuine cycle lies inside the finite typed box

```text
s in [-1,1],
m in [-3,3],
tau in [-10,10].
```

There are exactly 1,971 integral typed states in this box.

For each state and each of the nine first/run/last segment pairs,
`kernel/psc/class_d_minus_cycle_superset.mojo` computes the required
occurrence-index difference. Its legal interval is affine in `a,b`.
After shifting

```text
u=a-2 >= 0,
v=b-1 >= 0,
```

the two range conditions are affine forms in `u,v`. An edge is deleted only
when the repository's checked exact Farkas kernel proves those forms have no
common point. Failure to refute keeps the edge, so the resulting graph is a
sound overapproximation.

Its recurrent part contains exactly 145 vertices, classified as

```text
131 sealed-carrier states
  2 offset-zero states
  8 boundary-only states
  4 productive exceptional states
---
145 recurrent superset states.
```

The eight boundary-only states have an overlap margin identically zero and
therefore cannot be genuine interior overlap vertices. The four exceptions are
the U/Ubar/V/Vbar states of §3.

Hence:

> **Conditional theorem (CycleSum- => minus BH).** If CycleSum- holds, then
> every genuine cyclic overlap in the minus positive-b residual has an
> offset-zero descendant. Carrier states use #287/#288; offset-zero states are
> already done; boundary-only states are impossible; the four exceptions use
> §3.

The selected-path depth after entering the ranked carrier is at most four.

## 6. Why the sum lemma is genuinely the last gap on this route

For a child chosen at top/bottom word indices `i,j`,

```text
s(w')
 = (3a+7+b) wx
 + (3a+8+b) wc
 + (2a+6+b) wy
 + (j-i).
```

Equivalently,

```text
s(w')
 = b s(w)
 + a(3wx+3wc+2wy)
 + (7wx+8wc+6wy)
 + (j-i).
```

The earlier parameter-free SCC overapproximation that let each edge choose a
different `(a,b)` contains artificial higher-sum cycles. A representative
`|s|=2` cycle requires simultaneously

```text
v = 2u+7
and
v <= u,
```

with `u=a-2,v=b-1`, which is impossible. Thus common-parameter compatibility
around a cycle is essential.

The next proof should exploit this shared-parameter constraint, not enlarge
the overlap carrier.

## 7. Finite calibrations

The independent exact Q(beta) SCC oracle remains useful as a calibration, but
its former RC- interpretation is retired. Finite grids do not prove
CycleSum-.

## 8. Non-claims

- CycleSum- remains open.
- The old RC- premise is false and must not be cited.
- The finite 1,971-state superset is conditional on CycleSum-.
- The plus branch is separate and uses the merged finite chamber decomposition.
- Universal #139, #84 and PSC remain open.

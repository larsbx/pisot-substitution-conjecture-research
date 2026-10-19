# Minus positive-b class D: recurrent-carrier reduction — 2026-10-19

**Status:** conditional reduction for issue #139. This note proves the logical
interface from recurrent-carrier inclusion to boundary hitting. It does not
prove the recurrent-carrier premise itself and does not promote class D, #139,
#84 or PSC.

## 1. Inputs already on main

For the minus residual

```text
p = 3a+5+b,
q = 3a+6+b,
r = 2a+4+b,
a>=2, b>=1,
```

main now contains two separate facts about the sealed 145-label boundary
carrier.

1. **Algebraic selected-state descent (#287).** Every non-target sealed label
   has valid occurrence-index formulas whose computed child state is another
   sealed label of strictly smaller rank. There are six rank-zero targets and
   maximum rank four.
2. **Conditional selected-target geometry (#288).** Whenever such a sealed
   source label is a genuine overlap, the #287 selected target is also a
   genuine overlap. In fact both target overlap margins exceed `1/10`.

These statements do not assert that every child of a sealed label remains in
the carrier.

## 2. Full carrier closure is stronger than BH needs

The manuscript's two-obstruction completion theorem uses boundary hitting only
for vertices lying on directed cycles of the finite seed-patch overlap graph.

Transient children outside a convenient symbolic carrier therefore do not need
to be classified, provided they do not lie on a cycle.

This gives the exact remaining premise.

> **RC- (recurrent carrier inclusion).** Every seed-reachable nonterminal
> overlap vertex that lies on a directed cycle of a minus positive-`b`
> class-D seed graph has one of the 145 sealed labels.

This is strictly weaker than the positive-`b` child-closure statement
attempted by the original sealed-cover checker.

## 3. Conditional theorem

> **Proposition (RC- => BH on the minus positive-b residual).**
> Fix a minus positive-`b` class-D substitution with `a>=2,b>=1`.
> If RC- holds for its seed-patch overlap graph, then every cyclic overlap has
> an offset-zero descendant, at selected-path depth at most four.

### Proof

Let `v` be a cyclic overlap.

If `v` already has offset zero there is nothing to prove. Otherwise RC-
places its integral overlap label in the sealed 145-label carrier.

By #287 that label has a declared selected occurrence whose computed child
label has strictly smaller sealed rank. By #288, because `v` is a real
overlap, the selected target is also a real overlap; indeed its two overlap
margins are both greater than `1/10`. Thus the declared occurrence is an
actual overlap child.

If that child has offset zero, stop. Otherwise repeat. Every step strictly
decreases the nonnegative sealed rank. The maximum rank is four, so after at
most four selected steps an offset-zero label is reached. QED.

No child-closure premise was used.

## 4. Exact finite calibration

`oracles/python/class_d_positive_b_recurrent_support.py` asks RC- directly on
the declared finite grid

```text
2 <= a <= 8,
1 <= b <= 8.
```

For each of the 56 specimens it:

1. builds the complete exact Q(beta) seed-overlap graph;
2. recovers integral Parikh-offset labels by exact Gauss inversion;
3. computes exact SCCs;
4. keeps precisely SCCs carrying directed cycles;
5. fails if any nonterminal recurrent label lies outside the 145-label carrier.

Caps fail closed. A zero-escape finite result is evidence for RC-, not its
uniform proof.

## 5. Uniform proof target

The remaining minus theorem should now be stated as RC-, not full carrier
closure.

A natural route is cycle algebra. Every overlap edge has

```text
w' = M(a,b) w + delta,
M(a,b) = M(a,0) + b e_y 1^T.
```

For a directed cycle the accumulated `b`-dependent drift must close exactly.
The sealed carrier has the strong invariant

```text
1^T w in {-1,0,+1}.
```

The next proof attempt should determine whether cycle closure forces this same
small-sum regime (and the remaining sealed coordinate bounds) for every real
periodic orbit. This is a cycle-level statement and need not control arbitrary
transient children.

## 6. Non-claims

- RC- is open uniformly.
- Finite recurrent-support calibration is not a theorem.
- No plus-branch statement follows; the plus chamber certificate is separate.
- Universal #139, #84 and PSC remain open.

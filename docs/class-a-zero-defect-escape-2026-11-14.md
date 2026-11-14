# Minus Class A: strict zero-defect entry and legal-gap escape

Date: November 14, 2026. Research branch based on
`c9358c2d46d7b306853609e2c5a090328aff92c3`.

This is a local occurrence-level result for issue
[#452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452),
inside BH #139. It concerns the two equations defining the affine hull of
the known one-step target. **For every parameter and every strict source
in that zero-defect slice, the following construction gives an actual
ordered-occurrence path to integral offset zero in at most ten edges.**
This is a written symbolic theorem, with canonical native implementation
and separate Lean subfamily work; verification receipts are scoped below.
It does **not** prove that arbitrary cyclic seed descendants enter that
affine slice. The pre-code source review and
candidate decision are in
[the stop/go record](bh-class-a-entry-stop-go-2026-11-14.md).

## 1. Model and the complete reduction to endpoint states

Let `k,t>=0`, and write

```text
n=k+t+3, d=k+2t+5, A=n+d=2n+t+2, K=k+1.
sigma(x)=x y^A x, sigma(c)=c y^n x, sigma(y)=x y^(n-1) c.
```

All offsets are integral, oriented bottom-minus-top Parikh vectors. Use
`R_x=A`, `R_c=n`, `R_y=n-1`, and let `f(a)` and `e(a)` be the first and
last letters of the actual image of `a`. Thus `f=(x,c,x)` and `e=(x,x,c)`.
Let `delta=1_(f(a)=x)-1_(f(b)=x)`. The incidence update is

```text
M(p,q,r)=(2p+q+r, q+r, A*p+n*q+(n-1)*r).
```

Suppose a strict physical overlap `w=(a,b,p,q,r)` satisfies the
**zero-defect equations**

```text
p=delta, p+q+r=0.
```

Set `m=q+(d+1)*delta`. Then, identically,

```text
w=W_ab(m)=(a,b,delta,m-(d+1)*delta,-m+d*delta),
M(p,q,r)=(delta,-delta,m).
```

Normalize `L_y=1`, `L_c=1+h`, `L_x=2+rho`, where the existing exact
Perron certificates give `0<h<1/5` and `h<rho`. The cubic also gives
`1-rho-3h=K/(beta+1)>0`, as already recorded in
[the signed-strip note](class-a-x-signed-strip-2026-10-31.md), hence
`rho+3h<1`.
Write `F_a=L_(f(a))` and `E_a=L_(e(a))`. Since
`beta*L_a=F_a+R_a+E_a`, the strict source inequalities are exactly

\[
\boxed{-R_b-F_a-E_b<m<R_a+F_b+E_a.}
\]

Indeed `beta*L(p,q,r)=m+F_a-F_b`; substitute this into
`-beta*L_b<beta*L(p,q,r)<beta*L_a` and cancel the first-letter terms.
This equivalence uses strict inequalities throughout.

If `-R_b<=m<=R_a`, the existing complete one-step theorem applies.
Its legal positive occurrence pair is
`i=max(1,1+m)`, `j=i-m`, with a full integral offset-zero child. A
zero-offset source itself can instead use the empty path.

If `m>R_a`, put `s=m-R_a>=1`. The literal LAST/FIRST pair
`(R_a+1,0)` has child

\[
\boxed{B_{e(a),f(b)}(s)
  =\bigl(e(a),f(b),-\mathbf e_{f(b)}+s\mathbf e_y\bigr).}
\]

The proof is the full prefix calculation: the top LAST prefix is
`e_(f(a))+R_a*e_y`, the bottom FIRST prefix is zero, and
`(delta,-delta,0)=e_(f(a))-e_(f(b))`. The actual child letters are
`e(a),f(b)`, including the LAST `c` in `sigma(y)`.

Moreover, `1<=s<F_b+E_a` is exactly the strict-overlap condition for
this endpoint child. If `m<-R_b`, apply the same argument to the true
reversal `(b,a,-p,-q,-r)`, then reverse the complete path, swapping
every actual ordered index pair. This is not word reversal of `sigma`.

The possible endpoint states are therefore:

| Top/bottom endpoint types | Full offset | Possible positive `s` |
| --- | --- | --- |
| `x,x` | `(-1,0,s)` | `1,2,3,4`, and `5` exactly when `rho>1/2` |
| `x,c` | `(0,-1,s)` | `1,2,3` |
| `c,x` | `(-1,0,s)` | `1,2,3` |
| `c,c` | `(0,-1,s)` | `1,2` |

This is an exhaustive classification, not a rectangle of possible offsets:
`2L_x=4+2rho` lies in `(4,6)`, `L_x+L_c=3+rho+h` lies in `(3,4)`,
and `2L_c=2+2h` lies in `(2,3)`. Thus the entire strict zero-defect
slice reduces to the original target and at most **thirteen endpoint
states**. No seed-reachability premise or conclusion is hidden here.

There is also an exact count. Put `epsilon=1` if `rho>1/2`, and zero
otherwise, and let `Slice` denote all strict zero-defect states. Each oriented
`m` segment has `R_a+R_b+1` one-step points, plus
`floor(F_b+E_a)` upper and `floor(F_a+E_b)` lower overruns. The nine
upper terms have four `x/x` endpoint combinations, four mixed ones and
one `c/c`, so their sum is `30+4epsilon`. Therefore

```text
|Slice|=18n+6d+63+8epsilon.
```

The only possible integral sum boundary would be `2L_x=5`; the exact
separator below excludes it at every integral parameter pair.

Exactly five states of `Slice` have offset zero, corresponding to `delta=0`.
The full zero-offset set `Z` has nine oriented states, giving
`|Slice union Z|=18n+6d+67+8epsilon`. Compared with the complete one-step
predecessor set, this adds exactly `60+8epsilon` strict nonzero states.
The counts concern all formal strict states in this slice, not their
intersection with a swap-seed graph.

## 2. Explicit endpoint paths

Every row below is a composable list of actual `(top,bottom)` ordinals,
starting at `B_ef(s)` from the preceding table. The full successor is
always recomputed from the source letter, actual prefix and integral
incidence update. The endpoint is full Parikh offset zero. Its two
letters need not agree; for example the final `(3,1)` on a `y/y` source
at `n=3` uses a genuine top LAST `c`. BH requires this integral zero
target; it must not be silently called a typed coincidence.

### Eleven elementary endpoint cases

| Endpoint | Guard | Actual ordinal sequence | Length |
| --- | --- | --- | --- |
| `B_xx(1)` | all `k,t` | `(0,d+1),(2,1)` | 2 |
| `B_xx(2)` | all `k,t` | `(1,t+3),(3,1)` | 2 |
| `B_xx(3)` | all `k,t` | `(k+3,0),(0,n-2),(1,2)` | 3 |
| `B_xc(1)` | all `k,t` | `(0,1),(2,1)` | 2 |
| `B_xc(2)` | all `k,t` | `(n+1,1),(3,1)` | 2 |
| `B_xc(3)` | `k>=1` | `(2n+2,0),(t+3,0),(0,t+4),(4,1)` | 4 |
| `B_xc(3)` | `k=0` | `(2n+2,0),(n,0),(0,n),(0,n-1),(n+1,0),(t+3,1),(1,3)` | 7 |
| `B_cx(1)` | all `k,t` | `(1,d+2)` | 1 |
| `B_cx(2)` | all `k,t` | `(n+1,d+1),(d+2,0),(1,2)` | 3 |
| `B_cx(3)` | `k>=1` | `(k+3,0),(t+3,0),(1,t+5),(3,1)` | 4 |
| `B_cx(3)` | `k=0` | `(3,0),(n,0),(0,n),(n+1,0),(1,4)` | 5 |
| `B_cc(1)` | all `k,t` | `(1,2)` | 1 |
| `B_cc(2)` | all `k,t` | `(n+1,0),(d+1,n+1),(0,d+2),(2,1)` | 4 |

The number eleven counts distinct endpoint families; the two `s=3`
mixed cases have separate `k=0` and `k>=1` rows. The shorter suffixes
reuse existing local paths, including the E3 and L6/Q certificates.
The new statement is the full zero-defect source reduction and its
typed occurrence-compatible composition with those suffixes.

For clarity, the longest row has the complete state sequence, at `k=0`,

```text
(x,c,0,-1,3)
  --(2n+2,0)--> (y,c,1,2,-4)
  --(n,0)-----> (c,c,-1,-2,4)
  --(0,n)-----> (c,y,0,3,-4)
  --(0,n-1)---> (c,y,0,-1,2)
  --(n+1,0)---> (x,x,1,0,-2)
  --(t+3,1)---> (y,y,0,-2,2)
  --(1,3)-----> (y, sigma(y)[3], 0,0,0).
```

The two `B_cx(3)` branches are

```text
k>=1:
(c,x,-1,0,3) --(k+3,0)--> (y,x,1,2,-4)
 --(t+3,0)--> (y,x,-1,-2,4)
 --(1,t+5)--> (y,y,0,2,-2) --(3,1)--> (y,y,0,0,0).

k=0:
(c,x,-1,0,3) --(3,0)--> (y,x,1,2,-4)
 --(n,0)--> (c,x,-1,-2,4) --(0,n)--> (c,y,1,2,-4)
 --(n+1,0)--> (x,x,0,-3,3) --(1,4)--> (y,y,0,0,0).
```

All RUN and LAST distinctions follow directly from the displayed guards.
For example `A-(2n+2)=t>=0`, `n-1-(t+3)=k-1>=0` on the positive
`k` branch, and `n-(t+4)=k-1>=0`. At `k=0`, the index `t+3=n` in
the image of `y` is LAST `c`, which is why a separate branch is present.
Also `d+2<=A`, `t+5<=A`, `n+1<=A`, and `3<=n` throughout the
chamber. These are symbolic integer inequalities, not fitted finite data.

### The fourth x/x endpoint

For all parameters, the actual first edge

```text
B_xx(4) --(A+1,2t+1)--> V=(x,y,2,4,-8)
```

uses top LAST `x` and bottom RUN `y`: `1<=2t+1<=A`.
If `k+t>=1`, continue

```text
V --(2t+9,1)--> Y=(y,y,0,-4,4).
```

This is an actual RUN pair since `A-(2t+9)=2k+t-1>=0`.
For `k+t>=2`, `n>=5` and `Y --(1,5)-->` integral zero, with the
possible LAST at `n=5` retained. For `k+t=1`, use instead

```text
Y --(0,4)--> (x,c,1,0,-1) --(A+1,4)--> integral zero.
```

At the sole remaining parameter `k=t=0`, use

```text
B_xx(4) --(9,1)--> V --(7,0)--> (y,x,-1,-4,6)
 --(1,7)--> (y,y,0,2,-2) --(3,1)--> (c,y,0,0,0).
```

Thus this endpoint has a genuine zero-offset path of at most four edges
for every parameter. These formulas require exact independent replay
before an implementation acceptance claim is added below.

### The fifth x/x endpoint: exact existence guard

This endpoint is strict precisely when `rho>1/2`. The exact cubic gives

```text
beta*rho=t+2-2h,
(2beta+1)*(rho-1/2)=t-k-3/2-5h.
```

Consequently it exists exactly when

```text
t>=k+3, or t=k+2 and k>=2.
```

For `t-k<=1` the right side is negative; for `t-k>=3` it is positive.
For `t-k=2`, its sign is that of `beta-10`. Here `n=2k+5` and
`n+2<beta<n+3`, so it is negative at `k=0,1` and positive at `k>=2`.
Equality is excluded by these strict brackets. This is an algebraic
separator, not a floating-point root test.

Set `D=t-k`. The existence guard has exactly the following disjoint
path cases:

| Guard | Actual ordinal sequence from `B_xx(5)` | Length |
| --- | --- | --- |
| `D=2,k=2` | `(25,0),(25,0),(19,0),(0,2),(1,4)` | 5 |
| `D=2,k>=3` | `(A+1,0),(4k+18,0),(n-2,0),(2,1)` | 4 |
| `D=3` | `(A+1,0),(2t+10,1),(1,5)` | 3 |
| `D=4` | `(A+1,0),(7,0),(1,2t+10),(5,1)` | 4 |
| `D>=5,k>=1` | `(3k+2t+13,0),(D+3,0),(1,2t+10),(5,1)` | 4 |
| `D>=5,k=0` | `(2t+13,0),(n,0),(1,2t+9),(n,0),(1,0),(n,0),(0,n),(n+1,0),(1,4)` | 9 |

Here are the full coordinate reductions and the nontrivial word guards.
They also prove that the listed cases cover every strict `B_xx(5)`.

For `D=2,k>=3`, the first two targets are

```text
(x,x,2,5,-8), then (a,x,0,-3,4),
```

where `a=x` at `k=3` and `a=y` at `k>=4`. Indeed `A=5k+14` and
`A-(4k+18)=k-4`: the index is LAST exactly at `k=3`, RUN thereafter.
The next two targets are `(y,x,0,1,-1)` and integral zero. At the
remaining `D=2,k=2` point, `n=9,d=15,A=24`; the full path is

```text
(x,x,-1,0,5) --(25,0)--> (x,x,2,5,-8)
 --(25,0)--> (x,x,0,-3,5) --(19,0)--> (y,x,1,2,-5)
 --(0,2)--> (x,y,0,-3,3) --(1,4)--> integral zero.
```

For `D=3`, the first two targets are `(x,x,2,5,-9)` and
`(y,y,0,-4,4)`. The second top RUN has slack
`A-(2t+10)=3k+1>=1`; `n>=6` makes the final `(1,5)` legal.

For `D=4`, the first three targets are

```text
(x,x,2,5,-10), (y,x,-2,-5,9), (y,y,0,4,-4).
```

The last has the displayed `(5,1)` zero edge. The middle bottom RUN
has slack `A-(2t+10)=3k+2>=2`, and `n>=7` supplies the last ordinals.

For `D>=5,k>=1`, the first two targets are
`(y,x,2,5,-10)` and `(y,x,-2,-5,9)`, and the last two steps reuse
the preceding pair of targets. The first RUN has slack
`A-(3k+2t+13)=D-5>=0`. The second is an actual `y` RUN because
`n-1-(D+3)=2k-1>=1`.

At `k=0,D=t>=5`, that second ordinal is instead `n`, the LAST `c`
of the `y` image. Keeping this type gives the nine-edge path

```text
(x,x,-1,0,5) --(2t+13,0)--> (y,x,2,5,-10)
 --(n,0)--> (c,x,-2,-5,9)
 --(1,2t+9)--> (y,y,1,3,-5)
 --(n,0)--> (c,x,-1,-2,5)
 --(1,0)--> (y,x,1,2,-4)
 --(n,0)--> (c,x,-1,-2,4)
 --(0,n)--> (c,y,1,2,-4)
 --(n+1,0)--> (x,x,0,-3,3)
 --(1,4)--> (y,y,0,0,0).
```

The new bottom RUN has slack `A-(2t+9)=t-1>=4`. The last four
steps are exactly the already displayed `k=0` mixed-endpoint suffix.
All coordinates follow by the same literal integral update, and every
ordinal lies in the actual word. Thus all thirteen endpoint families have
zero paths of at most nine edges. Adding the initial overrun reduction
proves the claimed ten-edge bound on the entire strict zero-defect slice.

## 3. Why a legal final zero path supplies strict geometry

The path tables do not infer physical overlap from matching letter names.
Every step is a legal pair of proper occurrences and has the exact
integral child recurrence. At the last step the two child starts agree,
and both child lengths are positive. A common positive interval inside
these children is contained in both inflated parents. Pull it back through
the inflation, then repeat through the supplied composable occurrence
chain. Every ancestor and every displayed edge is therefore strict.

This is the existing actual-ancestry argument used by the one-step inverse
theorem and the multilevel prefix notes. It justifies the geometry of a
completed path once every ordinal and integral transport identity has
been proved. It does not construct a path from an arbitrary source.

### Actual multilevel prefix equality

Let the constructed path have depth `m<=10`, and write `z` for its source
Parikh offset triple. At level `r`, retain the
actual top and bottom prefix counts `P_r,Q_r` for its chosen occurrences.
The path is composable, so the nested choices specify actual proper
occurrences in `sigma^m(a)` and `sigma^m(b)`. Their full prefixes have
Parikh vectors

\[
p=\sum_{r=0}^{m-1}M^{m-1-r}P_r,\qquad
q=\sum_{r=0}^{m-1}M^{m-1-r}Q_r.
\]

Telescoping the literal recurrence gives `M^m z=p-q`, because the final
offset vanishes. This is an equality of full integral Parikh vectors at
genuine ordered occurrences, with the intermediate source and child
letters retained. No finite graph quotient is substituted for the path.

### What this changes in the remaining entry problem

Let `Gamma` be any actual, strict, occurrence-indexed, child-closed graph
at a fixed parameter, let `Z` be its full offset-zero set, and let `D`
be its strict zero-defect slice. For any nonzero-offset vertex,

\[
v\text{ reaches }Z\quad\Longleftrightarrow\quad
v\text{ reaches }D.
\]

For the forward implication, the predecessor of the first zero is in
the original one-step set and therefore in `D`. For the reverse
implication, append the at-most-ten-edge path proved here; actual child
closure retains every chosen successor in `Gamma`.

Thus the legal-gap condition can now be removed from the **multi-step
entry target**, while it remains necessary for the original one-step
test. This proves the rank-zero base case for the two-defect candidate.
It supplies no decreasing choice from arbitrary sources with nonzero
defects, so the universal BH entry assertion remains open.

For a production graph that terminalizes coincidence, stop a supplied
transcript at its first integral-zero hit. This retains its actual prefix
addresses through that hit and can only shorten the ten-step bound. No
claim that an arbitrarily longer literal transcript remains a production
path is needed.

## 4. Exact reachable countermodel to the two-defect rank

At `k=t=0`, so `n=3,d=5,A=8`, let

```text
X=(x,x,1,0,-1), w=(y,y,0,-4,4).
```

This is an actual recurrent X-descendant. Its two target defects vanish,
but its target gap `m=-4` is outside `[-2,2]`. In particular all three
proposed ranks `|p-delta|+|p+q+r|` and the two lexicographic orderings
of those absolute values are already minimal at this nonterminal state.
Its actual source path is

```text
X --(7,0)--> (y,x,0,-1,0)
  --(3,9)--> (c,x,-1,-1,3)
  --(0,1)--> (c,y,1,2,-5)
  --(1,1)--> w.
```

Its actual return path, checked by the canonical regression, is

```text
w --(0,2)--> (x,y,1,0,-3) --(0,3)--> (x,c,0,-3,4)
  --(2,1)--> (y,y,0,2,-2) --(3,2)--> (c,y,0,0,1)
  --(4,0)--> X.
```

The productive exit is

```text
w --(0,3)--> (x,c,1,0,-2)
  --(6,4)--> (y,x,-1,-1,2)
  --(0,7)--> (x,y,0,1,-1)
  --(2,1)--> (y,y,0,0,0).
```

The first arrival at the one-step target takes three edges, and zero
takes four. A complete direct enumeration of the first two actual child
stars checks 106 literal position pairs, accepts two first-level and
thirteen second-level occurrences, and finds no target or offset zero
at either level. Thus allowing a macrostep of at most two does not rescue
the proposed rank. This is a counterexample to that candidate mechanism,
not to BH.

There is also a uniform extension of this very missed-target shape:

```text
(y,y,0,n+1,-n-1) --(n,0)--> (c,x,-1,0,2)
 --(n+1,d+1)--> (x,y,1,1,-2)
 --(d+2,0)--> (y,x,0,-1,1) --(1,2)--> (y,y,0,0,0).
```

It holds for all `k,t>=0`, with true reversal giving the negative
orientation of the finite countermodel. It does not supply a uniform
ancestry from X for these sources at every parameter.

## 5. Validation and nonclaims

Before native implementation, the eleven elementary endpoint families
were independently replayed with full literal-word transport and exact
Perron strictness at eight selected parameter pairs:
`(0,0),(0,1),(0,9),(1,0),(1,1),(4,0),(2,3),(7,12)`.
This gave 88 paths and 236 checked edges. A second independent
literal-prefix oracle replayed six parameter pairs. These finite checks
test the written formulas; the universal statement rests on the symbolic
case partition, legal address inequalities and exact transport identities.

The fifth `x/x` endpoint was independently checked with full literal
transport and exact Perron strictness at fifteen targeted specimens
spanning every branch and its endpoint, including `(2,4)`, `(3,5)`,
`(4,6)`, `(0,3)`, `(0,4)`, `(1,6)`, `(0,5)` and `(0,64)`:
15 paths and 73 edges. The exact slice-count identity was also checked
at `(0,0)` (147 states, 60 overruns) and `(2,4)` (323 states,
68 overruns). These checks do not establish the universal quantifiers.

The canonical rank-negative regression is
`kernel/tests/test_class_a_entry_defect.mojo`. Its local runtime check
passed. The complete positive constructor is
`kernel/psc/class_a_zero_defect_escape.mojo`, with regression
`kernel/tests/test_class_a_zero_defect_escape.mojo`. Its native local
receipt is

```text
CLASS_A_ZERO_DEFECT_ESCAPE_PASS members=14 endpoint_paths=176
  slice_paths=904 checked_edges=4145 max_path=10
```

The emitted replay additionally includes 126 one-step and 126 empty
zero-offset base cases, for 1,332 complete path records. The module
and verification controls refuse non-strict endpoint cases, sources
outside the affine slice, negative parameters, nonexistent indices,
corrupted targets and checked integer overflow. The constructor does not
search for a path or accept a truncated search as a verdict.

The independent oracle `oracles/python/class_a_zero_defect_escape.py`
reconstructs incidence columns and proper-prefix counts from the actual
finite words. It compared all 1,332 emitted native paths and all 4,145
edges, including every original ordinal, intermediate letter pair and
Parikh coordinate. Its log acceptance also binds the exact fixture set,
rejects duplicate source keys, and independently reconstructs the complete
expected endpoint, one-step, zero and strict-overrun source set using
exact geometry. A log containing one valid row for each of the fourteen
members is therefore rejected as incomplete. The full native receipt
records `complete_source_set_compared=true`; a duplicate-row control is
retained as well. Separately the oracle enumerated the complete strict
zero-defect slices at the same fourteen named specimens: 3,970 source
states and 6,512 replayed edges, with maximum path length ten. Every
member's exact slice cardinality agreed with the formula above. This is
a complete finite check at the named parameters, not a parameter-cover
claim or a seed-graph census.

`oracles/python/class_a_zero_defect_symbolic.py` checks the unbounded
transport and ordinal guards coefficientwise over integer polynomials.
Its sixteen ordinary parameter chambers are the Cartesian products of
`{0}`, `{1}`, `{2}`, and `{u+3:u>=0}` for `k` and `t`. The seven
disjoint strict fifth-endpoint chambers are

```text
(k,t)=(2,4), (3,5), (u+4,u+6), (u,u+3), (u,u+4),
      (u+1,u+v+6), (0,v+5),   u,v>=0.
```

These are exactly the `D=2` singleton/boundary/tail, `D=3`, `D=4`,
and `D>=5` positive/zero-`k` cases. Every legal strict fifth endpoint
belongs to exactly one such chamber. The certificate verifies 199
endpoint/chamber paths and their genuine reversals: 398 directed paths
and 1,096 edges. FIRST and LAST are polynomial equalities; each RUN
ordinal has both lower and upper slack proved nonnegative by its
coefficients. It also checks the nine full source LAST/FIRST reduction
identities and rejects a deliberately altered ordinal. No sampled
selector is used as a proof of a guard.

The symbolic certificate supplies universal address and transport checks;
the geometric reduction, exact strictness separator, exhaustiveness of
the endpoint cases and backward strict-interval argument are the written
proof above. These boundaries are recorded separately from the finite
native/oracle replay. The corresponding pytest tests are
`tests/test_class_a_zero_defect_escape.py`; the observed test receipt is
recorded in section 6.

Exact-head hosted acceptance and independent review remain separate.
The scoped Lean compile and exact-type audit receipts are recorded in
section 6. They cover the two-step RUN/RUN slice and the four-step `y/y`
family; the entire endpoint table is not a Lean endpoint.

Nothing here proves full child closure, a finite cover of arbitrary
descendants, entry into the zero-defect slice, or the universal BH
quantifier. A1′, the nonunit realization dictionary, the alternate C4
strict-component route, and the all-alphabet generalization remain
separate. PR #574's conditional bridge is useful downstream and is not
used as an unconditional entry hypothesis.

## 6. Scoped Lean endpoints and integration receipts

The new `ClassAZeroDefectEscape.lean` module has compiled locally, and
`ClassAZeroDefectEscapeAudit.lean` has checked all 71 owned declarations
(53 theorem declarations, including generated/internal declarations). Five
exact theorem signatures and fifteen missing-declaration, wrong-type and
extra-premise controls pass. Only `propext`, `Classical.choice` and
`Quot.sound` occur in the permitted axiom closure.

The Lean endpoints prove the four-step overrun family displayed above and
the following additional two-step RUN slice. Set `S=p+q+r` and
`h=q+(d+1)*delta-(d-n)*S`. If

```text
p+S=delta, 1-R_b<=h<=R_a-1, and -(n-1)<=2S<=n-1,
```

then the actual first addresses `(1+max(h,0),1+max(-h,0))` give
`(y,y,0,2S,-2S)`. The next addresses
`(1+max(2S,0),1+max(-2S,0))` give integral offset zero. At
`|2S|=n-1`, an actual LAST `c` is retained, so equal terminal letters
are not asserted. Both results retain literal `Mark` witnesses and their
original indices; strictness follows from positive exact substitution
length scaling and the proved backward-containment lemma.

**The full thirteen-case, ten-step theorem is not a Lean endpoint of this
audit.** Its proof layer remains the complete written argument and universal
symbolic address/guard certificates, with native and independent exact
replay. The local Lean build reused byte-matched transitive development
objects; the dedicated fresh-source gate and the whole-library audit are
separate hosted acceptance checks. Their actual exact-head results must be
read from the PR, not inferred from the local audit.

The focused Python run passed all 23 tests (new regressions plus the old
one-step oracle), and the complete claim-governance, generated proof-bank
and vendored-pin checks pass. All 126 governed claims retain their existing
status. Raw successful and failed development receipts, reproducible
commands, and source hashes are in
[the evidence packet](../evidence/class-a-zero-defect-2026-11-14/README.md).

# Class-A boundary T_m: complete first/run and first/last children

Status: exact scoped chamber classification; not a closed carrier, rank or BH.
Independent human review pending. Continues the same first/run experiment in
the [three-source stop/go and child-carrier note](class-a-boundary-child-carrier-2026-10-26.md).
No new external theorem or spectral transfer is imported. Read the side-notes
ledger first: neither a first-child loop nor the previous outgoing star is a
closed obstruction. Decision: proceed with this next exact child-kind guard.

## Work shown

### Assumptions and hypotheses

Use exactly PR #348's boundary chambers, signs eps=+-1 and k,t>=0. Put
`n=k+3+t` minus, `n=2(k+2)+t` plus, `d=2n+6eps+5-k`.
Both actual run/run seed targets are `T_m=(y,y,-1,1,m)`, with
`m in {r,r+1}` and r the certified integer part of `u=d/(beta-1)`.
Normalize Ly=1, `b=1-eps/beta`, `a=b+u`, and `N=n+eps`.
No independent lengths, unimodularity or tiling realization is assumed.

### Derivation / reduction

The inflated parent displacement is `B=beta*(m-u)=m*beta-d-u`.
Top first x starts at 0; bottom run y at B+a+j-1. Its strict interior
intersection is therefore **equivalent** to

`-B-a < j < 1-B`, with actual word bound `1<=j<=N`.

Write `A=n+3+eps`, `alpha=beta-A`. The characteristic cubic gives the exact
identity

`u-alpha=1+2eps/beta`.

After multiplying by positive `beta*(beta-1)`, its difference is exactly
`-f(beta)=0`; the Mojo kernel recomputes this polynomial identity. Thus no
sampled eigenvalue, limiting estimate or rounding approximation is used.

The complete answer, always clipped to the actual word, is:

| Chamber / source | Exactly the admissible bottom run indices j |
| --- | --- |
| minus, T_1 | `max(1,t-1) <= j <= t+1` |
| minus, T_2 | none |
| plus, k=0..3, T_2 | `1 <= j <= 4-k` |
| plus, k=0..3, T_3 | none |
| plus, k>=4, T_1 | `k+t+10 <= j <= min(k+t+13,2k+t+5)` |
| plus, k>=4, T_2 | none |

In particular plus T_1 is empty at k=4, then has 1,2,3,4 occurrences at
k=5,6,7,>=8. Minus T_1 has 1,2,3 occurrences at t=0,1,>=2.

**Minus T_1.** The certified root bracket gives `0<alpha<1` and
`d-beta=t-alpha`. Put `v=alpha+1/beta`. Then `0<v<1`:

`beta^2*(1-v)=beta*(beta-t-4)+2>0`,

because `beta>n+2=t+k+5>t+4`. The two index margins are
`t-1-v < j < t+2-2/beta`. Since beta>2, integer rounding gives exactly
`t-1<=j<=t+1`. Only the lower actual-word bound clips; `N>=t+1`.

**Plus T_1, k>=4.** Put `s=k+t+11` and `v=alpha-1/beta`.
The exact positive identity
`beta^2*v=(k+t+9)*beta+2` gives v>0; u<2 gives v<1.
Now `s-1-v < j < s+2+2/beta`, so `s-1<=j<=s+2`.
The final y ordinal is N=2k+t+5, producing the explicit upper clip.

**Plus T_2, k<=3.** Two further exact positive identities are

`beta^2*(alpha-2/beta)=(k+t+8)*beta+2`,

`beta^3*(1+2/beta-alpha)=k*beta^2+(k+t+8)*beta+2`.

Thus `2/beta<alpha<1+2/beta`. The upper index margin
`U=5-k-alpha+2/beta` lies strictly in `(4-k,5-k)`.
For the lower margin, u>2 gives `alpha>1-2/beta`, hence
`L=2-k-2alpha+1/beta < -k+5/beta < 1` since beta>n+4>=8.
Therefore every j=1..4-k and no other integer passes. These all lie in
the word because `N-(4-k)=3k+t+1>0`.

**The three empty families.** Their m>u, so B>0. Every bottom run starts
at B+a+j-1>a, beyond the top first child's end. These are actual, available
word occurrences with disjoint interiors, and must not be admitted.

The complete target packet, independently verified in all coordinates, is

`(x,y,m,m+1,m*(n+eps)-d+j-1)`.

For minus T_1 write j=t+q: q=-1,0,1 (subject to word bounds), and the
target is `(x,y,1,2,q-4)`. For plus T_1 write j=k+t+11+q:
q=-1,0,1,2 clipped by q<=k-6, with the same target expression.
Plus T_2 gives `(x,y,2,3,k-10+j)`. These are finite lists of actual target
labels, not an assertion that the enlarged carrier is forward closed.

### Evidence and replay

Canonical kernel: `kernel/psc/class_a_boundary_next_run.mojo`. It checks the
cleared identity, exact polynomial remainders and positive coefficient cones
in Q[t,k], synthesizes at most four actual occurrences, and verifies them
through the existing literal-word/Parikh/Perron target-packet guard.

Native finite regression: `kernel/tests/test_class_a_boundary_next_run.mojo`;
80 fixed members, both T_m sources and every actual bottom run ordinal.
Independent oracle: `oracles/python/class_a_boundary_next_run.py`; 512 members,
1024 source cells, **22,784 actual run ordinals, 1,488 accepted occurrences**,
with the same finite budgets and
512-step rational-sign refusal of the already independent Geometry oracle.
The archived receipt states its finite scope. Finite agreement is not the
source of the all-parameter quantifier proved above.

From root:
```sh
python -m pytest -q tests/test_class_a_boundary_next_run.py
python oracles/python/class_a_boundary_next_run.py
python tools/make_proof_bank.py --check
```
From kernel/:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_next_run.mojo
pixi run --locked mojo run -I . class_a_boundary_next_run.mojo
```
Dedicated hosted native/Python workflow is required before integration.
No Lean source or governed theorem status is changed by this increment.

### Negative controls

The native verifier refuses corrupted polynomial identity, bad signs and
source m, indices outside the actual y-run, a word-legal but disjoint minus
T_1 j=t+2 child, and a mutated target coordinate at an otherwise legal index.
The plus k=4 packet must be empty. Keep both endpoint clips: replacing plus
N with an unconstrained formal index creates nonexistent occurrences.

### Non-claims / remaining gaps

This completes **first/run and first/last** for the two T_m sources, after first/first in
PR #348. The [complete T_m carrier note](class-a-boundary-tm-carrier-2026-10-26.md)
now resolves the other six kind guards for these same sources. Their further
descendants, global forward closure and composable well-founded descent remain open. In particular it
does not certify an intended interior boundary-hitting packet merely by
recognizing an intermediate target label. No universal BH, A1-prime, G1 or
PSC follows. The next source obligation after the complete table is
U=(x,y,1,2,-3), as recorded in the complete-carrier note.

## First/last: a second complete guard

The actual bottom last occurrence has ordinal `N+1` and type c, with shift
`B+a+N`. It intersects the top first x exactly when

`-a-b-N < B < -N`.

All signs except plus T_1 with `4<=k<=7` are excluded. In that sole chamber,
the exact target is `(x,c,1,2,k-9)` and the occurrence is `(0,N+1)`.

For minus T_1,
`B+N=k+1+2/beta>0`, contradicting the upper strict guard.
Minus T_2 and plus T_3 have B>0, and so does plus T_2 at k>=4.
For plus T_2 at k<=3,
`B+N=n+k-3+alpha-2/beta>0`, using the positive alpha margin already certified
above and `n+k-3=3k+t+1>0`.

For plus T_1 at k>=4, exact cancellation gives

`B+N=k-7-2/beta`,

`B+N+a+b=k-4+alpha-2/beta>0`.

The lower strict guard therefore always holds. Since beta>2, the upper
guard is equivalent to k<=7: at k=7 the value is still strictly negative,
whereas at k=8 it is strictly positive. Parikh transport gives
`2N-d=k-9`. The native certificate checks these coefficient identities and
the generic target guard verifies both actual endpoint types and full geometry.
The independent finite oracle checks all 1024 actual first/last pairs,
accepting precisely 64. This is separate from the 22,784 run-ordinal checks.

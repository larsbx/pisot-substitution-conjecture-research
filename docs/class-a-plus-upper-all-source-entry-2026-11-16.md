# Plus-Class-A upper entry from every strict integral source

Reviewed against main `065d59ee155592d17b1bc45207e9ed11776731f7`.
The central theorem and cycle exits are the ones integrated in
[PR #584](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/584)
at head `abc046c41eaaaf67003f14cf13a7693da8c13984`.

## Assumptions and hypotheses

Let n and d be integers with n ≥ 7 and n+5 ≤ d ≤ 2n+11. Use the original words

```text
sigma(x) = x y^(n+d) x
sigma(c) = c y^n x
sigma(y) = x y^(n+1) c
```

Use the positive eigenlengths from the
[central-source proof](class-a-plus-upper-central-recurrence-2026-11-15.md).
Write X = Lx, K = Lc, Ly = 1, J = 2n+12−d, and v = J/(β+1).
We use β > 11, 2 < X = β−n−2+1/β = 3+3/β−v < 10/3,
and 10/11 < K = 1−1/β < 1. These follow from the established
root bracket and v > 0. In particular every letter length is less than 4.

Take top letter a, bottom letter b and an arbitrary full integral offset
w = (p,q,r) in the order (x,c,y), with bottom-minus-top shift
u = Xp+Kq+r. Strictness is −Lb < u < La. The target is y/y with
|u| < 1/2. Such a source can use the empty entry path.

**Entry theorem.** Every strict integral source has a finite path of
actual ordered occurrences to this target. Orient the source so u ≥ 0
and let m = La−u > 0 in that orientation. If k is the least natural
number with β^k m ≥ 4, the path has at most k+1 edges. The orientation
change swaps complete tracks and negates the complete offset.

By concatenation with the existing written central-source theorem,
every strict integral source in this upper parameter range has a
strict original-occurrence path to typed y/y zero.

## Derivation / reduction

Write f(a) and g(a) for the first and last letters of sigma(a), and put
F_a = L_(f(a)), G_a = L_(g(a)), R_a = number of RUN occurrences.
These are literal quantities.

| Parent | FIRST at 0 | RUN at 1 through R_a | LAST at R_a+1 |
| --- | --- | --- | --- |
| x | x | n+d occurrences of y | x |
| c | c | n occurrences of y | x |
| y | x | n+1 occurrences of y | c |

A RUN prefix at i is e_(f(a))+(i−1)e_y. At LAST it is
e_(f(a))+R_a e_y. At FIRST it is zero. The length identity is
βLa = F_a+R_a+G_a. At every step with indices (i,j) the complete
update is w' = Mw + prefix_b(j) − prefix_a(i), where

```text
M(p,q,r) = (2p+q+r, q+r, (n+d)p+nq+(n+1)r).
```

### Direct RUN entry

For u ≥ 0 define D = β(La−u), E = G_a+F_b and
T(a,b) = (G_a+F_b+1/2)/β. For this orientation the ordered pairs
give the following values of E.

| Top \ bottom | x | c | y |
| --- | --- | --- | --- |
| x | 2X | X+K | 2X |
| c | 2X | X+K | 2X |
| y | X+K | 2K | X+K |

The first RUN start on the bottom minus that on the top is
s = βu+F_b−F_a = R_a+E−D. For two RUN indices the output shift is
s+j−i. The integer gaps i−j fill [1−R_b, R_a−1]. The exact lower
and upper range for central output is therefore
1/2−R_b < s < R_a−1/2, with half ties excluded.
The lower inequality holds because s ≥ F_b−F_a > −10/3 and R_b ≥ 7.
The upper inequality is D > E+1/2, or m > T(a,b).

Indeed s is the length of the full integral vector
Mw+e_(f(b))−e_(f(a)). The upper cubic has degree three, and for any
integral offset the identity βu = pβ²+(q+r−(n+2)p)β+(p−q)
precludes a half-integer u by comparing the coefficient of β after
clearing the factor 2. Thus s has a nearest integer e with strict
error less than 1/2. In the stated gap range the literal indices are
(1+max(e,0), 1+max(−e,0)). Their output is strictly central.

The same test applies for u < 0 after swapping tracks. To obtain
original indices, swap both selected indices back and negate the
full output offset. No track swap is itself an edge.

### The boundary cases

Suppose 0 < D ≤ E+1/2. Put A = g(a), B = f(b), G = G_a and F = F_b.

1. **0 < D ≤ G.** Select (R_a+1,0), producing A/B with shift G−D ≥ 0.
   It is strictly between −F and G. The new positive boundary distance
   is G−(G−D) = D = βm. This includes D = G.
2. **G < D < E.** The same (R_a+1,0) produces a strict A/B child with
   negative shift G−D. In the reverse orientation its distance is E−D.
   If E−D > T(B,A), use direct RUN entry from that child and return the
   original indices. Otherwise choose (R_a,0), the last RUN and FIRST,
   producing y/B with shift G+1−D. When D ≤ G+1 it is nonnegative
   and its distance is D−G = F−(E−D) ≥ F−T(B,A) > T(y,B).
   When D > G+1 its shift is negative, and its distance in reverse
   orientation is E+1−D > 1 > T(B,y). Both children in this second
   selection are strict and allow direct RUN entry.
3. **E ≤ D ≤ E+1/2.** Select (R_a+1,1), producing A/y with shift
   E−D in [−1/2,0]. It is strict. The reverse orientation has distance
   1+(E−D) ≥ 1/2 > T(y,A), which gives direct RUN entry. At shift
   zero the original orientation also has distance L_A > 2/3.

For the strict comparison in case 2, all T are less than 2/3, since
(2·(10/3)+1/2)/11 = 43/66 < 2/3. When B=x, F=X>2, so
T(B,A)+T(y,B)<4/3<F. When B=c, F=K, T(y,B)=(2K+1/2)/β<5/22,
so T(B,A)+T(y,B)<2/3+5/22=59/66<10/11<F.
These exhaust B. Also T(y,A)<((10/3)+1+1/2)/11=29/66<1/2.

Each pass through case 1 preserves the nonnegative orientation and
multiplies m by β. Since the new distance is at most its top tile
length, it remains below 4. The least k in the theorem exists by
β>1 and m>0. There can be at most k−1 successive case-1 edges.
The next choice takes at most two edges. This proof gives a
source-dependent bound without a finite carrier assumption.

### Original-prefix composition

For local proper prefixes p_i and q_j start from P_0=Q_0=0, and update
P_(t+1)=MP_t+p_i and Q_(t+1)=MQ_t+q_j. At the word level this replaces
the previously chosen proper prefix by its substituted word and appends
the proper prefix of the newly marked letter's image. Induction yields
actual original prefixes on both tracks and the identity

```text
w_t = M^t w_0 + Q_t − P_t
```

at every depth. The central continuation begins at exactly this typed
endpoint with all three coordinates. Its indices append to the same
tracks and its prefix counts continue the same update. At typed zero
the identity gives M^t w_0=P_t−Q_t.

## Evidence and replay

See the independent replay script in
[oracles/python](../oracles/python/class_a_plus_upper_entry_independent.py).
It uses the existing exact cubic sign oracle, expands the actual words,
and replays the selector's indices against counted prefix vectors.
It checks strictness, the complete transport identity, original prefix
counts and the entry depth bound. The grid uses n in {7,8,12,31}, J in
{1,2,3,4,5,n+7}, all nine ordered types, p,q in [−3,3], and integer r
within four of the unique central r for that p,q. At J=n+7 it also
includes both orientations of the near-boundary powers with t in
{1,2,4,8,12,20}. The Python step cap is 128, root refinement cap is 512,
and inherited literal-word cap is 50,000. Cap exhaustion refuses the
calibration. The native selector uses checked machine coordinates and
separately verifies each actual strict edge. It also feeds the exact endpoints into
the existing independent central replay.

```sh
(cd kernel && MODULAR_TELEMETRY_ENABLED=0 MODULAR_CRASH_REPORTING_ENABLED=0 \
  pixi run --locked mojo run -I . tests/test_class_a_plus_upper_entry.mojo --emit) \
  > /tmp/psc-plus-upper-entry-native.txt
python oracles/python/class_a_plus_upper_entry_independent.py \
  --native /tmp/psc-plus-upper-entry-native.txt \
  --transcripts /tmp/psc-plus-upper-entry.jsonl
python oracles/python/class_a_plus_upper_entry_independent.py \
  --replay-transcripts /tmp/psc-plus-upper-entry.jsonl
```

The local exact grid produced 33,684 paths and 47,412 entry edges
with maximum depth 37, including 22,748 paths composed to typed zero.
All 33,324 native paths and their 41,232 entry edges matched the
independent index pairs and integral targets. The standalone JSONL
replay accepted all 33,684 records. All 96 controls passed, and a
separate mutation of a supplied original prefix was rejected.

| Reproduced output | SHA-256 |
| --- | --- |
| Native stdout | `36ef371410b3817ddcde53403c25d972c4a9b4e035e7a7f3a93bb2d5e83d5acb` |
| Full entry JSONL | `c1dccf0c6f7f1ae8fcc953733035d705741e14787f5cf56c9890a3617015688d` |

The unchanged central native regression reproduced 818 paths and
4,728 edges. The existing upper cycle, symbolic and central Python
regressions passed all 95 tests.

## Negative controls

The strict y/c source w=(0,1,0) has u=K, D=1 and E=2K. Any
central one-edge child would have two RUN indices, but
1 < 2K+1/2, so the direct test fails for every member. The actual
two-edge path is

```text
y/c (0,1,0)  --(n+2,0)-->  c/c (0,1,-1)
             --(1,2)---->  y/y (0,0,0).
```

The middle shift is −1/β. The two local top prefixes are
(1,0,n+1) and (0,1,0), and the two bottom prefixes are (0,0,0)
and (0,1,1). The composed vectors are
P=(n+3,n+2,n+d+(n+1)^2) and Q=(0,1,1), so P−Q=M²(0,1,0).
Using n+1 in the first top index selects
y in place of c and must fail replay of the claimed packet. The
other controls alter an integral coordinate, truncate the path, and
supply a literal but touching child. The standalone replay also
checks the supplied final top and bottom prefix vectors.

## Lean obligations and scope

`ClassAPlusUpperEntry.lean` checks the real thresholds and boundary case
split, realizes the strict nearest-gap window as integer RUN indices,
and proves the abstract finite-path bound from the growth alternative.
The nearest-index lemma takes absence of half ties as a hypothesis,
established for this cubic in the written argument above. The isolated
Lean 4.34.0-rc2 target built against the manifest-pinned Mathlib, and
its five printed axiom reports contained only propext, Classical.choice,
and Quot.sound.

```sh
cd proof/PscVerif
lake build PscVerif.ClassAPlusUpperEntry
lake env lean ClassAPlusUpperEntryAudit.lean
```

## Non-claims / remaining gaps

The next entry-specific Lean step is to instantiate the arithmetic with
the literal upper words and the cubic no-half-ties lemma, and produce
`OrderedInteriorPath` and `MarkTrace` witnesses for the same indices.
Separately, assemble the central nearest recurrence, reconstruction, and
signed cycle completion into a central-source Lean theorem.
The n ≤ 6 upper members and universal BH #139 remain open here.
This proof makes no general spectral or Pisot substitution claim.

# Class-A minus boundary: complete U children and a nontrivial loop

Status: exact one-source symbolic child classification. Native acceptance is
head-specific and pending until its locked workflow passes. Independent human
review pending. No global closure, existential descent or BH theorem.

## Work shown

### Assumptions and hypotheses

Continue the same actual-occurrence experiment and the three-primary-source
[stop/go](class-a-boundary-child-carrier-2026-10-26.md#targeted-stopgo).
This is another specialization of the same affine overlap update; no new
spectral transfer or realization premise is introduced. The distinction between
potential and interior overlap, global termination debt, and non-unit internal
space hypotheses remain in force. Proceed with this narrowed outgoing-star
calculation; no claim of novelty for the standard overlap construction.

Restrict to the entire minus chamber: k,t>=0, n=k+3+t, d=2n-1-k.
Use the ordered words x->x y^(n+d) x, y->x y^(n-1) c, and c->c y^n x.
Offsets retain all three bottom-minus-top Parikh coordinates.
Set a=Lx/Ly, b=Lc/Ly, u=d/(beta-1). The accepted dependencies give
1<u<2, b=1+1/beta in (1,2), a=b+u, and n+2<beta<n+3.
The source is U=(x,y,1,2,-3), not a quotient of its Parikh offset.

The incoming occurrence witnesses are uniform: the aligned seed's (1,2)
child is T1=(y,y,-1,1,1); T1's (0,t+1) child is U. Both word bounds and
strict overlaps are checked, with the symbolic first/run proof in
[class-a-boundary-first-run-2026-10-26.md](class-a-boundary-first-run-2026-10-26.md).

### Derivation / reduction

U has normalized shift a+2b-3=u+3/beta. Inflation therefore has shift
B=beta*u+3=d+3+u. Put A=n+d, N=n-1, D=d+3.
The two words' first/run/last prefixes are (0,a+i-1,a+A) and
(0,a+j-1,a+N). The exact full incidence transport is
M*(1,2,-3)=(1,-1,D), before literal bottom-prefix minus top-prefix correction.
The proper-prefix Parikh vectors are 0, (1,0,i-1), (1,0,A) on top,
and 0, (1,0,j-1), (1,0,N) on bottom.

All run indices below are clipped to their actual word bounds
1<=i<=A and 1<=j<=N. Every excluded pair is geometrically disjoint.

| Top / bottom kind | Exact allowed indices | Typed child and full offset |
| --- | --- | --- |
| first/first | none | B>a |
| first/run | none | shift B+a+j-1>a |
| first/last | none | shift B+a+N>a |
| run/first | d+2<=i<=min(A,d+5), j=0 | (y,x,0,-1,d+4-i) |
| run/run | i-j in {d+4,d+5} | (y,y,1,-1,D+j-i) |
| run/last | none | shift B+N-i+1>=3+u>1 |
| last/first | i=A+1,j=0 iff k+t<=1 | (x,x,0,-1,3-n) |
| last/run | i=A+1, max(1,n-4)<=j<=N | (x,y,1,-1,2-n+j) |
| last/last | none | shift 2+u>a |

The rounding proof uses only the stated open bounds:

* Run/first shift is d+4-b-i. The strict inequalities -a<shift<1
  become d+2-1/beta<i<d+4+u, hence exactly d+2..d+5 before word clipping.
* Run/run requires abs(D+u+j-i)<1. Since 1<u<2, the only integer
  i-j values are d+4,d+5. For m=1,2 the exact free range is
  1<=j<=n-3-m with i=j+d+3+m; an empty range contributes nothing.
* Last/first shift is 3-n-b. Its upper margin is immediate since n>=3;
  its lower margin is 3+u-n. Thus it occurs exactly when n<=4,
  equivalently k+t<=1. No approximate root cutoff is used.
* Last/run shift is u+z, z=2-n+j. Its inequalities are -1-u<z<b;
  integer z is exactly -2..1, yielding the listed actual-word clip.

The first exclusions use d>=5 and b<2. Last/last is disjoint because
2>b. These exhaust the nine kinds and prove the full table over all k,t.
The canonical symbolic kernel independently checks the full indexed transport
polynomials in Q[t,k] and the parameter cancellations. It checks the legal
run-index basis 1,2 in each free index; affine dependence then fixes both
index coefficients while n,d remain symbolic. Its finite member API
uses checked machine arithmetic and refuses overflow; that API is not itself
an enumeration of unbounded integers.

There are exactly 2n-1 ordered children. The four contributing counts are
min(n-1,4), max(n-4,0)+max(n-5,0), [n<=4], min(n-1,4), respectively.
After projection, the exact union over the chamber has 12 labels:

| Child types | (x,c) | y coordinates |
| --- | --- | --- |
| y/x | (0,-1) | -1..2 |
| y/y | (1,-1) | -2,-1 |
| x/x | (0,-1) | -1,0 |
| x/y | (1,-1) | -2..1 |

Containment follows directly from the table and word clipping, not sample
extrapolation. The receipt supplies actual finite witnesses for all 12 labels,
which proves attainment of the listed finite union. A member need not attain
all 12. All children have c=-1, so no one-step zero-Parikh hit follows.

### A four-cycle prevents strict decrease on every child

For R(p,q,w)=(q,p,-w), the affine update and strict interior overlap are
preserved when the two occurrence indices are swapped. This is orientation
reversal of the same actual intervals, not identification of two target packets.
Every occurrence retains its original orientation in the carrier and tests.

For every n>=5 (k+t>=2) there is the following actual four-cycle:

| Source | Ordered occurrence (i,j) | Target |
| --- | --- | --- |
| T1 | (0,t+1) | U |
| U | (d+5,1) | R(T1) |
| R(T1) | (t+1,0) | R(U) |
| R(U) | (1,d+5) | T1 |

The only additional word condition is d+5<=A, exactly n>=5. Each target
has strict overlap by the preceding table or its orientation reversal. The four
labels are distinct. Therefore no function into a strict well-founded order
can decrease along **every** one of these edges: it would decrease around a
cycle. This is a universally quantified negative control for that stronger
rank proposal, separate from the finite replay of its witnesses.

It does not refute an existential choice of a productive child. For example
U always also has the distinct (d+2,0) child V=(y,x,0,-1,2), since n>=3.
The loop is not an independently certified closed obstruction: alternative
children have not been eliminated, and the union of packets is not proved
forward closed.

### The alternative V has exactly one child

The distinct V=(y,x,0,-1,2) child has shift 2-b=1-1/beta, hence
inflated shift beta-1. Exact clearing of the characteristic polynomial gives
beta-a=n+1/beta: multiplying the difference by beta*(beta-1) and
subtracting beta-1 leaves exactly the minus characteristic cubic. This
identity is checked coefficientwise by the canonical polynomial kernel.

For every actual V child the complete nine-kind classification is:

| Top / bottom kind | Exact conclusion |
| --- | --- |
| first/first, first/run, first/last | beta-1>a, and a bottom prefix cannot reduce it |
| run/first | beta-a-i >= 1+1/beta>1 for i<=n-1 |
| run/run | beta-1+j-i >= beta-n+1>1 |
| run/last | beta+A-i>1 |
| last/first | only (n,0), shift 1/beta, target W=(c,x,0,1,-1) |
| last/run | beta-n+j-1 >= beta-n>2>b |
| last/last | beta+d>a |

The top word is sigma(y), whose last ordinal is n, and the bottom is
sigma(x). Its full incidence update is M(0,-1,2)=(1,1,n-2).
Subtracting the last top prefix (1,0,n-1) gives precisely (0,1,-1).
Thus V->W is forced throughout the unbounded minus chamber. W has shift
b-1=1/beta>0, strictly inside both actual intervals. This supplies neither
a zero-offset hit nor an asserted successful boundary packet. W's alternative
children are the next remaining symbolic case.

### Evidence and replay

Canonical: kernel/psc/class_a_boundary_u_children.mojo; driver
kernel/class_a_boundary_u_children.mojo. Synthesis is O(n), using two run/run
strips and at most four occurrences per endpoint range. It never takes the
Cartesian product in the production carrier. Every supplied target packet
is rechecked against actual words, full Parikh transport and canonical exact
Perron-field interior geometry.

Native regression kernel/tests/test_class_a_boundary_u_children.mojo checks
all child pairs of 56 members (k=0..7,t=0..6), no duplicate synthesized
occurrences, exact 2n-1 cardinality, all 12 attained labels, orientation reversal
and every edge of the actual four-cycle when n>=5. It also exhausts every V
child pair and verifies the unique typed target W. A hosted receipt is required
before acceptance; a written native test is not a native pass.

Independent oracle oracles/python/class_a_boundary_u_children.py constructs
literal word prefixes and uses the separate integer-polynomial/Fraction
Perron embedding with its 512-refinement refusal budget. The archived replay
covers **117 members, 61,308 ordered pairs, 2,925 accepted** and 114 actual
four-cycle specimens. A further 61,308 independent V child pairs have exactly
117 accepted occurrences, all the single (n,0) target W. These are finite
evidence, not the universal proof.
The JSON and SHA256SUMS are in evidence/class-a-boundary-u-2026-10-26/.

From repository root:
```sh
python -m pytest -q tests/test_class_a_boundary_u_children.py
python oracles/python/class_a_boundary_u_children.py
python tools/make_proof_bank.py --check
bash tools/verify_all.sh provenance
```
From kernel/:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_u_children.mojo
pixi run --locked mojo run -I . class_a_boundary_u_children.mojo
```
Local locked native replay passed: 16,548 U pairs / 1,008 accepted and a
further 16,548 V pairs / 56 unique children; all 12 U labels attained and
53 actual four-cycle members. Both certificate drivers and the inherited
T_m regressions also passed (47,950 full-table pairs and 3,126 endpoint
ordinals). The archived native-local.txt pins the source bytes and preserves
the command output; it does not assert that hosted CI has run. The local
TLA gate passed all 18 expected model outcomes. The local Lean launcher
failed before compilation with "failed to locate application"; no fresh local
Lean pass is claimed. formal-local.txt preserves both outcomes. The unchanged
Lean source bank has the earlier accepted #348 hosted proof/audit receipt;
fresh hosted gates remain pending.

Dedicated workflow: .github/workflows/class-a-boundary-u.yml. No Lean source,
TLA dependency model or governed theorem status changes. Existing formal gates
remain applicable; the whole U table has not been formalized in Lean.

### Negative controls

Corrupted symbolic Parikh identity, nonexistent occurrences, geometrically
disjoint first/first, same-index runs and last/last pairs, altered typed target
offsets, duplicate occurrences, a missing envelope witness and a universal
all-child strict rank are explicit counter-controls. Unresolved exact signs or
machine overflow refuse instead of silently producing a mathematical verdict.
V additionally refuses unavailable ordinals, an altered W packet and its
word-legal but disjoint first/first child.

### Non-claims / remaining gaps

The 12-label image is not forward closure; neither it nor the earlier 50-label
image is claimed to be a complete occurrence-compatible descent mechanism.
The universal four-cycle excludes only a strict rank on all edges, while an
existential rank may choose another edge or a more structured packet.
The uniform alternative U->V at (d+2,0) now has the forced continuation
V->W at (n,0), with W=(c,x,0,1,-1). W's complete outgoing table and
productive target compatibility remain unresolved. Other U targets and the
earlier image labels also require
closure or descent, with the independent realization/internal-space hypotheses
still retained. Universal BH/#139, A1-prime, G1 and PSC remain open.

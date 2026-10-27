# Class-A minus boundary: a uniform six-step seed coincidence

Status: exact physical one-seed reachability on the entire minus chamber.
Four complete outgoing child stars accompany the path. This does not prove
universal BH/#139, forward closure of all relevant states, or PSC. Independent
human review pending; native/formal acceptance remains revision-specific.

## Work shown

### Assumptions and hypotheses

The [targeted stop/go](class-a-boundary-w-stopgo-2026-10-27.md) revisits three
primary sources before this experiment. The standard overlap update is prior
art; the result here is a specialized uniformly indexed path and exact carrier.
Use k,t>=0, n=k+3+t, d=2n-1-k and the actual minus words
x->x y^(n+d) x, c->c y^n x, y->x y^(n-1) c.
Offsets are full bottom-minus-top integer Parikh triples. Put A=n+d, N=n-1.

Accepted dependencies #349 and #352 establish all required root/length facts,
occurrence kernels and strict geometry at their exact source scope. Write
h=1/beta, b=Lc/Ly=1+h, u=d/(beta-1), a=Lx/Ly=b+u.
Then 0<h<1/2, 1<u<2 and beta-a=n+h. No decimal approximation enters.
The physical interval predicate is -length_bottom < shift < length_top.

The sources newly completed are
W=(c,x,0,1,-1), Z=(c,x,0,0,1), X=(x,x,1,0,-1),
and Q=(y,x,0,-1,1). Their shifts are h, 1, a-1 and -h.
Their inflated shifts are 1, beta, d+1+u and -1, respectively.
The exact incidence/prefix update, actual occurrences and typed target packet
are all retained; a matching symbolic pair alone cannot accept an edge.

### Derivation / reduction

A top c word has prefixes 0, (0,1,i-1), (0,1,n), and physical starts
0,b+i-1,b+n. A top x word has prefixes 0,(1,0,i-1),(1,0,A),
starts 0,a+i-1,a+A. A top y word has prefixes 0,(1,0,i-1),(1,0,N),
starts 0,a+i-1,a+N. Bottom sigma(x) always has starts 0,a+j-1,a+A.
Full incidence transports before prefix correction are

| Source | M applied to its offset |
| --- | --- |
| W | (0,0,1) |
| Z | (1,1,n-1) |
| X | (1,-1,d+1) |
| Q | (0,0,-1) |

The following table is complete for all nine kinds of every source. Every run
index obeys its actual word bounds: top i in 1..n for W/Z, 1..A for X,
1..N for Q; bottom j in 1..A. Empty run/run ranges contribute nothing.

| Kind | W | Z | X | Q |
| --- | --- | --- | --- | --- |
| first/first | (0,0) | none | none | (0,0) |
| first/run | none | none | none | (0,1) |
| first/last | none | none | none | none |
| run/first | i=1..3,j=0 | none | i=d..d+3,j=0 | none |
| run/run | i-j=2,3 | none | i-j=d+2,d+3 | j=i+1 |
| run/last | none | none | none | none |
| last/first | none | (n+1,0) | none | none |
| last/run | i=n+1,j=n-2..n+1 | none | i=A+1,j=n-2..n+1 | i=n,j=n+1,n+2 |
| last/last | none | none | none | none |

For W, run/first has shift 2-b-i. The guard -a<shift<1 gives
1-b<i<2+u, hence i=1,2,3. Run/run has shift 1+u+j-i, giving
u<i-j<u+2 and therefore i-j=2,3. Last/run has shift u+j-n;
its bounds give j=n-2..n+1. Last/first would require 1+u-n>0,
which fails since n>=3,u<2. First/run and first/last exceed top length b;
run/last and last/last are disjoint from d>=5. First/first shift 1 is
strictly less than b and greater than -a.

For Z, beta-a=n+h implies run/first shift beta-b-i+1>=a>1
at every i<=n. Run/run is even farther to the right. Last/first has shift
a-1, strictly between -a and a, and gives exactly X. Last/run already has
shift beta+u+j-n-1>=a+h+u>a. The first and remaining last pairs are
disjoint by beta>b and d>=5. Thus Z has exactly one actual child.

For X, run/first shift is d+2-b-i. Its bounds become
d-h<i<d+2+u, giving d..d+3, all actual since n>=3.
Run/run shift is d+1+u+j-i, giving i-j=d+2,d+3. Last/run is again
u+j-n, giving the same four j values. Last/first has shift -n-h;
its lower margin is a-n-h=1+u-n<0, so it is excluded. Every first
pair is disjoint since d+1+u>a; run/last and last/last are also excluded.

For Q, first/first shift -1 is strictly inside (-a,a). First/run shift
a+j-2 meets its top interior only at j=1; j=2 touches the endpoint exactly.
Run/first is -a-i and disjoint. Run/run shift j-i-1 is an integer, so the
strict bounds (-1,1) require j=i+1, giving typed coincidence (y,y,0).
Run/last shift A-i>=d+1 is disjoint. Last/first is less than -a.
Last/run shift j-n-1 must be an integer in (-1,b), hence is 0 or 1;
these give j=n+1,n+2. Last/last shift d exceeds b. These are all the cases.

The full target labels are reconstructed by the Parikh formula, never from
shift alone. Ordered occurrence counts are 2n+3 for W and X, one for Z,
and n+3 for Q. The outgoing union over all members has exactly 17 labels:

| Types | (x,c) | y |
| --- | --- | --- |
| y/x | (0,-1) | -1..2 |
| y/y | (1,-1) | -2,-1 |
| x/y | (1,-1) | -2..1 |
| c/x | (0,0) | 1 |
| x/x | (1,0) | -1 |
| x/x | (0,0) | -1 |
| x/y | (1,0) | -1 |
| y/y | (0,0) | 0 |
| c/y | (0,0) | 0,1 |

Containment follows by substituting the complete index ranges. The independent
receipt gives actual finite witnesses attaining all 17, proving equality of
the union, not just a guessed envelope. Only 16 appear at n=3, since the
second run/run strip is empty. The union is not claimed forward closed.

### Six-step physical coincidence from the aligned seed

The following is one uniform selected path for every k,t>=0:

| Stage | Source | Actual (i,j) | Target |
| --- | --- | --- | --- |
| 0 | (x,c,0,0,0) | (1,2) | T1=(y,y,-1,1,1) |
| 1 | T1 | (0,t+1) | U=(x,y,1,2,-3) |
| 2 | U | (d+2,0) | V=(y,x,0,-1,2) |
| 3 | V | (n,0) | W=(c,x,0,1,-1) |
| 4 | W | (1,0) | Q=(y,x,0,-1,1) |
| 5 | Q | (1,2) | C=(y,y,0,0,0) |

The earlier exact seed and U/V tables prove the first four selections.
The W table proves the fifth; the Q table proves the sixth. All are actual:
n>=3,d>=5, t+1<=n-1, d+2<=A, and run indices 1,2 exist.
The symbolic kernel additionally checks each full Parikh transition as a
polynomial identity with cone-certified actual prefix indices.

The normalized source shifts are 0, 1-u, u+3h, 1-h, h, -h, 0,
with types x/c,y/y,x/y,y/x,c/x,y/x,y/y. Each is strictly interior:
for U the only less immediate upper margin is a-(u+3h)=1-2h>0;
all others follow directly from h>0,h<1/2,1<u<2,a=b+u,b=1+h.
Thus this is a genuine nested occurrence-compatible physical coincidence
path of length six, rather than a numerical graph extrapolation.

Assign ranks 6,5,4,3,2,1,0 to these seven distinct typed labels in order.
Each selected edge decreases that natural-number rank. The rank refuses
states outside this selected packet; it is not a rank on all children or on
all relevant strict-zipper states. The full child stars retain every alternative.

In particular every member also has an actual cycle
V -> W -> Z -> X -> V at indices (n,0),(0,0),(n+1,0),(d,0).
The W->Q->C exit shows concretely why that cycle is not a closed obstruction.
A rank decreasing on every actual edge remains impossible; the selected path
provides a valid existential exit for this seed only.

### Evidence and replay

Canonical kernel: kernel/psc/class_a_boundary_w_children.mojo. Star synthesis
is O(n) and uses at most two run/run strips plus bounded endpoint ranges.
Typed envelope membership is constant-space; no 17-label list is rebuilt per
edge. The member interface refuses machine overflow; the symbolic proof and
coefficient certificates quantify over all k,t. Driver:
kernel/class_a_boundary_w_children.mojo.

The native regression exhaustively compares every ordered occurrence pair of
W/Z/X/Q against literal target transport and exact Perron-field geometry on
56 members. It checks 93,604 pairs / 3,220 accepted, all 17 image labels,
336 selected path edges, every actual four-cycle and all negative controls.
This locked local run passed. Dedicated hosted acceptance is still required
at the PR head and is not inferred from writing the test.

The separate integer-polynomial/Fraction oracle uses literal prefixes, not the
Mojo guard code. Its fixed 512-refinement budget refuses instead of guessing.
Receipt: 117 members, 468 source cells, 340,704 ordered pairs, 8,775 accepted,
all 17 target labels with actual witnesses, 702 selected path edges.
These finite replays check the implementation; the uniform proof is above.

From root:
```sh
python -m pytest -q tests/test_class_a_boundary_w_children.py
python oracles/python/class_a_boundary_w_children.py
python tools/make_proof_bank.py --check
bash tools/verify_all.sh provenance
```
From kernel/:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_w_children.mojo
pixi run --locked mojo run -I . class_a_boundary_w_children.mojo
```
Hosted native/Python workflow: .github/workflows/class-a-boundary-w.yml.

PscVerif.BoundarySeedPath adds four narrow Lean lemmas: the six full integer
Parikh updates, actual index bounds, the seven rational open-interval guards
under explicit length assumptions, and strict decrease of the selected stage
rank. They do not formalize the Perron root/embedding, generic word kernels or
universal BH. The rational guard lemma is an algebraic check under assumptions;
it does not assert that beta or the actual lengths are rational. The new module
is imported by the root proof bank; the official generator inventories 34
named proofs while all 120 governed claims and their statuses remain unchanged.
Fresh hosted Lean compilation and the complete axiom audit are required;
the local Lean launcher still fails before compilation and earns no proof pass.

### Negative controls

The native and oracle tests reject an intermediate corrupted edge even when
the submitted packet ends at C; a terminal target cannot validate its history.
They reject unavailable ordinals, altered targets, disjoint word-legal children,
and the Q first/run endpoint contact (0,2). Symbolic transport corruption
refuses. Q also has a genuine zero-Parikh c/y child at (n,n+1): it intersects,
but it is not typed coincidence because c and y differ. The terminal predicate
requires equal tile types AND zero offset. A state outside the selected packet
cannot be silently assigned a rank or classified as a successful target.

### Non-claims / remaining gaps

This discharges physical coincidence reachability for this one aligned seed
family on the entire minus boundary chamber. It does not cover every relevant
strict-zipper state or the plus chamber. The chosen seven-state path is not
forward closure of the 17-label outgoing union or earlier 50-label image.
Neither a first-child loop nor the displayed cycle supplies a closed obstruction.
The coincidence C is a concrete typed terminal, not a proof of every intended
boundary packet or of the global return-lattice/internal-space realization.

For further carrier closure, a smallest new unclassified source is
E=(x,x,0,0,-1), reached uniformly from W at (1,0) and then Q at (0,0).
Its complete children and the other unclassified targets remain open in this
increment. For #139 the missing quantified premise is occurrence-compatible
coverage of every relevant strict-zipper state and compatibility with the
specific boundary-hitting target, rather than just this one seed's C terminal.
Universal BH, A1-prime, G1 and PSC retain their existing open statuses.

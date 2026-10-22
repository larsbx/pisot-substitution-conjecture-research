# Class A d=2: first descent proof obligations and a uniform rank obstruction (2026-10-22)

**Status:** finite-domain exact path-witness research with a scoped uniform integer-affine *negative lemma*; no all-n hitting result and no universal PSC promotion. Independent human review and fresh CI acceptance pending.

## Scope and targeted literature/method gate

The accepted gap-one line's first-hit certificate and descent table in [class-a-carrier-closure-2026-10-22.md](class-a-carrier-closure-2026-10-22.md) are a useful **proof method**, not an imported d=2 theorem. The accepted two-sign geometry (#311), distinct even/odd d=2 carriers (#312), and their uniform real geometry/seed inclusion (#313) define the new proof target. Open #314 develops an all-child closure argument. The Akiyama–Lee, Minervino–Thuswaldner and Barge literature gate remains binding: neither finite overlap algorithms nor non-unit representation-space tiling facts provide this quantified descent.

For `sigma_n=(xy^(n+2)x,cy^nx,xy^(n+1)c)`, consider both parity candidates `C^even_n, C^odd_n` with 93 and 87 typed intervals. The pending theorem is a *parameter-dependent nonnegative integer potential* on every label in the candidate and a strictly decreasing **actual ordered child occurrence** from every non-target label, for every n in both parity rays. A rank assigned to the entire carrier is sufficient but stronger than a rank only on seed-reachable labels.

## Uniform obstruction to the simplest rank shape

Both parity templates contain the same three-point typed slice:

```
(top,bottom,s,y)=(x,x,0,0),   -1<=k<=1,
w=(k,-k,0).
```

Its existence and strict physical overlap for every even n>=8 and odd n>=7 are exactly the component obligations of #313. The k=0 label is an offset-zero target; k=-1 and k=+1 are non-target labels. Suppose one tries to normalize the target rank to zero and place **one affine-in-k rank** on the *entire* typed slice, `X_n(k)=A(n)+B(n)k`, with integer `X_n(k)>=1` at every non-target label (required by a nonnegative strictly descending potential that must still make at least one step). Target normalization gives `A(n)=X_n(0)=0`. But then

```
X_n(-1)=-B(n)>=1,    X_n(+1)=B(n)>=1,
```

which implies `0>=2`, impossible for every n. Thus **the target-normalized affine-single-piece strategy is refuted uniformly** for both parity candidates. At minimum that construction must split this typed slice at the target, use a nonlinear rank, or relax its normalization. It does **not** refute other affine rankings with nonzero target values, nor uniform productivity.

This is not merely a numerical observation: the algebraic contradiction is parameter-independent, and the exact source-row member conditions show the three candidate labels persist on both infinite rays. Canonical `uniform_centered_slice_obstruction` and the independent test guard the witness row.

## Exact finite descent evidence, retaining occurrence indices

For n=7,8,9,10,11,12, `kernel/psc/class_a_d2_descent_probe.mojo` builds the **complete** cap-refusing canonical exact graph. It obtains the true shortest first offset-zero distance from the shared graph kernel, recovers the *integral* Perron-length coordinates of every state, and rejects any nonzero-offset vertex lacking an actual adjacent vertex at depth `D-1`.

A separately written Python Fraction-field oracle reconstructs the entire graph, computes backwards breadth-first distances, and supplies an **explicit ordered occurrence** `(i,j)` for a child at depth `D-1` from every non-target state. It verifies the occurrence algebraically:

```
child_shift=beta*parent_shift+bottom_prefix(j)-top_prefix(i),
```

checks child types and strict positive interior geometry, refuses duplicate/missing parents or incorrect depth, and hashes the ordered witness list for reproducibility. This independent replay is stronger than counting reachable vertices or reporting a depth histogram.

| n | Complete states | Offset-zero targets | Nonzero states with chosen decreasing children | Maximum first-hit depth |
|---:|---:|---:|---:|---:|
| 7 | 231 | 8 | 223 | 5 |
| 8 | 265 | 8 | 257 | 5 |
| 9 | 271 | 8 | 263 | 6 |
| 10 | 305 | 8 | 297 | 6 |
| 11 | 311 | 8 | 303 | 7 |
| 12 | 345 | 8 | 337 | 7 |

These are **finite** complete graphs, not a claim about all n. The centered `(x,x,s=0,y=0)` three-point slice has shortest depths `(2,0,2)` at each of these parameters. It exhibits precisely why the full-row shortest-depth function is not a monotone affine function of k.

The independent oracle tests deliberately corrupt a chosen child occurrence index, claimed rank, or source coverage; each must refuse. The canonical test rejects a missing entire target slice, unknown n, incomplete graph, and nondecreasing child. No CI/graph cap is silently interpreted as a successful theorem.

## Concrete next mathematical and implementation steps

The appropriate next rank ansatz parallels the accepted gap-one potential **without copying its table**:

1. On each parity ray, partition every affine carrier row into finitely many **affine-in-`m=floor(n/2)` subintervals**. Split offset-zero targets into singleton pieces, including the central `k=0` target noted above.
2. Fit a candidate nonnegative integer potential `X(m,j)=a m+b j+c` on each piece from these complete finite graph distances (possibly via `D=floor(X/3)`), treating this fitting only as **candidate generation**.
3. For every non-target piece subinterval, choose an explicit FIRST/RUN/LAST occurrence pair, destination y-coordinate and destination piece. Preserve the full proper-prefix indices and residue-dependence `n=4ℓ+r` where divided run-index bounds require it.
4. Prove on each infinite residue ray that the chosen child is **real and realizable**, remains in the named destination piece, and has **`X_child<=X_parent-1`** throughout the entire subinterval. Use the existing exact d=2 Perron polynomial/Sturm or nonnegative-coefficient sign machinery. Refuse a crossing or incomplete certificate.
5. Only once the piece partition and every ordered descent are uniformly checked may d=2 boundary hitting be asserted, via the finite bases n=4..11 plus the four infinite rays. No general Class-A/C or #139/#84 promotion follows automatically.

This PR implements the **finite typed, ordered-edge evidence and obstruction/negative controls**, not steps 1–5's completed infinite-family proof. Fresh CI on the exact head is required before treating the implementation itself as accepted.

## Reproduction and receipts

Canonical Mojo: `kernel/psc/class_a_d2_descent_probe.mojo`, native test `kernel/tests/test_class_a_d2_descent_probe.mojo`, driver `kernel/class_a_d2_descent_probe.mojo`. Independent full graph and ordered-prefix witness: `oracles/python/class_a_d2_descent_probe.py` with `tests/test_class_a_d2_descent_probe.py`. The dedicated GitHub Actions workflow preserves fresh receipts.

```sh
python oracles/python/class_a_d2_descent_probe.py 7 8 9 10 11 12
python -m pytest -q tests/test_class_a_d2_descent_probe.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_d2_descent_probe.mojo
```

No governed theorem status is promoted by finite data. Class-D and the selected d=1 all-n hitting result remain accepted at their own scopes. The d=2 all-n child closure of #314 remains a prerequisite under validation, not an alternative to proving a descent.

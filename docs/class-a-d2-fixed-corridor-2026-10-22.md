# Class-A d=2: a uniform 80-state absorbing corridor (2026-10-22)

**Status:** repository-proved, scoped **exact coefficient/ordered-occurrence certificate**, with fresh locked CI acceptance and independent human review pending. Every one of the **80 explicitly listed integer-labelled physical overlaps** has an actual path to an offset-zero overlap in **at most four** inflation steps for every integer (n\ge4). **This does not establish that all 80 states are canonical swap-seed reachable for all n, or that all states in the parity carriers are productive.** General d=2 hitting, remaining class-A/C regions, #139/#84/#138/G1 and PSC remain open.

## Stop/go and the specific gap this addresses

The currently accepted gap-one family (#310) uses a 155-piece all-parameter descent. The d=2 parity carriers from merged #312/#313 have 93/87 typed intervals; open #314 implements all-child forward closure, while #315 records finite chosen descents and two uniform **two-step** paths on the central x/x slice. Its ranking negative control shows that a single affine rank normalized to zero at the center cannot cover the flanking states.

The targeted Akiyama–Lee / Minervino–Thuswaldner / Barge literature and hypothesis gate remains the one recorded in `docs/p1b-class-a-run-index-2026-10-21.md`. None of those imported theorems supplies uniform hitting for this non-unit family. Instead of fitting an unverified whole-carrier rank, isolate a **fixed, parameter-independent subset of the parity carriers** on which the expensive `n` term cancels from every selected inflation step. This produces a uniform *absorption target* for the remaining parity-piece ranking problem. It is not a new bounded-depth claim for the growing graph as a whole.

## Uniform algebraic setting

For every integer `n>=4`, fix

```
sigma_n(x) = x y^(n+2) x
sigma_n(c) = c y^n x
sigma_n(y) = x y^(n+1) c.
```

Use letters `(x,c,y)=(0,1,2)`. An overlap label is `(top,bottom,k,c,y)` with bottom-minus-top integral offset `w=(k,c,y)` and `s=k+c+y`. The incidence update before prefix differences is

```
M_n w = (k+s, s-k, n*s+2k+y).
```

The whole proposed corridor **lies in the exact hyperplane `s=0`**. Therefore the parameter-dependent term `n*s` vanishes **identically**. For all its vertices and all `n>=4`, the child of an ordered proper-prefix occurrence `(i,j)` with prefix-coordinate difference `delta=prefix_b(j)-prefix_t(i)` is

```
w_child = (k+delta_x, -k+delta_c, 2k+y+delta_y).
```

All chosen indices in the certificate belong to `{0,1,2,3,4}`. They are legal at every n>=4: every substituted word has at least four y positions, and the first five child types and proper-prefix vectors are uniform:

```
index 0: first x, except first c for the c parent; prefix = 0
index i=1..4: child y; prefix = first_letter + (i-1)*e_y.
```

Thus **every chosen child index and integral label identity is valid for all n>=4**, not simply at the source specimen.

## Uniform strict geometry for all 80 states

The positive Perron parameter `h=1/(beta-1)` satisfies

```
P_2(n,h)=1-(n+1)h-(n+2)h²-2h³=0.
```

Since `P_2(n,0)=1`, `P_2` is strictly decreasing on `h>0`, and `125 P_2(n,1/5)=88-30n<0` for n>=4, the physical root lies in `0<h<1/5`.

In the common positive scale, tile lengths are

```
L_x = 1+2h+2h²,  L_c=1,  L_y=1+h.
```

For `s=0`, the bottom-minus-top displacement is precisely

```
T(w)=(2k+y)h+2k h².
```

Each candidate label is a **strict real overlap** iff the two quadratic polynomials

```
L_bottom+T(w)>0,      L_top-T(w)>0
```

are both positive at the Perron root. Rather than evaluating at sampled roots, the canonical Mojo verifier computes the **160 exact quadratic margins** and their integer coefficient transform

```
25(1+t)² f(t/(5(1+t)))
   =25a+(50a+5b)t+(25a+5b+c)t²
```

for each `f(h)=a+bh+ch²`. It checks that **all three coefficients are nonnegative and at least one is strictly positive**. This proves each margin positive for every `0<h<1/5`; equality at an endpoint would not be credited. An independently written Python checker recomputes the same margins and signs directly from the immutable row data.

## Exact ordered descent certificate

The table `kernel/psc/class_a_d2_fixed_corridor_data.mojo` has exactly **80 nine-integer records**:

```
(top,bottom,k,c,y,rank,top_index,bottom_index,child_row_index).
```

A record with rank zero has exactly zero offset and no chosen successor; the eight such rows are *boundary-hitting targets* (not necessarily terminal equal-letter coincidences). Every other record names one actual ordered proper-prefix occurrence, with both indices in `0..4`, whose derived child equals the named destination's **entire five-coordinate typed label** and whose nonnegative integer rank is exactly one smaller.

The verifier checks **every row**, refuses any duplicate typed label, proves both strict geometric margins, verifies the exact parameter-independent child identity, and checks that ranks decrease. There are:

| Rank | Number of explicitly certified states |
| ---: | ---: |
| 0 (offset zero) | 8 |
| 1 | 20 |
| 2 | 26 |
| 3 | 22 |
| 4 | 4 |
| **Total** | **80** |

For each non-target state its chosen successor is a *strict real child* for every n>=4, and the integer rank decreases by one. By induction all 80 listed states reach one of the eight offset-zero targets in **at most four inflation steps for every integer n>=4**. No global bound is claimed for other states. The two centered paths already proved in #315 are contained in this larger uniform corridor.

### Relation to the formal even/odd carriers

The checker separately rebuilds the prior candidate tables from pinned exact source pairs `(8,12)` and `(9,13)`, and verifies for **each** of these 80 fixed labels that a matching typed interval contains it at the parity floor and has a **nonincreasing lower endpoint** and **nondecreasing upper endpoint** in `m=floor(n/2)`.

Consequently **every corridor state belongs to both formal parity candidates on the corresponding complete infinite rays** (even n>=8, odd n>=7). This statement concerns the *formal candidate sets*; it is **not** proof of uniform seed-reachability for each state. Exceptional n=4,5,6 are handled by the abstract all-n strict-margin and index proof itself; no parity-candidate membership at those small parameters is assumed.

## Discovery versus evidence, replay, and falsification

The 80-state set and descending edges were **discovered** using a complete exact graph at n=8, extracting its s=0 states and shortest paths that retain s=0 and use proper-prefix indices <=4. This discovery process is **not** the proof. The immutable certificate is entirely revalidated by algebraic child updates and all-n polynomial sign inequalities; no runtime graph is needed to establish its quantified conclusion. The independent Fraction-field oracle also differentially replays the 80 states and 72 ordered edges against complete exact graphs at n=4,8,9,12 (finite calibration only).

Canonical: `kernel/psc/class_a_d2_fixed_corridor_data.mojo`, `kernel/psc/class_a_d2_fixed_corridor.mojo`, driver `kernel/class_a_d2_fixed_corridor.mojo`, tests `kernel/tests/test_class_a_d2_fixed_corridor.mojo`. Independent oracle: `oracles/python/class_a_d2_fixed_corridor.py`, tests `tests/test_class_a_d2_fixed_corridor.py`. Dedicated locked CI: `.github/workflows/class-a-d2-fixed-corridor.yml`.

```sh
python oracles/python/class_a_d2_fixed_corridor.py
python -m pytest -q tests/test_class_a_d2_fixed_corridor.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_d2_fixed_corridor.mojo
```

Explicit negative controls: missing/duplicate state, corrupt chosen child, illegal prefix index, n-dependent offset sum, false rank decrease, forged zero-rank target, zero/negative margin (boundary contact not counted), failed parity-template inclusion, incomplete exact finite graph and unsupported finite parameter. The independent finite verifier includes all actual Q(beta) child types, ordered index prefixes and strictness, not merely adjacency counts.

**Fresh CI on the exact PR head is mandatory for repository acceptance**, and independent human review remains pending. This note does not promote any governed universal claim.

## Remaining d=2 proof obligation

The parity carriers grow linearly in n, while this uniform corridor has a fixed 80 states. Uniform forward closure (#314) and a uniform productive subgraph are not enough: a seed-reachable closed component could remain outside this corridor forever.

The next constructive target is an **affine-piece rank or universally quantified selected occurrence**, on **every remaining candidate interval**, whose child either reduces a nonnegative rank or reaches the 80-state absorbing corridor. Candidate pieces may depend on n mod 4 to preserve the integer ceil/floor run-position conditions of #314. Prove exact occurrence feasibility, strict real geometry, destination-piece membership and an integer potential drop uniformly over the full parameter ray. The rank can stop when it enters the 80-state corridor, and then inherit the separate depth bound <=4. This reduces the all-n d=2 hitting task without pretending to have completed it. Other A/C residual families and the general PSC remain open.

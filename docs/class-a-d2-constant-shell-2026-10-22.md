# Class A d=2: an all-parameter 518-state one-step shell into the productive core (2026-10-22)

**Status: scoped repository-proved mathematical certificate, new branch CI and independent human review pending.** The result concerns **598 explicitly listed constant integral overlap states**, not the entire parity-dependent carrier or general PSC. All 518 new states have a chosen actual ordered child into the 80 states of the already established uniform productive core; every listed state reaches offset zero in at most **five** steps for every integer n>=4. This is a quantified all-parameter physical-overlap statement, **not** a proof that all 598 labels are seed-reachable uniformly, nor that all d=2 seed-reachable labels are productive.

## Literature and parameter firewall

Continue the targeted non-unit hypothesis stop/go from [the class-A run-index analysis](p1b-class-a-run-index-2026-10-21.md) (Akiyama–Lee, Minervino–Thuswaldner and Barge); nothing about a global non-unit tiling, a strong-coincidence-to-pure-discreteness bridge, or independent tile-length realizations is imported. The specific accepted family is the class-A determinant-two plus-sign gap-two line

```
sigma_n(x)=x y^(n+2) x
sigma_n(c)=c y^n x
sigma_n(y)=x y^(n+1) c,      n>=4.
```

Merge dependency #314 proposes uniform all-child closure of a parity candidate. The fixed 80-state core from [the prior note](class-a-d2-fixed-corridor-2026-10-22.md) is separately productive by actual selected edges in at most four steps for every n>=4. The **new proof constructs one full symbolic inverse-inflation shell around that core**, without pretending the fixed set is automatically a forward-invariant or seed-reachable complete graph.

## Exact source and ordered child algebra

A state is `(top,bottom,k,c,y)` with bottom-minus-top integer displacement `w=(k,c,y)` and sum `s=k+c+y`. The correct integral incidence action is

```
M_n w=(k+s,s-k,ns+2k+y).
```

All 518 new records have **s=+1 or -1**, in equal numbers (259 each). Unlike the 80-state core (s=0), their n-dependence does not vanish *by itself*. The chosen ordered proper-prefix indices exploit the long y-runs.

Each chosen top and bottom zero-based index is

```
i=a_t*n+b_t,   j=a_b*n+b_b,
a_t,a_b ∈ {0,1}.
```

Indices with slope 0 are among 0..4; a slope-one index is `n+b`, with `-3<=b<=3` for x, `-3<=b<=1` for c, and `-3<=b<=2` for y. Every one of these is a legal proper-prefix position for **all** n>=4: either FIRST, a y-RUN position or the LAST position. The proper-prefix vector has constant x/c components, and its y-component is `a*n+(b-1)` for every positive index (0 if the index is zero).

Writing `delta=prefix_bottom(j)-prefix_top(i)`, the full child coordinate update becomes

```
k'=k+s+delta_x,
c'=s-k+delta_c,
y'=n*(s+a_b-a_t)+2k+y+b'_b-b'_t,
```

where `b'` is the constant y-prefix part (zero for a zero index). The selected occurrence pairs satisfy the **integer identity**

```
s+a_b-a_t=0
```

at **every one of the 518 rows**. Therefore each child label is independent of n and coincides coefficient-by-coefficient with the exact target record in the established 80-state core. Child letters are also checked: FIRST has x/c according to the parent first letter, RUN has y, LAST has x for x/c and c for y.

This proves not merely unlabelled adjacency but an **actual, specifically indexed, proper-prefix occurrence valid at every parameter**. Each chosen child's integer rank in the prior core is exactly one smaller than the new row's rank.

## Exact strict geometry, not an infinite numerical sample

The physical Perron root `h=1/(beta-1)` obeys

```
P_2(n,h)=1-(n+1)h-(n+2)h²-2h³=0
```

and `0<h<1/5` for every n>=4 by monotonicity and `125P_2(n,1/5)=88-30n<0`. In common positive scale, `L=(1+2h+2h²,1,1+h)`. For each new fixed offset the physical shift is a **quadratic**

```
T(w)=s+(2k+y)h+2k h².
```

Strict overlap is equivalent to *both* `L_bottom+T(w)>0` and `L_top-T(w)>0`. The canonical Mojo certificate checks **1,036 exact quadratic polynomial margins**. For every margin `f(h)=A+B h+C h²`, it checks the three integer coefficients of

```
25(1+t)² f(t/(5(1+t)))
  = 25A+(50A+5B)t+(25A+5B+C)t²
```

are nonnegative and at least one is positive. That proves f(h)>0 throughout the entire `0<h<1/5` interval, hence for **every integer n>=4**, not merely where complete exact graphs were sampled. A separate arithmetic read of the committed 518-row table found all 1,036 source strictness obligations and all 518 child identities valid with no undecided case; it is a supporting check, **not** a locked CI acceptance receipt.

## The complete fixed shell certificate

The table `kernel/psc/class_a_d2_constant_shell_data.mojo` contains **518 exact eleven-integer witness rows**:

```
[top,bottom,k,c,y,rank,top_index_slope,top_index_constant,
 bottom_index_slope,bottom_index_constant,core_child_row_index].
```

Every source has a distinct complete five-field label, offset sum `s=±1`, and rank 2..5. The canonical verifier refuses any duplicate, missing row, bad source rank, invalid parameter-dependent index, non-cancelled n-term, false child letter/offset, nondecreasing child rank, non-strict physical geometry, or damaged 80-state core. The prior core is *recertified*, not trusted solely by name.

The exact rank histogram of new shell states is:

| Rank | New one-step source states |
| ---: | ---: |
| 2 | 230 |
| 3 | 176 |
| 4 | 106 |
| 5 | 6 |
| **Total** | **518** |

Combined with the prior core's rank histogram (ranks 0..4: 8,20,26,22,4), there are now **598 distinct explicitly certified states**, since the core has s=0 and all shell states have s=±1. The maximum chosen path length for every shell state is its rank, hence at most **five** inflation steps to offset zero.

### How the candidates were found versus how they are proved

A finite reverse search over the 80 source-pinned core records, three parent letter types, and the bounded FIRST/near-end index forms solved the child-coordinate equations exactly and collected the 518 distinct, uniformly strict source labels. *Discovery is not the proof.* The final immutable table is independently checked by the full integer incidence/prefix equations and uniform Perron-margin certificates. The table contains all nine parent letter pairs, and 259 states for each source sum sign.

A separately written Python oracle reparses the immutable table and checks every uniform coefficient and complete chosen edge independently. It also performs **finite differential calibration** against the exact independent Q(beta) substitution engine at n=4,8,9: it constructs the displacement from the Perron tile-length vector even for candidate states that are not in the finite **seed-reachable** graph, evaluates the *actual* indices, and checks the exact field child and strict physical intersection. Those finite replays are implementation controls only; the all-n theorem rests on integer-algebraic identities and interval-wide signs.

## Replay and falsification

- Exact source data: `kernel/psc/class_a_d2_constant_shell_data.mojo`.
- Canonical certificate: `kernel/psc/class_a_d2_constant_shell.mojo`, driver `kernel/class_a_d2_constant_shell.mojo`, tests `kernel/tests/test_class_a_d2_constant_shell.mojo`.
- Independent arithmetic: `oracles/python/class_a_d2_constant_shell.py`; regressions: `tests/test_class_a_d2_constant_shell.py`.
- Dedicated locked workflow: `.github/workflows/class-a-d2-constant-shell.yml`.

```sh
python oracles/python/class_a_d2_constant_shell.py
python -m pytest -q tests/test_class_a_d2_constant_shell.py
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_d2_constant_shell.mojo
```

Negative controls damage an actual index beyond the LAST bound, introduce an n coefficient in an alleged constant child, change the chosen destination or rank, duplicate a state label, and inject a zero/negative margin; every such mutation must refuse. The independent field check compares entire typed child shifts, not graph membership guesses.

## Remaining mathematical objective

The new shell is a **productive subset**, not a complete carrier. It is not asserted to include every seed-reachable state, to be forward closed under *all* possible edges, or to satisfy the cardinality formulas of the parity carrier. Its usefulness is that a future parity-piece potential may *terminate early* whenever it enters any of these 598 certified productive states, with an added bound ≤5.

The next *all-n d=2 hitting theorem* still requires a complete, uniformly verified descent or bad closed-SCC exclusion for **every** canonical seed-reachable state in the growing parity carrier. New fixed corridors do not alone discharge that obligation, and no global #139/#84/#138, G1 or PSC promotion follows. Human independent review and locked GitHub Actions acceptance are pending.

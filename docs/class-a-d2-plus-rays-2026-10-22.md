# Class A d=2 plus line: boundary hitting for every n by the residue-ray certificate (2026-10-22)

**Status:** repository-proved, computer-assisted, scoped to the single
determinant-two class-A line `(n+2,n,n+1)`,

```text
sigma_n(x) = x y^(n+2) x,   sigma_n(c) = c y^n x,   sigma_n(y) = x y^(n+1) c,
```

for every `n>=1` (its whole determinant-two PIP domain except `n=0`, which
lies on the previously certified line `p=2q+2`); independent human review
pending. Every vertex of the complete canonical swap-seed overlap graph has an
offset-zero descendant. Other gaps `d>=4`, the class-C residual, universal
#139/#84/#138, G1 and PSC remain open. No ledger claim is promoted; the status
is that of the executable certificate.

This closes the objective left open by the d=2 parity-carrier program
([parity carrier](class-a-d2-parity-carrier-2026-10-22.md),
[uniform child closure](class-a-d2-uniform-child-closure-2026-10-22.md),
[descent obligations](class-a-d2-descent-obligations-2026-10-22.md), and the
open PRs #318/#319 with their 80- and 598-state productive subsets): a
parameter-dependent nonnegative potential strictly decreasing along an actual
ordered child from every nonzero-offset carrier state, on both parity rays.

## Stop/go

No new literature route: the Akiyama–Lee / Minervino–Thuswaldner / Barge
decision of [p1b-class-a-run-index-2026-10-21.md](p1b-class-a-run-index-2026-10-21.md)
covers all of determinant-two class A, and nothing is imported. The method is
the generic residue-ray certificate of
[class-a-residue-rays-2026-10-22.md](class-a-residue-rays-2026-10-22.md) (#321),
which is parametric in `(d, eps, r)` and left exactly this line untabulated
because the parity-carrier PRs owned it. The side-notes ledger records that
certificate, the gap-one potentials it generalizes, and the d=1 → d=2
non-transfer theorem; none of those forbids this route. Decision: **proceed**
by adding the two rays `(d,eps) = (2,+1)`, `r = 0,1`, to the shared registry
instead of continuing to grow fixed productive subsets.

## Work shown

### Assumptions and hypotheses

- Line `(n+2,n,n+1)`, i.e. class A with `q=n`, `p=n+2`, sign `s=+1`, gap
  `d=2`; its determinant-two PIP domain is `q>=0` (`1<=d<=2q+11`), checked by
  `ALine.check_domain`.
- Canonical swap seeds `(xc,cx)`, `(xy,yx)`, `(cy,yc)`, zero-based
  proper-prefix occurrence indices, bottom-minus-top integral offsets
  `w=(k,c,y)`, `s=k+c+y`, equal-letter offset-zero coincidences terminal and
  not inflated — exactly as in the gap-one and residue-ray notes.
- `h = 1/(beta-1)`, `P(n,h) = 1-(n+1)h-(n+2)h^2-2h^3`,
  `n h(1+h) = 1-h-2h^2-2h^3`, `L = (1+2h+2h^2, 1, 1+h)`,
  `T(w) = s + 2k h(1+h) + y h` (the `eps=+1, d=2` row of the residue-ray
  geometry; the Python verifier re-derives `P` from the incidence matrix).

### Derivation / reduction

Write `n = 2l + r`, `r in {0,1}`. The three facts of the residue-ray note
reduce each ray to the gap-one proof:

1. *Scaling.* `2(a l + b) = a n + (2b - a r)`, so every Perron sign is again
   the sign of `A(h) + n B(h)`; eliminating `n` by the identity above leaves an
   integer polynomial in `h` whose sign on `(0, 1/n0]` an exact Sturm count
   decides (`n^3 P(n,1/n) = -2n^2-2n-2 < 0` puts `h_n` there for `n>=n0`).
2. *Child index.* `M w = (k+s, s-k, n s + 2k + y)`, so for a fixed child
   `y'` the realizable row indices are `j in [ceil(./2), floor(./2)]`, affine
   in `l` because every y-run has `l`-slope 2 (a non-divisible slope refuses).
3. *Monotonicity.* `T'` increases in `j` (slope `2h(1+h)`) and in `y'`
   (slope `1+h`), so the window, gap and endpoint arguments apply.

Then Theorem A (forward closure: every actual ordered child of every
non-terminal carrier label lies in the carrier, or is proved non-interior) and
Theorem B (an `l`-affine nonnegative potential `X` on 149 / 141 pieces with
`depth <= floor(X/3)`, and for every non-target piece a chosen occurrence
whose child lies in a named piece with strictly smaller `X`) hold on each ray
from its floor.

| ray | floor | rows / slices | `|C_n|` | closure covered / gaps / windows | pieces / targets / descents | depth `<=` |
| --- | ---: | --- | --- | --- | --- | --- |
| `n=2l` | 14 | 93 / 82 | `40l+105 = 20n+105` | 3,576 / 3,100 / 1,674 | 149 / 8 / 207 | `2l+9 = n+9` |
| `n=2l+1` | 13 | 87 / 80 | `40l+111 = 20n+91` | 3,378 / 2,942 / 1,566 | 141 / 8 / 186 | `2l+11 = n+10` |

Both rays: 9 real seeds in the carrier, 3 non-strict seed candidates, 65
terminal splits, no conservative clip, and one slack-fitted row (`r=1`, row 83:
`depth <= floor(X/3) <= depth+1`, the dominate-and-drop relaxation recorded for
the minus line).

**Theorem (d=2 plus line).** For every integer `n>=1`, every vertex of the
complete canonical swap-seed overlap graph of `sigma_n` has an offset-zero
descendant. For `n>=14` even (`n>=13` odd) the first such descendant is at
depth at most `n+9` (`n+10`).

*Proof.* For `n` at or above its ray's floor: Theorems A and B on that ray —
the seed graph lies in the carrier, and the potential strictly decreases along
chosen actual children until an offset-zero target. For `1<=n<=12`, below
both floors: the exact complete graph, cap not reached, every
first-hit depth finite. ∎

The ray rows *are* the #312 parity carriers, as exact affine tables:
`carrier_is_parity_template` in `kernel/psc/class_a_d2_plus_line.mojo`
compares them row for row and coefficient for coefficient with
`psc.class_a_d2_parity_carrier.inferred_template(8,12)` and `(9,13)` (affine in
`m = floor(n/2) = l`). The independent Fraction-field oracle agrees with the
ray rows at `n = 8,9,12,13` (`tests/test_class_a_d2_plus_ray_carrier.py`).
Hence the 80- and 598-state productive subsets of #318/#319 lie inside
carriers now proved productive in full; they remain correct but are no longer
load-bearing for this line.

### Shown in Mojo: one command per part, one receipt per part

The whole argument is assembled by one canonical Mojo driver,
`kernel/class_a_d2_plus_line.mojo` (module `psc.class_a_d2_plus_line`):

```sh
cd kernel
pixi run --locked mojo run -I . class_a_d2_plus_line.mojo theorem
pixi run --locked mojo run -I . class_a_d2_plus_line.mojo witness 14
```

`theorem` prints one receipt per proof part, in proof order:

| receipt | what it establishes |
| --- | --- |
| `SUMMARY n …` ×12, `D2P_FINITE_BASE n=1..12` | exact complete graphs, cap-refusing, every vertex hits (max first-hit depth 7) |
| `CLASS_A_CARRIER_CLOSURE n>=14 … n=2l+0` | Theorem A on the even ray |
| `CLASS_A_CARRIER_DESCENT n>=14 … hit_depth_bound 2l+9` | Theorem B on the even ray |
| `D2P_FLOOR_LEAST r=0 floor 14 refused_at 12` | the certificate refuses at the preceding ray member 12 (its closure line prints, then descent stops at an undecided sign) |
| `D2P_CARRIER_IS_PARITY_TEMPLATE r=0 rows 93 identical=true` | even ray carrier = #312 even template |
| the same four for `r=1`, floor 13, refused at 11 | odd ray |
| `CLASS_A_D2_PLUS_LINE_BOUNDARY_HITTING n>=1 …` | the theorem, printed only after every part passed |

`witness N` (`13 <= N <= 24`; below the floor the evidence is the exact
graph) instantiates the certificate at one `n` and prints every step:

```text
W 14 (0,0,0,1,-2) X 9 piece 0 --(0,17)-> (0,0,0,-1,0) X 6
…
SEED 14 (2,2,0,-1,0) --(0,16)-> (0,1,0,-1,1) --(2,1)-> (2,2,-1,1,0) --(0,3)-> (0,2,0,1,0) --(16,0)-> (2,0,0,1,-1) --(1,2)-> (2,2,0,0,0) steps 5
D2P_WITNESS 14 labels 385 targets 8 graph_vertices 385 seeds 9 longest_seed_path 5 longest_chain 11 hand_checked_steps 377
```

A label is `(top,bottom,k,c,y)` with letters `x,c,y = 0,1,2`. Each `W` line is
a carrier label, its potential `X`, its piece, the chosen ordered occurrence
`(i,j)` (zero-based indices into `sigma_n(top)`, `sigma_n(bottom)`) and the
child with its potential. Each line is checked twice:

1. by the exact Perron-field engine (`descent_witnesses_line` in
   `psc.class_a_carrier_descent`: the occurrence is an actual ordered child,
   both ends strict, `X' <= X-1`); and
2. by hand (`hand_step`), from the integral incidence identity alone:
   `w' = (k+s, s-k, n s+2k+y) + prefix(sigma(bottom), j) - prefix(sigma(top), i)`,
   with child letters `sigma(top)[i]` and `sigma(bottom)[j]`.
   For the first line above: `s = 1-2 = -1`, `i = 0`, and `j = 17` is the final
   `x` of `x y^16 x`, whose prefix has abelianization `(1,0,16)`. So
   `w' = (0-1+1, -1-0+0, -14+0-2+16) = (0,-1,0)` with letters `(x,x)`.

The witness then checks that the label set equals the vertex set of the exact
complete graph. It follows every chosen chain to an offset-zero target, refuses
any chain longer than its potential, and prints the path of each of the nine
canonical swap seeds. Archived traces: `evidence/class-a-d2-plus-rays-2026-10-22/witness/`
for every `n = 13..24` (5,598 hand-checked steps in all). CI rebuilds the
driver and `diff`s `theorem` and every witness against the archive.

### Evidence and replay

From `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_class_a_d2_plus_line.mojo
pixi run --locked mojo run -I . tests/test_class_a_residue_rays.mojo
pixi run --locked mojo run -I . class_a_residue_ray.mojo certify 2 1 0 14
pixi run --locked mojo run -I . class_a_residue_ray.mojo certify 2 1 1 13
pixi run --locked mojo run -I . class_a_residue_ray.mojo survey 2 1 30
```

From the repository root:

```sh
python oracles/python/class_a_carrier_closure.py 14 --ray 2,1,0
python oracles/python/class_a_carrier_closure.py 13 --ray 2,1,1
python -m pytest -q tests/test_class_a_residue_rays.py tests/test_class_a_d2_plus_ray_carrier.py
(cd evidence/class-a-d2-plus-rays-2026-10-22 && sha256sum -c SHA256SUMS)
```

Tables: `kernel/psc/class_a_ray_d2p.mojo` (generated, a proof *target*);
registry: `kernel/psc/class_a_ray_tables.mojo`. Packet:
`evidence/class-a-d2-plus-rays-2026-10-22/`. The Mojo certificate and the
independent Python verifier report identical closure and descent counts on
both rays; the existing CI workflow `class-a-residue-rays.yml` iterates the
registry and therefore runs both new rays.

### Negative controls

The shared native and Python suites apply, per tabulated ray: a removed carrier
row escapes closure; the other residue's carrier does not fit; a raised child
potential, a mislabelled child `y'` and a missing descent row refuse. The new
calibration test checks that the odd carrier differs from the `n=12` profile.
`tests/test_class_a_d2_plus_line.mojo` refuses a corrupted child coordinate
or letter and a shifted occurrence index in `hand_step`, a witness below
either floor, and a third residue, and fails if a floor stops being least. Below the floors the
certificate refuses rather than concluding: `certify 2 1 0 12` and
`certify 2 1 1 11` pass closure and stop at an undecided Sturm sign (root
inside `(0,q]`) in descent; generating the even descent table from `n=10`
leaves two incomparable clipped pieces and the generator refuses ("incomplete
descent table"). These are fail-closed outcomes, not counterexamples.

### Non-claims / remaining gaps

Only the line `(n+2,n,n+1)`. Gaps `d>=4` of class A, the class-C residual
`d>=4`, aligned #138, universal #139/#84, G1 and PSC are open. The finite
formulas and the carrier = #312 profile coincidence are observations at the
listed `n`; the generator is not evidence. Not Lean-formalized; locked CI on
the PR head and independent human review pending. PRs #318/#319 are not closed
or altered by this note.

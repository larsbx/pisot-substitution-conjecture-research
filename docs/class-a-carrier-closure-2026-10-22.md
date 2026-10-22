# Class A: uniform carrier closure and descent on the line (n+1, n, n+1) (2026-10-22)

**Status:** repository-proved, computer-assisted, scoped to the determinant-two
class-A line `(p,q,r)=(n+1,n,n+1)` for every integer `n>=4`; independent human
review pending. Every reachable overlap state of this line has an
offset-zero descendant: the strict-zipper obligation of #139 is discharged on
this one-parameter family. The other class-A regions, the class-C residual,
universal #139/#84, G1 and PSC remain open. No ledger claim is promoted by this
note; the status above is the status of the executable certificate.

## Stop/go before implementation

The targeted literature decision of
[p1b-class-a-run-index-2026-10-21.md](p1b-class-a-run-index-2026-10-21.md)
(Akiyama–Lee, Minervino–Thuswaldner, Barge) stands: no finite overlap
decision, Archimedean contraction or initial-letter theorem supplies a
uniform family argument here, and nothing is imported from them. The repository
precedent for the method is the class-D symbolic closure of
[p1b-class-d-minus-recurrent-carrier-2026-10-19.md](p1b-class-d-minus-recurrent-carrier-2026-10-19.md)
§14.3 and `kernel/psc/class_d_boundary_template.mojo`: nine first/run/last
segment pairs, exact signs, a derived child window. The new ingredients are
(a) an unbounded integer index inside every carrier row, handled by affine
forms in `n` and in the row index, and (b) the elimination of `n` from every
Perron inequality through `n h(1+h) = 1-h-h^2-h^3`, which turns each margin
into one integer polynomial whose sign an exact Sturm count decides on a
whole interval. The explicit obligation came from
[class-a-typed-carrier-2026-10-21.md](class-a-typed-carrier-2026-10-21.md):
all-n seed inclusion, strict geometry, all-child closure, then a
parameter-dependent descent for every state. Decision: **proceed** with
exactly that target. The [rectangle countermodel](class-a-cover-obstruction-2026-10-21.md)
is the standing negative control: a cover that forgets letter types or offset
correlations is not child-closed, so every check below is at label level.

## Setting

Letters `(x,c,y)=(0,1,2)`, images

```text
sigma_n(x) = x y^(n+1) x,   sigma_n(c) = c y^n x,   sigma_n(y) = x y^(n+1) c,   n >= 4.
```

The incidence matrix and Perron root are those of the run-index note:
`f_n(t)=t^3-(n+4)t^2+(n+4)t-2`, `beta in (n+2,n+3)`. Put `h = 1/(beta-1)`.
Substituting `beta = 1 + 1/h` and multiplying by `h^3`,

```text
P(n,h) = h^3 + (n+1) h^2 + (n+1) h - 1 = 0,     hence     n h (1+h) = 1 - h - h^2 - h^3.
```

`P(n, 1/(n+2)) < 0 < P(n, 1/(n+1))` gives `1/(n+2) < h_n < 1/(n+1)`; in
particular `0 < h_n <= 1/(n0+1)` for every `n >= n0`.

Tile lengths (left Perron eigenvector), scaled by `1+h` and normalized at the
y tile, are `L = (L_x, L_c, L_y) = (1+h+h^2, 1, 1+h)`; the three residuals
`h (M^T L)_j - (1+h) L_j` all equal `P(n,h)`, which binds `L` to this line.
A state is `(top, bottom, w)` with an integral bottom-minus-top offset
`w=(k,c,y)`, `s=k+c+y`; its scaled displacement is

```text
T(w) = (1+h) * (ell . w) = s + k h(1+h) + y h,
```

and the state is a strict overlap iff `-L_bottom < T(w) < L_top`. These are
exactly the signs `interior_overlap` decides in `Z[beta]`; the scaling is a
positive constant. The carrier is the 89-row table of
`kernel/psc/class_a_typed_carrier.mojo`: a row `(top,bottom,s,y,a,b,c,d)`
contains the labels with `k = a n + b + j`, `0 <= j <= J`, `J = (c-a)n + (d-b)`,
and `c = s - k - y`. Rows of one typed slice `(top,bottom,s,y)` are disjoint.

## Three decision lemmas

**Lemma 1 (elimination of n).** For integer polynomials `A, B` and every `n`,
`sign(A(h_n) + n B(h_n)) = sign(Q(h_n))` with
`Q = A(h) h(1+h) + (1-h-h^2-h^3) B(h)`, since `h(1+h) > 0`.

**Lemma 2 (interval sign).** Let `Q` be an integer polynomial, `q = 1/(n0+1)`.
Strip the factors of `h` (positive on the interval). If `Q(q) != 0` and the
Sturm count of `Q` on `(0, q]` is zero, then `sign Q(h_n) = sign Q(q)` for
every `n >= n0`. If either condition fails the sign is *undecided* and the
certificate refuses: no sign is ever inferred from a sample.

**Lemma 3 (affine ray).** For affine forms `u = u_1 n + u_0`, `v`: `u <= v`
for every integer `n >= n0` iff `u_1 <= v_1` and `u(n0) <= v(n0)`; `u > v`
for every such `n` iff `u_1 >= v_1` and `u(n0) > v(n0)`; otherwise the order
changes on the ray and the comparison is refused.

Lemma 1 is an identity; Lemma 2 is Sturm's theorem on `(0,q]` (the vendored
`count_roots_in`); Lemma 3 is monotonicity of an affine function of an integer.

## Symbolic ordered occurrences

**Lemma 4 (children of a carrier label).** Let `(t,b,w)` be a label with
`T(w)` as above and let `R(x)=R(y)=n+1`, `R(c)=n` be the run lengths. The
proper prefixes of `sigma(t)` fall into three segments: FIRST (empty prefix;
child letter `x` for `t in {x,y}`, `c` for `t=c`), RUN (prefix = first letter
then `m` copies of `y`, `0 <= m <= R(t)-1`; child letter `y`) and LAST
(prefix = first letter then the whole run; child letter `x` for `t in {x,c}`,
`c` for `t=y`). Write `pi_x, pi_c in {0,1}` for the first-letter counts of a
prefix and `m` for its y count. For an occurrence pair with top segment
`(pi_x^t,pi_c^t,m_t)` and bottom segment `(pi_x^b,pi_c^b,m_b)`, the child is
`(t', b', w')` with

```text
k' = k + s + (pi_x^b - pi_x^t),     c' = s - k + (pi_c^b - pi_c^t),
y' = k + n s + y + (m_b - m_t),     s' = 2 s + (pi_x^b+pi_c^b-pi_x^t-pi_c^t) + y',
```

because `M w = (k+s, s-k, k+ns+y)`. The child displacement
`beta T(w) + pos_b - pos_t` equals `T(w')`, and the child is an ordered
occurrence of the exact merge scan iff it is a strict overlap. Conversely,
for fixed segments, `y'` is attained iff `m_b - m_t = y' - (k+ns+y)` lies in
the integer interval `[m_b^min - m_t^max, m_b^max - m_t^min]` of the two
segments (all intermediate differences are realized by run positions), so
*realizability* of `y'` is an affine-in-`n` interval condition on `j`.

Proof: `w' = M w + pi(prefix_b) - pi(prefix_t)` is the shared affine update
of `selected_overlap_child`; the three segments exhaust the image positions
`0`, `1..R`, `R+1`; `T(M w) = beta T(w)` since `L` is a left eigenvector.
`check_symbolic_edge` of the run-index note checks this identity
coefficient by coefficient, and `replay_descent_finite` compares every
chosen child with the exact engine at `n = 8, 11` (below).

## Theorem A: uniform forward closure

**Theorem A (uniform carrier closure).** For every integer `n >= 5`: (i) every
label of the 89-row carrier is a strict overlap; (ii) each of the nine strict
seed overlaps of the three oriented swap pairs is a carrier label, and the
other three seed candidates are not strict overlaps; (iii) every ordered child
occurrence of every non-terminal carrier label is a carrier label. Hence the
complete swap-seed graph `G_n` is contained in the carrier `C_n`. For
`n >= 8` the certificate needs no conservative interval clip.

**Status:** repository-proved (exact executable certificate
`kernel/psc/class_a_carrier_closure.mojo`, independently re-proved by
`oracles/python/class_a_carrier_closure.py`; independent human review pending).
Containment `G_n ⊆ C_n`, not label-set equality, is what is proved for
arbitrary `n`; equality holds at the exact finite graphs `n = 4..24`.

Proof. Fix `n0 in {5, 8}` and `q = 1/(n0+1)`; every sign below is decided by
Lemmas 1–2 on `(0,q]`, every comparison by Lemma 3.

(i) On a row, `T` is affine in `j` with positive coefficient `h(1+h)`, so
`-L_b < T < L_t` on `0 <= j <= J` iff it holds at `j = 0` and `j = J`: two
polynomial sign pairs per row, 178 in all.

(ii) The twelve candidates `(a,b,0)`, `(a,a,e_b)`, `(b,b,-e_a)`, `(b,a,e_b-e_a)`
have constant labels; nine are strict for every `n >= n0`, three are not for
any such `n`, and membership of the nine is an affine check.

(iii) Fix a row, a segment pair and the child type it determines. The child
displacement is `T' = 2s + delta + y'(1+h) + k' h(1+h)` with `k' = k_0 + j`,
affine increasing in `y'` (slope `1+h`) and in `j` (slope `h(1+h)`).
*Window.* At `y' = +6` the child is at or beyond its right boundary for
`j = 0` and `j = J`, hence for all `j`, hence for all `y' >= 6`; at `y' = -6`
it is at or before its left boundary likewise: 1,602 sign checks. So only
`|y'| <= 5` can be real. *Gaps.* For each such `y'`, the realizable `j` form
an affine interval (Lemma 4), intersected with `[0,J]`; the carrier rows of
the child slice `(t',b',s',y')` cut it into covered intervals and *gaps*. On
a gap the child must not be strict: since `T'` is affine increasing in `j`,
it suffices that at the gap's upper end `T' + L_{b'} <= 0` or at its lower
end `L_{t'} - T' <= 0`. The coincidence `(t,t,0)` is terminal and is split out
of every gap of its row. Every one of the 8,811 `(row, segments, y')` cases
closes: 3,802 (n0=8) or 3,947 (n0=5) have a realizable range, and all of their
3,334 (resp. 3,479) gaps are excluded by geometry; 65 gaps are split at a
terminal. A single real child in a gap would be an *escape* and the
certificate raises. (When two realizability endpoints are incomparable on the
ray below `n0 = 8`, the range is widened to `[0,J]`, which only adds gaps to
exclude: 277 such clips at `n0 = 5`, none at `n0 = 8`.)

By induction on the inflation depth, every state reachable from a seed is a
carrier label. ∎

| Count | `n0 = 8` | `n0 = 5` |
| --- | ---: | ---: |
| rows / row-member sign pairs | 89 / 178 | 89 / 178 |
| segment pairs / `(row, segments, y')` cases | 801 / 8,811 | 801 / 8,811 |
| cases with a realizable range / gaps excluded by geometry | 3,802 / 3,334 | 3,947 / 3,479 |
| window sign checks / terminal splits | 1,602 / 65 | 1,602 / 65 |
| real seeds in carrier / non-strict seed candidates | 9 / 3 | 9 / 3 |
| conservative interval clips | 0 | 277 |

The certificate refuses at `n0 = 4`: the terminal index of a row then enters a
gap for some `n` and not others, which Lemma 3 cannot decide. Those members
are covered by the exact finite certificates below.

## Theorem B: uniform descent to offset zero

A *piece* is an affine sub-interval `[lo(n), hi(n)]` of the index range of
one carrier row with an integer potential `X(n,j) = a n + b j + c`. The 155
pieces of `kernel/psc/class_a_descent_data.mojo` partition every row; eight
of them are *targets*, the single offset-zero labels `w = 0` of the rows
with `s = y = 0` (three coincidences and five unequal-letter zero offsets).
A *descent row* names, for an affine sub-interval of a non-target piece, one
symbolic child occurrence (top segment, bottom segment, `y'`) and the piece
of the child; the 221 descent rows partition every non-target piece.

**Theorem B (uniform descent).** For every integer `n >= 8` and every
non-target carrier label, the child occurrence named by its descent row is
realizable, is a strict overlap, is a label of the named child piece, and
satisfies `X_child <= X_parent - 1`; and `X >= 0` on every piece. Consequently
every carrier label reaches an offset-zero label after at most `X <= 2n + 9`
inflations.

**Status:** repository-proved (exact executable certificate
`kernel/psc/class_a_carrier_descent.mojo`, independently re-proved by the
Python oracle; independent human review pending). The bound `2n+9` is the
proven potential; the exact first-hit depth is observed to be
`floor((2n+9)/3)` at `n = 8..24`, a finite observation only.

Proof. Partition and non-negativity are affine checks (Lemma 3) at the piece
ends. For a descent row with parent sub-interval `[s_lo, s_hi]`: the child's
letters and `s'` are forced by Lemma 4 and must equal the child row's; the
child index `j' = j + Delta` with `Delta` affine, so containment in the child
piece is two affine checks; realizability is two affine checks; strictness
of parent and child is linear in `j` and is decided at `j = s_lo` and
`j = s_hi` by Lemmas 1–2; and `X_parent(j) - X_child(j+Delta) - 1` is affine
in `(n, j)`, non-negative on the sub-interval iff non-negative at its two
ends for every `n >= 8` (Lemma 3). `X` is a non-negative integer that
strictly decreases along the chosen children, so the chosen path from any
label reaches a label with no descent row, i.e. a target, in at most `X`
steps; `X <= 2n+9` is the maximum of the piece potentials at their ends
(slope 2, value 25 at `n = 8`). ∎

How the tables were made, and why that is not the proof: on the exact graphs
`n = 8..24` the first offset-zero depth of each row equals `floor(X/3)` on
affine pieces (it is *not* affine on a row: period-three plateaus), the target
is split into its own piece, and for each piece one child type was chosen that
lowers `X` at every sampled member, splitting where the child's piece changes.
`oracles/python/class_a_descent_table.py` regenerates the tables from the
exports; the Mojo module is byte-identical to its output. The tables are a
quantified proof target that the two verifiers discharge for all `n >= 8`.

## Corollary C: boundary hitting on the whole line

**Corollary C (class-A line boundary hitting).** For every integer `n >= 4`,
every state reachable from the three oriented swap seeds in the exact overlap
graph of `sigma_n` has an offset-zero descendant: within `2n+9` inflations for
`n >= 8`, and within `5, 6, 7, 7` inflations at `n = 4, 5, 6, 7`.

**Status:** repository-proved (Theorems A and B for `n >= 8`; for `n = 4..7`
the exact finite certificate `certify_finite(n)` of the typed-carrier module,
which builds the complete graph without reaching its cap, checks label-set
equality with the carrier and finds every first-hit depth finite; independent
human review pending). This closes the strict-zipper obligation on this line
only. It is consistent with the proven `L(A_n) > n/10`: the depth genuinely
grows linearly, and no parameter-independent bound exists.

## What is and is not established

- Established: for the line `(n+1,n,n+1)`, `n >= 4`, no reachable overlap
  state is zero-shift-free forever; every recurrent component has a
  productive exit of length at most `2n+9`.
- Not established: the remaining class-A domains (`d = p - q >= 2`, the minus
  sign, other `q`), the class-C residual `d >= 4`, universal #139/#84, aligned
  #138, G1 or PSC. Containment `G_n ⊆ C_n` is proved; equality is finite.
- Not changed: the accepted class-D scope and receipts, and the run-index,
  cover-obstruction and typed-carrier results, which this note depends on.
- Not promoted: no `claim_governance.toml` claim or ledger record; the test
  declares a contract. A ledger record is for the integration step once the
  dedicated CI receipts exist.

## Evidence and replay

Canonical Mojo: `kernel/psc/class_a_carrier_closure.mojo` (Lemmas 1–4 and
Theorem A), `kernel/psc/class_a_carrier_descent.mojo` (Theorem B and the
finite differential replay), `kernel/psc/class_a_descent_data.mojo` (tables),
driver `kernel/class_a_carrier_closure.mojo`, regression
`kernel/tests/test_class_a_carrier_closure.mojo`. Independent oracle:
`oracles/python/class_a_carrier_closure.py` (own Fraction Sturm chains and
affine comparisons), `tests/test_class_a_carrier_closure.py`. Generator:
`oracles/python/class_a_descent_table.py`. Packet:
`evidence/class-a-carrier-closure-2026-10-22/` (logs, exit codes, oracle
output, generated table, source digests, runtime identity, `SHA256SUMS`).
Dedicated CI: `.github/workflows/class-a-carrier-closure.yml`.

```sh
cd kernel
pixi run --locked mojo run -I . tests/test_class_a_carrier_closure.mojo
pixi run --locked mojo run -I . class_a_carrier_closure.mojo 8
cd ..
python oracles/python/class_a_carrier_closure.py 8
python -m pytest -q tests/test_class_a_carrier_closure.py
sha256sum -c evidence/class-a-carrier-closure-2026-10-22/SHA256SUMS
```

Local runs use the lock-matched `Mojo 1.1.0.dev2026090805 (34562fa1)`
(compiler SHA-256 `0d5f0b70…`, the accepted class-D compiler); the receipts
in the packet are from that runtime, not from a fresh full Pixi install or a
CI run. The dedicated workflow produces the locked receipts.

## Negative controls

- Lemma 2 refuses a polynomial with a root inside `(0,q]` (`-1 + 10h` on
  `(0,1/5]`) and one vanishing at the bound (`-1 + 5h`); Lemma 3 reports the
  crossing of `n-4` and `1` on the ray from `5` as undecided.
- Theorem A at `n0 = 4` refuses (terminal membership varies with `n`); a
  carrier with one row removed is an escape, not a smaller theorem.
- Theorem B refuses a raised child potential (no drop), a negative potential,
  a removed descent row, a child `y'` off by one, a wrong child piece, and a
  descent row attached to a target piece. Raising the potential of a piece
  that no descent enters is *not* a control and is recorded as such.
- `replay_descent_finite(n)` at `n = 8, 11` matches every chosen child
  occurrence against `ordered_child_occurrences` of the exact engine by
  segments and label, checks the potential drop numerically, and that every
  non-target label is covered by exactly one descent row.
- The rectangle witness `V_n` of the cover-obstruction note is absent from
  the carrier for every `n`, consistent with Theorem A: its typed slice
  `(x,c,s=1,y=-2)` has no row.

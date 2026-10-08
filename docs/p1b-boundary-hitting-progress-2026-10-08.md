# P1b: boundary hitting at every reachable strict-zipper vertex — progress, 2026-09-21 → 2026-10-08

**Status:** status synchronisation for issue #139. It also adds one
computer-assisted result in the style of Theorem L′ (Theorem L″, §4): 32
infinite families with pure discrete spectrum and finite BPA, unreviewed. No ledger node or manuscript statement changes. #84, #138, #139,
G1 and PSC stay open.

Canonical implementation for §4: `kernel/symbolic_line_certificate.mojo`
(now any line of Theorem E's four classes), regression
`kernel/tests/test_symbolic_line.mojo`, evidence workflow
`.github/workflows/class-b-lines-evidence.yml`.

## 0. The obligation, stated once

For PIP `sigma` on three letters, let `Reach(s)` be the overlaps reachable from
the swap seed `s`, and let `L(x)` be the first offset-zero depth of `x`
(`∞` if there is none). Issue #139 asks for

    AllSeedStrictZipperExclusion(sigma):  ∀ s ∀ x ∈ Reach(s).  L(x) < ∞,

which is *boundary hitting at every reachable strict-zipper vertex*. A vertex
with `L(x) = ∞` lies above a closed SCC with no offset-zero vertex. That SCC is
case (b) of manuscript Proposition `prop:zipper-dichotomy`, the strict zipper.
Its realization-free form is

    BH(sigma):  every potential overlap on a cycle has L < ∞.

What it buys (all recorded, with their review status):

| from | to | by |
| --- | --- | --- |
| `AllSeedStrictZipperExclusion` | G1 (finite BPA) | `G1HalfCoincidenceRoute` (Prop. `prop:G1-from-half-coincidences`) |
| `BH ∧ SC_all` | FP, hence PDS | Proposition FP (#211) |
| `BH` | `PPVC` | Proposition V (#211; rests on Theorem B) |
| `PDS` | `BH` | Theorem S + Corollary FP″ (#211) |

So `BH ⟺ PPVC`, and BH and PDS are equivalent wherever `SC_all` is known.

## 1. What the recent PRs did for it

In order of landing. "Advance" means a change in what is proved, what is
reduced, or what is excluded as a route. Census-only rows are labelled as
such.

| PR | Date | What it does for #139 | Kind |
| --- | --- | --- | --- |
| #141 | 09-21 | Literature gate. Names the residual obligation `AdelicPeriodicOffsetHitting`. Compactness, multiple tiling, Perron-criticality and the Archimedean projection alone are excluded. | scoping |
| #181 | 10-01 | M-adic carry theorem. Descaled zero-class candidates obey `z' = M z + pi(q) − pi(p)`, the overlap affine update itself. So quotient-depth sieving cannot close #139 on its own. | stop result |
| #211 | 10-04 | Proposition V / Theorem B: `BH ⟺ PPVC` on a finite box automaton. Proposition FP: `FP ⟺ SC_all ∧ BH`. Corollary FP″: `FP ⟺ PDS`. #139 becomes realization-free, and decidable per specimen. | reduction |
| #227 | 10-07 | Theorems E, H, K: `SC_all` on the catch-up-free `\|det M\| = 2` class, outside part of Theorem K's family `F`. Corollary C3: there, #138's A1′ and #139's T2 are **the same** boundary-hitting statement. Proposition LC: the leftmost-chain (`CU`) route cannot reach #139, whose obstruction is interior-vs-interior (Theorem B). | reduction, redirect |
| #231 | 10-07 | Adversarial audit of Proposition V and Theorem E. No disproof, no failing step. | review |
| #232 | 10-08 | Proposition Z: on the class (outside `F`'s open part) `PSC ⟺ PPVC`, so the strict zipper is *the* problem there. Survey: PPVC on 358 parametric members, depth ≤ 14, not growing. **Theorem L:** BH from every seed on the infinite class-B line `p = 2q + 2, r = q + 1`, so PDS and G1 for all of it. This is the first infinite family on which #139's obligation is proved. | **theorem on an infinite family** |
| #233 | 10-08 | Theorem Ω: BH plus `SC_all` on the box gives PDS through Lee–Moody–Solomyak plus Proposition V step 1, which is elementary. So the finite-domain BH verdicts no longer rest on Theorem B. `BoundedPureDiscreteSpectrum` holds on 145,806 specimens. | finite-domain theorem |
| #234 (open) | 10-08 | Theorem SC: one productive seed ⟺ every seed ⟺ FP ⟺ PDS. Choosing the seed gives no slack, only a different object. **Theorem L′:** fourteen more class-B lines. | theorem on 14 families |
| this note | 10-08 | **Theorem L″:** the same certificate on 32 lines of classes A, C and D. Class A at slope 1 is recorded as out of reach of the constant-graph method. | theorem on new families |

Summarised: on 2026-09-21 #139 was an adelic hitting problem with no
decision procedure. Today it is:

1. **decidable per specimen** (PPVC on the box, #211). The decision rests on
   elementary facts and an import (#233).
2. **the whole of PSC** on the catch-up-free `|det M| = 2` class, outside
   `F`'s open part (#232).
3. **proved on infinitely many infinite families**: lines of Theorem E's classes
   (#232, #234, §4). It is not proved on any two-parameter region.

The universal statement is untouched. No uniform-in-`|S|` mechanism has been
found, and the acceptance criterion of #139 is not met.

## 2. What stays settled negatively

Do not re-attempt any of these. Each is recorded with its evidence.

- Cycle algebra, affine pumps, bounded collars, generic Perron growth, the
  contracting lower bound (issue body; side-notes ledger §1).
- Quotient-depth (M-adic) sieving without a coverage theorem (#181).
- The `CU` / leftmost-chain route (#227, Proposition LC). Its obstructions
  are prefix-vs-interior and harmless.
- Picking a better seed (#234, Theorem SC). It changes the object, not the
  truth.
- A parametric BPA. Its states grow exponentially along lines (#232 §3).
  Use the overlap graph, whose vertices are bounded.

## 3. Where the line method stands

The method of `p1b-symbolic-line-2026-10-07.md` §2 decides one line from its
**seed** graph, symbolically in the line parameter. It needs a seed graph of
constant size along the line, with constant offsets. That held on every line
of Theorems L and L′. Where it fails, the method raises or exhausts its
budget. It never certifies a false graph (Lemma S).

Exact seed-graph sizes (scratch probe through `exact_hits`, not pinned) show
which lines the method can reach:

| line (`p`, `q`, `r`) | exact seed-graph size at the sampled `n` |
| --- | --- |
| B `(n + 1, n, n + 1)` | 121 at `n = 3, 6, 10, 14, 20` |
| A `(n + 1, n, n + 1)` | 235, 355, 515, 675, 915 at `n = 3, 6, 10, 14, 20` |
| A `(n + 1, n, n − 1)` | 300, 458, 618, 778 at `n = 4, 8, 12, 16` |
| A `(n + 3, n, n + 1)` | 138, 178, 254, 294 at `n = 4, 8, 12, 16` |
| A `(3n, n, n + 1)` | 276, 324, 294, 302 at `n = 4, 8, 12, 16` |
| A `(2n + 1, n, n + 1)` | 198, 194, 194, 194 at `n = 4, 8, 12, 16` |
| C `(n + 1, n, n)` | 169 at `n = 4, 8, 12, 16` |
| D `(n + 1, n, n)` | 246 at `n = 4, 8, 12, 16` |
| D `(n + 1, n, 2n)` | 93 at `n = 4, 8, 12, 16` |

In **class A at slope 1** the seed graph grows linearly in `n`. At
`p = n + 1` it grows by about 40 vertices per unit of `n` on both branches,
and at `p = n + 3` more slowly. The one-parameter method needs a symbolic
graph of constant size, so it cannot certify these lines. The four lines
`p = n + 1, n + 2`, `r = n ± 1` were stopped after 12 CPU-minutes each
without output. That is an exhausted budget, not a verdict. At slope 2, and
in classes C and D, the graph is constant from small `n` on, and §4
certifies those lines.

## 4. Theorem L″: lines of classes A, C and D

The driver took class-B lines only. It now takes any line of Theorem E's
normal form,

    sigma(x) = x y^p s_x,   sigma(c) = c y^q s_c,   sigma(y) = t y^r s_y,

in class A, B, C or D (endings from `class_ending`), with `p, q, r` affine
in `n`:

    mojo run -I . symbolic_line_certificate.mojo CLASS AP BP AQ BQ AR BR

Here `p = AP·n + BP`, and likewise for `q` and `r`. Old invocations and pins
are unchanged: no argument runs Theorem L, `SLOPE K BRANCH` runs a class-B
line, and `lines` runs every pinned line. Below the threshold, the parameters
counted as outside are those leaving the normal form (`p, q, r ≥ 0`), and, in
classes A–C, those violating Lemma P1's necessary PIP condition `p > q`.
These are the same parameters the class-B driver already skipped.

*Theorem L″.* For each line below, every PIP member is catch-up-free with
`|det M| = 2`, and every overlap reachable from any of its three swap seeds has
an offset-zero descendant. So every member has all-pairs strong coincidence
(Corollary E2, which covers all four classes), productivity of every
seed-reachable overlap (Corollary `cor:scc-reduction`(ii)), **pure discrete
spectrum** (Theorem `thm:main-density`), and a **finite balanced-pair
automaton** (Proposition `prop:G1-from-half-coincidences`). Status as for
Theorem L: computer-assisted, unreviewed, resting on Theorem E (unreviewed)
and on the imported Barge–Štimac–Williams theorem. The literature gate of
`p1b-catch-up-free-ppvc-2026-10-07.md` §3 governs, and the novelty claim is
as narrow as Theorem L's: no source in that gate proves pure discrete
spectrum for these families. Barge (2018) could reach a member only through a
conjugacy to a β-substitution, which is not checked here.

| class | `p` | `q` | `r` | symbolic vertices | threshold `q0` | below `q0`: PIP, all hitting / not PIP / outside | sign reads | wall-clock (four lines at a time on four cores) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| A | `2n` | `n` | `n − 1` | 281 | 39 | 38 / 0 / 1 | 7,722 | 184 s |
| A | `2n` | `n` | `n + 1` | 210 | 20 | 19 / 0 / 1 | 6,356 | 80 s |
| A | `2n + 1` | `n` | `n − 1` | 365 | 87 | 85 / 1 / 1 | 10,590 | 829 s |
| A | `2n + 1` | `n` | `n + 1` | 194 | 19 | 19 / 0 / 0 | 5,808 | 110 s |
| A | `2n + 2` | `n` | `n − 1` | 325 | 107 | 104 / 2 / 1 | 9,846 | 1107 s |
| A | `2n + 2` | `n` | `n + 1` | 230 | 52 | 52 / 0 / 0 | 6,590 | 294 s |
| A | `2n + 3` | `n` | `n − 1` | 303 | 128 | 124 / 3 / 1 | 9,418 | 1674 s |
| A | `2n + 3` | `n` | `n + 1` | 260 | 14 | 14 / 0 / 0 | 7,370 | 110 s |
| C | `n + 1` | `n` | `n − 2` | 279 | 36 | 33 / 1 / 2 | 6,792 | 101 s |
| C | `n + 1` | `n` | `n` | 169 | 17 | 17 / 0 / 0 | 4,026 | 64 s |
| C | `n + 2` | `n` | `n − 3` | 238 | 37 | 32 / 2 / 3 | 6,276 | 112 s |
| C | `n + 2` | `n` | `n − 1` | 182 | 23 | 22 / 0 / 1 | 4,572 | 64 s |
| C | `n + 3` | `n` | `n − 4` | 229 | 39 | 32 / 3 / 4 | 6,376 | 124 s |
| C | `n + 3` | `n` | `n − 2` | 188 | 36 | 34 / 0 / 2 | 5,184 | 96 s |
| D | `n − 1` | `n` | `n − 1` | 150 | 22 | 19 / 2 / 1 | 3,782 | 41 s |
| D | `n − 1` | `n` | `n` | 128 | 17 | 15 / 1 / 1 | 3,066 | 34 s |
| D | `n − 1` | `n` | `n + 1` | 111 | 26 | 23 / 2 / 1 | 2,958 | 32 s |
| D | `n − 1` | `n` | `n + 2` | 105 | 38 | 34 / 3 / 1 | 3,018 | 42 s |
| D | `n − 1` | `n` | `n + 3` | 105 | 43 | 38 / 4 / 1 | 3,130 | 51 s |
| D | `n − 1` | `n` | `n + 4` | 105 | 97 | 91 / 5 / 1 | 3,130 | 212 s |
| D | `n − 1` | `n` | `2n − 3` | 105 | 14 | 11 / 1 / 2 | 3,160 | 47 s |
| D | `n − 1` | `n` | `2n − 2` | 113 | 12 | 10 / 1 / 1 | 3,256 | 40 s |
| D | `n + 1` | `n` | `n − 1` | 250 | 24 | 23 / 0 / 1 | 5,718 | 58 s |
| D | `n + 1` | `n` | `n` | 246 | 19 | 19 / 0 / 0 | 5,402 | 66 s |
| D | `n + 1` | `n` | `n + 1` | 181 | 21 | 21 / 0 / 0 | 4,198 | 54 s |
| D | `n + 1` | `n` | `n + 2` | 132 | 22 | 22 / 0 / 0 | 3,418 | 34 s |
| D | `n + 1` | `n` | `n + 3` | 97 | 18 | 17 / 1 / 0 | 2,870 | 22 s |
| D | `n + 1` | `n` | `n + 4` | 93 | 49 | 47 / 2 / 0 | 2,886 | 62 s |
| D | `n + 1` | `n` | `2n − 1` | 93 | 22 | 21 / 0 / 1 | 2,944 | 47 s |
| D | `n + 1` | `n` | `2n` | 93 | 15 | 15 / 0 / 0 | 2,912 | 63 s |
| D | `n + 1` | `n` | `2n + 1` | 113 | 14 | 14 / 0 / 0 | 3,416 | 49 s |
| D | `n + 1` | `n` | `2n + 2` | 193 | 10 | 10 / 0 / 0 | 5,882 | 76 s |

**32 new lines**: 8 in class A, 6 in class C, 18 in class D. With the 15 class-B lines of Theorems L and L′, 47 lines are pinned in `certified_lines()`. Each was run once through the committed driver, one core each, and every cross-check passed. Each row is pinned in `certified_lines()` and re-run by the evidence workflow; `tests/test_line_certificate_workflow.py` keeps the workflow matrix equal to the pin list. The regression `test_a_class_d_line_is_certified` re-certifies the class-D line `(n + 1, n, n + 3)` on every test run.

**Refusals, all correct.** The certificate refused five more lines at the PIP step, and each is outside the Pisot class:

- class D, `p = n − 1`, `q = n`, `r = 2n + b` for `b = 0, 1, 2`: a second eigenvalue of modulus above 1 (exactly 1 at `b = −1`);
- class D, `p = n + 1`, `q = n`, `r = 2n + 3`: a second eigenvalue of modulus 1;
- class D, `p = n + 1`, `q = n`, `r = 3n` and `3n + 1`: a second eigenvalue of modulus about 1.3.

(Float spectra at `n = 20, 80`, as a scratch diagnosis of the refusals; the refusal itself is the exact certificate's.) No PIP line of classes C or D that was tried failed to certify.

## 5. Next, in order

1. **Two-parameter wedges.** On each class, the vertex counts settle along every
   certified line, and they do so for each offset `k`. Making `k` symbolic
   gives sign queries over `Q[n, k]`. This needs a cylindrical
   decomposition in two variables, not the eventual-sign reader. The first
   target is the class-B wedge `n + 1 ≤ p ≤ 2n + 4` (#234 §7.1).
2. **Growing seed graphs (class A, slope 1).** The vertices come in families
   indexed by a run position `0 ≤ j ≤ n`. The symbolic object is a vertex
   *family* `(a, b, w_0 + j·u)`, with children decided uniformly in `j`. This
   is Theorem H's parametric witness paths applied to vertices, not only to
   witnesses.
3. **The uniform mechanism.** Every certified line so far has hitting depth
   ≤ 14 and a bounded seed graph. A uniform depth bound `K` on the
   catch-up-free `|det M| = 2` class would make BH there a finite statement
   about `M^K w ∈ D_K(i, j)` (#232 §5.2). That is the first statement in this
   programme of the uniform kind #139's acceptance criterion asks for.

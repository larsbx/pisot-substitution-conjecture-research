# Minus class-A chamber: stop/go for entry into Z and H (#452), and the cone theorem on 𝒯_CA — 2026-11-15

**Status:** one theorem, repository-proved, computer-assisted, human review
pending: Theorem CA (§6), boundary hitting from the nine swap seeds on
`𝒯_CA = {t ≤ 5} ∪ {t ≤ k − 1}`. It is not registered in the claim ledger, like
Theorem C. With it come the elementary lemmas TW, I1–I3, R and the Transfer
Lemma (§3–§4), written proofs whose finite regressions are in
`kernel/tests/test_class_a_chamber_entry.mojo`, and the literature and route
stop/go decision of §2 and §5. Corollary CA-1 (§6.4) gives #452's entry into Z and H on
`𝒯_CA` and nowhere else. On `main` the complement `{t ≥ 6, t ≥ k}` stays an
open theorem target; a written proof covering the whole chamber exists on the
unmerged #577 stack (§2, "Parallel route"), and Theorem CA is independent of it.

Canonical implementation: `kernel/psc/symbolic_cone.mojo` (with an opt-in
Bernstein sign rule), `kernel/class_b_cone_certificate.mojo` (the cover, now
generic in the class), driver `kernel/class_a_chamber_cone_certificate.mojo`
(`pixi run class-a-chamber-cone-certificate`), regression
`kernel/tests/test_class_a_chamber_entry.mojo`, hosted workflow
`.github/workflows/class-a-chamber-entry.yml`, run log
`evidence/class-a-chamber-cone-2026-11-15/`.

**Labels.** [R] read and checked at the locator given; [D] derived here; [F]
finite observation, never universal; [U] not verified. Status lines are quoted
verbatim and never upgraded. `ledger:N` is `docs/side-notes-ledger.md` line N
as of `71afd61`. **Notation.** Offsets are `w = (w_x, w_c, w_y)`, bottom minus
top full Parikh vectors. Run lengths are `(R_x, R_c, R_y) = (A, n, n−1)`.
`(q, p)` are used only for Theorem C's twin coordinates `q = n`, `p = A`.
`γ = (1,3,−6)`, `K = k+1`, `D = ⌊(n−1)/K⌋`, `ρ = (n−1) mod K`; class B's
`l = ⌊n/K⌋` and residue `r₀ = n mod K`. The lemma names TW and I1–I3 avoid
the existing Lemma T (`docs/p1a-a1-prime-2026-10-05.md:605`) and Corollary E2
(`:624`).

## 1. The exact claim

**Objects** [R].
- Family (`docs/class-a-uniform-zero-return-2026-11-02.md:11-15`): `k,t ≥ 0`,
  `n = k+t+3`, `d = k+2t+5`, `A = n+d`, `σ(x) = x y^A x`, `σ(c) = c y^n x`,
  `σ(y) = x y^(n−1) c`, letters `x = 0`, `c = 1`, `y = 2`.
- Child edge: `(a,b,w) →_(i,j) (σ(a)_i, σ(b)_j, Mw + P_b(j) − P_a(i))`,
  `0 ≤ i ≤ R_a+1`, `0 ≤ j ≤ R_b+1`, with `P_a(0) = 0` and
  `P_a(i) = e_f(a) + (i−1) e_y` for `i ≥ 1`, `f(x) = f(y) = x`, `f(c) = c`
  (`kernel/psc/class_a_boundary_children.mojo:135-183`). It is admitted iff the
  child is strict, `−L_b < L·w < L_a` (`kernel/psc/class_a_x_productivity.mojo:100-121`,
  `interior_overlap_cached` at `:117`).
- `S9 = nine_sources()` (`kernel/psc/class_a_x_productivity.mojo:38-43`),
  `R(a,b,w) = (b,a,−w)`, `S18 = S9 ∪ R(S9)`. `Γ_(k,t)` is the forward closure
  of S18 with typed coincidences `(e,e,0)` terminal (`:34-35`).
- `Z := {v ∈ Γ : w(v) = 0}`, any letters (integral zero). `H :=` the nonzero
  vertices of Γ on the nine segments `W_(a,b)(m) = (a, b, δ, m−(d+1)δ, −m+dδ)`,
  `−R_b ≤ m ≤ R_a` (`docs/class-a-uniform-zero-return-2026-11-02.md:80-82,96`).

**T1 (open theorem target off 𝒯_CA).**

```text
∀ k,t ∈ Z≥0  ∀ v ∈ V(Γ_(k,t))  ∃ m ≥ 0  ∃ v = v_0 →_(i_1,j_1) v_1 → … →_(i_m,j_m) v_m :
   every step is an actual strict indexed child edge of Γ_(k,t),
   w(v_m) = 0 in Z³ (letters arbitrary), and w(v_s) ≠ 0 for every s < m   (first hit).
```

- *All vertices, transient ones included*: "The graph's transient sources and
  all actual children must be accounted for" (`docs/bh-escape-roadmap-2026-11-14.md:190`);
  T1 implies the roadmap's cyclic form (`:92-94`) [D]. The #452 ledger entry
  makes the same point (ledger:2855).
- *Integral, not physical, zero*: "Zero physical length alone is not integral
  zero" (`:156-157`). On this family the two agree (I2 below), but certificates
  test `w = 0`.
- *Corollary T1-H* [D, §4.4]: for `v ∉ Z`, `v_(m−1) ∈ H`, with `i_m, j_m ≥ 1`
  and `i_m − j_m ∈ [−R_b, R_a]`. This is the forward half of the zero-return
  reduction T0. T0's status reads "**Status:** proposed, mathematically derived
  parameter-uniform **one-step** family lemma; native and independent-oracle
  acceptance required." (`docs/class-a-uniform-zero-return-2026-11-02.md:3`),
  and it has no governed record. §4.4 proves the forward half independently.
- *Corollary T1-BH* [D, given T1 and I2]: both per-σ forms of BH at
  `docs/quantifier-transfer-audit-2026-11-09.md:327-334`. The positive form holds
  because `G9 ≅ Reach_Γ(S9) ⊆ Γ`. The exclusion form holds because a reachable
  child-closed non-coincidence set containing `v` contains `v`'s first-hit path.
  It is stated for chamber members only.
- *Not covered:* the plus chamber; minus members outside the chamber; classes
  B, C and D; universal BH #139, A1′ #138, #84, G1, PSC; the non-unit
  realization dictionary (`docs/class-a-uniform-zero-return-2026-11-02.md:130,134`);
  Lean adapters and #574's consumer form.

## 2. Prior art and the literature gate

| # | Source | Role | Transfer to this det −2 PIP family |
| --- | --- | --- | --- |
| L1 | Berthé–Bourdon–Jolivet–Siegel, ETDS 36 (2016) 1757–1794, arXiv:1401.0704 (`docs/p1a-swap-family-literature-gate-2026-10-06.md:33`) | closest construction: one finite certificate for an infinite family | "**no.** Discrete planes and dual substitutions need unimodularity, and class A has determinant two. The idea of a finite combinatorial certificate covering an infinite family does carry over" (`docs/class-a-gap-uniformity-stopgo-2026-10-23.md:23`) |
| L2 | Barge, *The Pisot conjecture for β-substitutions*, ETDS 38 (2018) 2009–2034, arXiv:1505.04408 (`docs/p1b-barge-diamond-configuration-gate-2026-10-02.md:31`) | strongest relevant theorem: PDS for the β-substitution "of **every** Pisot β, unit or not … Only through a conjugacy of tiling spaces" (`docs/p1b-catch-up-free-ppvc-2026-10-07.md:63`) | `σ` is not in β-substitution form. Conjugacy was probed in scratch only, at `(k,t) = (0,0)`, with negative results within the searched classes, and is not excluded (ledger:3059) |
| L3 | Barge, DCDS-A 36 (2016) 1159–1173, Theorem 3.13, arXiv:1403.7826 (`docs/sadic-transfer-literature-gate-2026-10-11.md:31`) | endpoint-class boundary | fails: "Class A has initial map `(x,c,x)`, hence is not injective; no power repairs this collision." (`docs/p1b-class-a-run-index-2026-10-21.md:32-33`) |
| L4 | Akiyama–Lee, Adv. Math. 226 (2011) 2855–2883 (`sources/issue-84/references.bib:1-12`) | per-substitution overlap decision | "Neither a family-uniform depth nor seed-graph realization follows merely from this algorithm." (`docs/p1b-class-a-run-index-2026-10-21.md:23-24`) |
| L5 | Hollander–Solomyak, two-symbol PDS (`docs/branch-b-prefix-suffix-literature-gate-2026-10-19.md:138`) | two-letter boundary | excluded: three letters, trace `n+2 ≥ 5` (`docs/class-a-gap-uniformity-stopgo-2026-10-23.md:25`) |
| L6 | Balková–Klouda–Pelantová, arXiv:1007.2724 | the critical-exponent formula behind the R-β sketch | [U]: not read; cited by no repository gate |

**Hypotheses that transfer** [R]: L2–L4 need no unimodularity ("No
unimodularity, no irreducibility", `docs/coincidence-rank-imports-literature-gate-2026-10-04.md:36-37`).
Primitive irreducible Pisot with `|det M| = 2` holds chamber-wide (Lemma TW).
**Hypotheses that fail** [R]: unimodularity and a fixed generator set (L1);
β-substitution form (L2); initial-letter injectivity (L3); two letters (L5); a
uniform contraction margin, since `−1 < λ_− < −1+(k+2)/n`
(`docs/class-a-boundary-layer-2026-10-26.md:23-27`, a "new candidate lemma,
not repository-governed", `:7`; its numerator is Mojo-checked in the chamber
kernel, `docs/class-a-boundary-chamber-2026-10-26.md:19-30`).
**Decision:** proceed with a narrowed target. No listed source states
coincidence or PDS for this chamber, so the method (a parametric overlap-graph
certificate) is the repository's own.

**Repository prior class-A art on this chamber** (compiled with verbatim status
lines in the stop/go scratch; summarized here):

| Group | PRs | Gives | Status (verbatim) or receipt |
| --- | --- | --- | --- |
| spectral obstruction, sign cone and `symbolic_child`, Parikh–cubic bridge | #346, #347, #438 | tooling | bridge: "scoped algebraic arithmetic theorem for the *minus class-A* normal form, with a Mojo-first checked-in contract and an independently executed exact Python reference. Native Mojo CI and independent review pending." (`docs/class-a-parikh-cubic-bridge-2026-10-31.md:3`) |
| ~40 per-label complete-star families | #348–#426, through #445 | selected exits, local stars; never coverage | "auditable inventory and finite replay, not a theorem about complete boundary hitting" (`docs/class-a-boundary-consolidated-frontier-2026-10-31.md:3-4`) |
| X-hub: `Reach(S18) = Reach(X) ∪ {E,R(E)}` | #428–#435 | reduction | "The universal minus-class-A conclusion depends on the *unaccepted* all-parameter certificates in #428, #430, #431 and #432." (`docs/class-a-oriented-swap-closure-2026-10-31.md:3-5`) |
| X-strips `S(z,s,p)`, `P_p`, `Z(p,s,u)`, `A_m`; `D` and exits of at most `4D+6` edges | #436, #440 | selected exits; "not a proof that all X descendants enter the cell" | body text, no status line (`docs/class-a-x-signed-strip-2026-10-31.md:6-16`) |
| finite S18 certificates (22 specimens) | #447, #448 | finite | hosted run 41448531108 passed at `4ec572a` (`evidence/class-a-finite-hosted-acceptance-2026-11-02/README.md:3-6`) |
| nine segments and T0; M-adic ladder; Smith trichotomy | #451, #453, #454 | target side | ladder: "parameter-uniform elementary integral-algebra theorem and canonical finite-level verifier **proposed**" (`docs/class-a-madic-digit-ladder-2026-11-02.md:3`); receipts: #451's dedicated run passed and its broader run failed, #453's and #454's exact-head runs failed (`docs/current-state-reconciliation-2026-11-11.md:124-127`) |

None of these is a parameter-uniform coverage result. Theorem CA is the first
on `main`.

**Parallel route, not on `main`** [R, PR bodies as of 2026-11-15]. The draft
stack of #577 contains, merged into its branch and not into `main`, PR
[#578](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/578) "Prove uniform minus-Class-A entry with original prefix
witnesses". Its body states "a written proof of the **mathematical
uniform-entry target of #452 throughout its declared minus-Class-A chamber**"
(`n+2 <= d <= 2n-1`, the chamber here): every strict integral overlap reaches
typed coincidence for `n >= 6`, and every vertex of the six complete S18 graphs
does for `n < 6`, with "Exact-head hosted acceptance and independent human
review remain pending". Its method is different: two-level literal word counts
force a central `y/y` overlap, a nearest RUN child gives a bounded integer
recurrence whose nonzero periodic tails are alternating states, and explicit
actual exits close those. Five of its Lean source modules reached `main`
through #583 (`ClassACentralRecurrence`, `ClassAZeroDefectEscape`, and the
constant-recurrence modules), the entry theorem and its note did not. If that
stack lands, Theorem CA is a second, independent and computer-assisted method
on `𝒯_CA` (cones and seed-patch graphs against density counts and a nearest
recurrence), and R-A below is superseded as the route to #452. Nothing of the
stack is cited as a premise here, and this note does not assess its proof.
**Class-B programme on the same matrix:** Theorem C ("Status: repository-proved,
computer-assisted, unreviewed.", `docs/p1b-symbolic-cone-2026-10-08.md:146-147`,
no governed record); the ray and middle certificates (`docs/class-b-middle-certificate-2026-10-27.md:3-5,16-19`,
"No governed claim or general PSC premise is promoted"); and the governed
`ClassBTopLayerLabelRays`, status `evidence` (`claim_governance.toml:301-308`).
None of these discharges anything for class A.
**Novelty, restricted** [R grep of `docs/`, `kernel/`, `oracles/`; U beyond
grep]: (a) the twin identification of Lemma TW; (b) Theorem CA and its
Bernstein rule; (c) the reading of Theorem L″'s rays `A 2 2 1 0 1 -1` and
`A 2 3 1 0 1 -1` as the chamber rays t = 0 and t = 1. **Not new:**
- `γ` and the bounded basis `3w_x+w_c+w_y`, `w_c−3w_x`: class A at `docs/class-a-x-cross-strip-2026-10-31.md:79`, class B at ledger:1957;
- `L·γ = −K/(β+1)`: class A's `v = 1−ρ−3h = K/(beta+1)`, `docs/class-a-x-transfer-plane-2026-10-31.md:23`;
- the coordinate `D`: `docs/class-a-x-signed-strip-2026-10-31.md:11`;
- χ, irreducibility, `β ∈ (n+2, n+3)` and primitivity: `docs/class-a-boundary-chamber-2026-10-26.md:9,15-18,36-39`, built in `Q[t,k]` by `kernel/psc/class_a_boundary_signs.mojo`;
- physical zero equals integral zero: `docs/class-a-parikh-cubic-bridge-2026-10-31.md:73`.

**Ledger read:** 1452-1462, 1848, 1900-2215, 1925, 1957, 1959, 1975, 2039, 2177, 2855, 3059; 2216-3058 scanned for `class-a`, `#452`, `cone`, `chamber`.

## 3. Lemma TW (the twin geometry)

`substitution_incidence` returns "`M[i][j]` = number of occurrences of letter `i`
in `sigma(j)`" (`kernel/psc/bpa.mojo:112-114`): column `j` is the Parikh vector
of `σ(j)`, and `Mw = (2w_x+w_c+w_y, w_c+w_y, A w_x+n w_c+(n−1) w_y)`.

**Lemma TW** [D]. For all `k,t ≥ 0`, with `K = k+1`:
1. `A = 3n − K`. The chamber member is `class_member(CLASS_A, 3n−K, n, n−1)`;
   its twin `class_member(CLASS_B, 3n−K, n, n−1)` lies on class B's minus line
   `(3q−g, q, q−1)` (`docs/class-b-ray-certificate-2026-10-27.md:7,50-53`) at
   `g = K`, `q = n`. The map `(k,t) ↦ (g,q)` has image `{g ≥ 1, q ≥ g+2}`.
   Theorem C's top-layer part of those lines (`docs/class-b-top-layer-stopgo-2026-10-23.md:16-18`)
   is `{t ≥ 6, t ≥ k−5}` in chamber coordinates.
2. Both members have `M = [[2,1,1],[0,1,1],[3n−K, n, n−1]]`.
3. `χ(λ) = λ³ − (n+2)λ² − (t+3)λ + 2`, `det M = −2`, χ irreducible, roots in
   `(−1,0)`, `(0,1)`, `(n+2,n+3)`; every chamber member is PIP (class-A prior
   art cited in §2).
4. With `L_y = 1`, `L = (β − n − 1/β, 1 + 1/β, 1)`, `LM = βL`,
   `L_x > L_c > L_y`; hence one strictness predicate and one S9 for the twins.
5. `Mγ = −γ − K e_y` and `L·γ = −K/(β+1)`.
6. The children differ: for a parent letter `y` the child letter at index 0 is
   `x` (A) against `c` (B), at LAST `c` (A) against `x` (B), and
   `P_y^A(i) − P_y^B(i) = e_x − e_c` for `i ≥ 1`. Witness: the seed `(x,y,0)`
   has the child `(x,x,0)` at `(0,0)` in class A, which is no class-B child
   of it.

*Proof.* (1) `3(k+t+3) − (k+1) = 2k+3t+8 = n+d`. (2) The images differ only
in `σ(y)` (`kernel/a1_normal_form_census.mojo:183-184,189-193`); the Parikh
vectors `(2,0,A)`, `(1,1,n)`, `(1,1,n−1)` are the columns in both classes. (3)
`tr M = n+2`; the principal minors sum to `2 + (2(n−1)−A) − 1 = −(t+3)`;
`det M = −2`. The rational-root candidates ±1, ±2 give `χ(1) = −d`,
`χ(−1) = −K`, `χ(2) = −2A`, `χ(−2) = −2(2k+t+10)`, all nonzero;
`χ(n+2) = 2 − (t+3)(n+2) < 0 < (n+3)(k+3) + 2 = χ(n+3)`; every entry of `M²` is
positive. (4) Column c: `L_x + L_c + n = β + 1 = β L_c`; column y:
`L_x + L_c + n − 1 = β`; column x: `2L_x + A = β L_x` ⟺ `χ(β) = 0`.
`L_c − L_y = 1/β`, `L_x − L_c = β − n − 1 − 2/β > 3/5`. Strictness and the
seeds read only `L` and the letters (§4.3). (5)
`Mγ = (−1, −3, A+3n−6n+6) = (−1, −3, 6−K)`, and
`β(β+1)(L·γ) = β³ − (n+2)β² − (n+1)β + 2 = −Kβ` mod χ. (6) Endings
`(X,X,X,C)` and `(X,X,C,X)` (`kernel/a1_normal_form_census.mojo:190-193`) and
the prefix rule of §1. ∎

**Regression** (`test_lemma_tw_over_q_k_t`): builds both cones over
`(s1, s2) = (k, t)` and checks in `Q[k,t]` that `M`, χ and the left Perron
vector `ell` (the engine's cross-product form) coincide for the twins, that χ
is the displayed cubic, that `Mγ = (−1, −3, 6−K)` and that
`(β+1)⟨ell, γ⟩ + K ell_y ≡ 0` mod χ, and that the twins' exact seed graphs
differ at `(0,0)` and `(12,6)`.

**What transfers:** `M`, χ, β, `L`, strictness, S9, the bracket proposals of
the cone cover (they read only `M`), and class B's middle sign geometry
`h = 1/β`, `v = gh` (`docs/class-b-middle-certificate-2026-10-27.md:46-52`) at
`g = K`. **What does not:** the child relation and class B's Lemma 4
(`kernel/psc/class_b_ray_certificate.mojo:9-18`); `WINDOW = 6` (`:52`); the
strict-core box (`docs/class-b-gap-uniformity-stopgo-2026-10-27.md:47-50`); the
anchored band (`:122-128`); every carrier and potential table. **Firewall,
both directions:** "no class-A result is used to discharge a class-B
obligation" (`docs/class-b-middle-certificate-2026-10-27.md:172`), and
conversely. The twin pins share `Q0` and PIP counts but not vertex counts:
`line B 2 2 1 0 1 -1 107 255 104 2 1` against `line A 2 2 1 0 1 -1 107 325 104 2 1`
(`kernel/symbolic_line_pins.txt:40,46`).

## 4. The transfer lemma

**Definitions.** `G9_(k,t)` is the forward closure of the strict contacts of the
patches `ab/ba` (`a < b`) under the physical strict child relation, with
`is_coincidence` terminal: the mathematical object of Lemma S/S′ and of
`overlap_seed_patch` (`kernel/psc/overlap_seed_patch.mojo:32-49,253-273`).
`HIT9(k,t)`: every vertex of `G9_(k,t)` has an offset-zero descendant.
`φ := geometric_state` (`kernel/psc/class_a_boundary_children.mojo:225-232`),
which is `(a,b,w) ↦ (a,b,λ L·w)` for the common positive scale `λ` of the
tables.

**4.1 I1 (symbolic certificate ⟹ HIT9).** If a line or cone closure finishes
on a region and every symbolic vertex has an offset-zero descendant, then
`HIT9` holds at every integer point of the region.
*Proof.* Every decision of the closure is a sign certified on the whole region
(Lemma S, `docs/p1b-symbolic-line-2026-10-07.md:70-78`; Lemma S′,
`docs/p1b-symbolic-cone-2026-10-08.md:93-98`; Lemma S″ below for the Bernstein
rule), so at each point `s` substitution maps symbolic seeds onto exact seeds
and the children of each non-terminal image onto the images of its children.
Every exact vertex is therefore an image. A symbolic path to offset zero maps
to an exact path that either reaches offset zero or meets an exact typed
coincidence first, which is itself offset zero. This uses surjectivity only:
a symbolic vertex `(e,e,w(s))` with `w ≢ 0` and `w(s0) = 0` is harmless. ∎

**Lemma S″ (the Bernstein rule).** Let `[L, U]` be a certified bracket of β
on a region (denominators certified positive, `L < U`, `L > |det M|`,
`χ(L) < 0 < χ(U)`; `kernel/psc/symbolic_cone.mojo:432-441`), so that β lies in
`(L, U)` at every point once the other two roots are certified in the disc,
and let `G` be a quadratic in `t`. Write `G = b0 (1−x)² + 2 b1 x(1−x) + b2 x²` with `x = (t−L)/(U−L)`, so
`b0 = G(L)`, `b2 = G(U)` and `b1 = G(L) + (U−L) G′(L)/2`. If the region signs of
`b0`, `b1`, `b2` are all certified equal to `σ ∈ {±1}`, then `G(β)` has sign
`σ` at every point of the region.
*Proof.* At each point β lies between `L` and `U`, so `x(β) ∈ [0,1]`. There the
basis functions are nonnegative and `(1−x)²` or `x²` is positive, so `G(β)` is
a combination with sign `σ`. The code reads `b1` through
`2 dL² dU b1 = 2 dU · dL² G(L) + (nU dL − nL dU) · dL G′(L)`
(`bernstein_middle`, `kernel/psc/symbolic_cone.mojo:265-270`), which has the
sign of `b1` because `dL, dU > 0`. ∎
**Bracket order, a hardening.** Before this note `certify_cone` did not certify
`L < U`, which Lemma S′'s own rules (two end reads, monotone, bending away)
already need: a proposal `U = 0` passes `χ(U) > 0`, since `χ(0) = 2`, and
would put β outside the bracket. The order is now certified
(`bracket_width`, `:260-262`, read at `:434-435`); a disorder refuses. On the
logged class-A run every bracket was already ordered, and the class-B replay is
in §6.2.
The rule is opt-in (`Cone.hull`, `:284`, read at `:372`). The cover turns it on
for class A only (`kernel/class_b_cone_certificate.mojo:152`); with it off, the
class-B and class-C decision sets are unchanged by code reading (identical
endings, no extra read). The class-B regression `kernel/tests/test_symbolic_cone.mojo`
passes; its only edit is the rename `class_b_cone` → `family_cone`. The rule is
needed [F]: in a scratch run without it the sector cone stopped at every shift
0–4 on a quadratic whose leading coefficient `s1 − (shift+2)` changes sign on
the region. With it, the cone still stops at shifts 0 and 1 and certifies from 2.

**4.2 I2 (G9 ≅ Reach_Γ(S9)), an identity of relations.** For every `k,t ≥ 0`,
φ restricts to a bijection `Reach_Γ(S9) → V(G9)` preserving ordered child
lists with multiplicity, terminals and the offset-zero set.
*Proof.* Both are forward closures, from φ-corresponding seed sets (§4.3),
under relations that φ intertwines:
- the literal words are the same;
- `L·(Mw) = β(L·w)` (`kernel/psc/overlap_seed_patch.mojo:143-149`);
- the strict predicate is the same;
- the terminal sets correspond, because `L·w = 0` forces `w = 0`. Indeed
  `β(L·w) = w_x β² + (w_c + w_y − n w_x) β + (w_c − w_x)`, and `{1, β, β²}` is a
  Q-basis since χ is irreducible (`docs/class-a-parikh-cubic-bridge-2026-10-31.md:73`).

Induction along the breadth-first closure gives the bijection. ∎
**I2′ (implementation).** An uncapped return of `build_seed_overlap_graph_from_tables`
is `G9`, and an uncapped return of `build_indexed` is Γ. This is code reading:
the same top-major sweep and the same `interior_overlap_cached` filter,
`build_indexed` being "The existing overlap_seed_patch streaming partition sweep,
specialized" (`kernel/psc/class_a_x_productivity.mojo:98-99`). A capped build
refuses. The regression is `test_transfer_link`: at `(k,t) ∈ {(0,0), (0,1), (1,0), (2,3), (3,2), (12,6)}`,
the label set of `Reach_Γ(S9)` equals `exact_vertex_keys`, Γ is
`Reach(S9) ∪ R(Reach(S9))` (both inclusions), and every vertex of Γ reaches
`w = 0`; at the sector apex `(12,6)`, `|Reach(S9)| = 277`, `|Γ| = 278`, and the
extra vertex is `R(E6) = (x,x,0,−1,0)`. Ordered child lists and depths are not
compared. The seed-patch builder is the one `exact_hits` uses, so a disagreement
would suspend Theorem CA itself, and flag Theorems C and L″, which share it.

**4.3 The nine seeds** [D]. For `a < b` the candidates are `(a,b,0)` and
`(b,a,e_b−e_a)`, always strict, plus `(a,a,e_b)` (strict iff `L_b < L_a`) and
`(b,b,−e_a)` (strict iff `L_a < L_b`). With `L_x > L_c > L_y` this is
`nine_sources()` entry for entry (`kernel/psc/class_a_x_productivity.mojo:38-43`).

**4.4 I3 and Lemma R (reversal)** [D]. `child(Rv, j, i) = R(child(v, i, j))`;
strictness, the terminal set and Z are R-invariant ("The terminal set is
reversal-invariant, so R is still an automorphism.",
`docs/class-a-reversal-quotient-2026-10-31.md:26-27`; that note's stacked status
is at `:3-6`, and nothing here uses the #428–#432 premises). Hence:
- (R1) `Reach(S18) = Reach(S9) ∪ R(Reach(S9))`;
- (R2) `dist_Z(Rv) = dist_Z(v)`;
- (R3) an S9-closed carrier `𝒞` gives the S18-closed carrier `𝒞 ∪ R(𝒞)`;
- (R4) `R(W_(a,b)(m)) = W_(b,a)(−m)`, so `R(H) = H`.

**Transfer Lemma** [D]. If `HIT9(k,t)` holds, T1 and T1-H hold at `(k,t)`. Region form: a
certificate of `HIT9` on a parameter set (line `certify`, cone `cover`, and
their exact points) gives T1 and T1-H there.
*Proof.* By (R1), `v` or `Rv` lies in `Reach(S9)`. I2 transports the G9 path,
and R maps it back. Truncating at the first Z-vertex gives a first-hit path;
the earlier vertices are nonzero, hence non-terminal, so every step is an
actual child edge.
*H-entry (the forward half of T0).* Let `u = (a,b,w) ∉ Z` have an actual
child `(i,j)` in Z, so `Mw = P_a(i) − P_b(j)`:
- `i = j = 0` gives `Mw = 0`, so `w = 0`, a contradiction;
- exactly one index 0 gives an x−c difference `±1` on the right, but
  `(Mw)_x − (Mw)_c = 2w_x` is even, a contradiction;
- otherwise the right side is `(δ, −δ, m)` with `δ = [f(a) = x] − [f(b) = x]`
  and `m = i − j ∈ [−R_b, R_a]`, and solving gives `w = (δ, m−(d+1)δ, −m+dδ)`,
  so `u ∈ W_(a,b)(m)`. ∎

**Lemma 0** [D]. For every `k ≥ 0` and `t ∈ {0,1}`, T1 and T1-H hold.
`DetTwoBoundaryHittingLines` (`claim_governance.toml:937-939`,
`status = "proved"`; "boundary hitting holds for every PIP member of the 47
one-parameter catch-up-free determinant-two lines declared by Theorems L, L'
and L''", "computer-assisted, human review pending; merged through PR #246",
`tools/make_ledger.py:152-153`) gives HIT9 on the rays t = 0 and t = 1, which
are the pins `line A 2 2 1 0 1 -1 107 325 104 2 1` and
`line A 2 3 1 0 1 -1 128 303 124 3 1` (`kernel/symbolic_line_pins.txt:46,48`).
Since `A = 2n+t+2`, those are `p = 2n+2` and `p = 2n+3`. The Sturm line engine
covers `k ≥ 104` resp. `k ≥ 124`, and `exact_hits` covers the PIP members below
(`kernel/symbolic_line_certificate.mojo:182-194,200-214`). Theorem CA re-proves
both rays by a second sign-decision method, the cone engine (§6); the two share
`exact_hits`, the seed-patch builder and the line engine's exact Sturm reads at
sample points.

## 5. Decisions, kill criteria, negative controls

| Route | Decision | Basis |
| --- | --- | --- |
| **R-C** cone/line certificates (class-A Theorem-C analogue) | **GO, done on 𝒯_CA** (§6) | the engine is generic in endings (`kernel/psc/symbolic_cone.mojo:3-8`); the brackets read only `M` |
| **R-A** class-B-twin partition certificate for `{t ≥ 6, t ≥ k}` | **GO, narrowed**, but superseded as the #452 route if the #577 stack's whole-chamber proof (#578) is accepted; then only as an independent second method | P1 rays `K ≤ K0` may fit reachable labels; P2/P3 default to the strict-core closure ("The uniform carrier is the core closure `C_q`, not a fit of the reachable graph", `docs/class-b-gap-uniformity-stopgo-2026-10-27.md:137-138`); child update from `symbolic_child` (`kernel/psc/class_a_boundary_occurrences.mojo:65`); signs from `kernel/psc/class_b_middle_geometry.mojo` at `g = K` |
| class-A sign box `class_a_gap_uniform` / `poly_hu` (`u = dh ≤ 1/5`) | **not reused** | "`u>1` **for all** these `k,t>=0`" (`docs/class-a-boundary-chamber-2026-10-26.md:41`); "no transfer of #335's u<=1/5 chamber into this strip" (ledger:1925) |
| **R-S** contradiction from a target-free terminal SCC | **DEFER: not pursued in this increment; not retired** | it is the roadmap's second form, which stays open (`docs/bh-escape-roadmap-2026-11-14.md:102-127`). One instantiation is as hard as T1: "every vertex returns to X" implies T1 via `X → Q ∈ H` (`docs/class-a-x-productivity-2026-10-31.md:170`). Re-open on an invariant of target-free closed subsets of Γ that forces a vertex with an actual exit. The per-instance check `summarize` stays (`kernel/psc/class_a_x_productivity.mojo:158`) |
| **R-β** PDS via L2 by conjugacy or MLD | **DEFER, not retired** | the critical-exponent obstruction sketch is unverified. Owed: (1) a primary read of L6 Thm 17 for `d_β(1) = (n+2)((t+2)n)^ω`; (2) an invariance lemma for the asymptotic critical exponent under conjugacy; (3) L2's non-unit branch. Untouched: factor maps, other β′. Scratch searches at `(0,0)` were negative within their classes (ledger:3059) |
| **R-B** bounded-depth backward generation `Pred^{≤m}(H)` | **REDIRECT**, resting on [F] only | max depth to H grows as `⌊(t+1)/2⌋+7` at k = 0, t = 10..21 [F]; the M-adic ladder fixes no level ("**No uniform m is fixed or required by the theorem.**", `docs/class-a-madic-digit-ladder-2026-11-02.md:51`) and its higher carries "need not remain inside those nine segments" (`:170-171`) |
| **R-P** descent over all strict states | **not proposed** | a different quantifier universe; class B's strict window "is not closed" (`docs/class-b-gap-uniformity-stopgo-2026-10-27.md:82-85`) |
| **R-L** per-label star programme | **REDIRECT** to parametric carriers, not retired | its frontier asks for closure label by label (`docs/class-a-boundary-consolidated-frontier-2026-10-31.md:74-81`); "merely enumerating a constant-size 10/42/59-label outgoing image is not an adequate closure proof" (`docs/class-a-boundary-four-seed-scc-2026-10-31.md:145-147`); Γ's growth with D is [F] |
| piecewise-affine potentials (the brief's WP2 fallback) | **not proposed** | retired for class B (ledger:2039); not re-tested for class A; re-open only if the core-closure potential `|w_x| + b` fails |

**Kill criteria.** "Closed" follows AGENTS.md "Fail closed, and which way closed points".

| When | Then | Closed means |
| --- | --- | --- |
| a complete Γ_(k,t) has a vertex with no Z-descendant | replay with the oracle and the Cartesian verifier; report a candidate counterexample. On 𝒯_CA it is also a defect of Theorem CA, I2′ or I3/Lemma R; at t ∈ {0,1} also of `DetTwoBoundaryHittingLines` | refuse to promote; retire nothing |
| `G9` and `Reach_Γ(S9)` disagree at any specimen | I2′ fails: suspend Theorem CA and Corollary CA-1, and flag Theorems C and L″, which share the seed-patch builder | refuse to promote |
| a label of `𝒞∖Γ` has no descending child, or `𝒞` holds a target-free closed subset | inconclusive: refine the core; never a BH failure | refuse to conclude |
| a cone family is undecided at every shift, or a region disagrees with its exact cross-check | split into lines or hand the region to R-A; an engine defect cites no region | refuse to conclude / to promote |
| P2 signs undecided under `(h, v = Kh)`, a middle table depends on K, or layer widths grow with D | narrow the regime; never two-variable Sturm (ledger:1452-1456) | refuse to conclude |
| any R-β check (1)–(3) fails | withdraw the sketch; the sub-route is fully open | refuse to retire |
| a state, pair or exact-graph cap is reached | raise it explicitly with a budget | refuse to conclude |

**Negative controls**, as executable refusals or cited records:
- *Bernstein rule:* through the engine, at the member `(8,0)` the quadratic `(10⁴t − 132155)(10⁴t − 132156)`, positive at both ends of both brackets and negative at β, refuses (`test_bernstein_refuses_a_dip_at_beta`); the middle read keeps its denominators (`(3t−4)(t−1)` on `[1/3, 3/2]` reads −33, `test_bernstein_rule`); the class-B twin's cone, with the rule off, refuses the sector sign that the class-A cone decides (`test_bernstein_decides_the_sector_sign`).
- *Twins:* the exact seed graphs differ (`test_lemma_tw_over_q_k_t`); the child witness of Lemma TW (6) is cited, not executed.
- *Every-edge descent* must fail: on `n ≥ 5` by the cycle `T1 → U → R(T1) → R(U)` (ledger:1945), and on the probed `n ∈ {3,4}` specimens only by [F] SCC data.
- *Strict window* is not a carrier (`docs/class-b-gap-uniformity-stopgo-2026-10-27.md:82-85`). The *superset trap* is inconclusive.
- *Boundary-band missing child* `(x,x,−6,−17,36)` (`docs/class-b-middle-certificate-2026-10-27.md:158-169`). *Rectangle carrier* `V_n → W_n` (ledger:1848).
- *Equal offsets, different ordered children:* R5/D3 and D5/R3 (ledger:2166, 2172). *Seed-name identification* is refused (ledger:2200).
- *Physical vs integral zero:* the `021/120` control (`docs/bh-escape-roadmap-2026-11-14.md:157`).
- *Endpoint transitions:* RUN assumed at E2's `2n+3 = A+1`, at H5's k = 0/1/≥2 split or at P9's `2n+2+[k>=2]` must refuse (ledger:2009, 2021, 2156).
- *Scoped results mistaken for universal ones:* 𝒯_CA is not the chamber; class-B certificates are not class A; the D = 2 interior is not class B's certified band (§7).

## 6. Theorem CA: the class-A cone theorem on 𝒯_CA

**Coordinates** [D]. `(k,t) ↦ (q,p) = (n, 3n−K)` is affine and unimodular,
with inverse `t = p−2q−2`, `k = 3q−p−1`. The chamber is `2q+2 ≤ p ≤ 3q−1`.
`D = 1 ⟺ t ≤ k−1 ⟺ 2p ≤ 5q`.

**6.1 The twelve families** (`chamber_families`,
`kernel/class_a_chamber_cone_certificate.mojo:46-53`; `Aff(c0,c1,c2) = c0 + c1 s1 + c2 s2`, `cls = CLASS_A`):

| Family | `(k,t)` | `p`, `q`, `r` | class-B twin |
| --- | --- | --- | --- |
| `t=c`, `c = 0..5` | `t = c`, `k = s1` | `Aff(3c+8,2,0)`, `Aff(c+3,1,0)`, `Aff(c+2,1,0)` | Theorem C's `C−(c+2)`: `p = 2q + c + 2` (`docs/p1b-symbolic-cone-2026-10-08.md:126`) |
| `sector` | `k = 12+s1+s2`, `t = 6+s2` | `Aff(50,2,5)`, `Aff(21,1,2)`, `Aff(20,1,2)` | Theorem C's `D−` (`:127`); unimodular generators |
| `k-t=m`, `m = 1..5` | `k = s1+m`, `t = s1` | `Aff(2m+8,5,0)`, `Aff(m+3,2,0)`, `Aff(m+2,2,0)` | for `t ≤ 5` the point lies on `C−(t+2)`; for `t ≥ 6`, `5q−2p = m−1 ≤ 4` lies in Theorem C's open set (`:225-226`) |

**Coverage** [D]. The pieces are `{t = c}`, `{t ≥ 6, k−t ≥ 6}` and
`{k−t = m}`. If `t ≤ 5`, `(k,t)` lies on `t=c`. Otherwise `m := k−t ≥ 1`; then
`m ≤ 5` gives `k-t=m`, and `m ≥ 6` gives `sector` at `s = (m−6, t−6)`. So
their union is exactly `𝒯_CA`. It is the D = 1 sector together with the six
low lines, which reach `D = 1 + ⌊(t+1)/K⌋ ≤ 7` where `k < t+1`. The overlaps
are the 30 points `{(t+m, t) : t ≤ 5, m ≤ 5}`. ∎ The driver re-checks this by
exact membership solves on `0 ≤ k,t ≤ 200` (`coverage`: missed 0, stray 0), and
the test on `0 ≤ k,t ≤ 60`.

**6.2 The run** (`pixi run --locked mojo run -I . class_a_chamber_cone_certificate.mojo all`,
36 min 3 s on the final sources, whose digests are in
`evidence/class-a-chamber-cone-2026-11-15/source-digests.txt`; log `native-cover.log`
there). A first run, before the bracket-order check of §4.1, printed the same
lines, timing aside.
Every family is covered by `cover` (`kernel/class_b_cone_certificate.mojo:229`):
symbolic regions at the least certifying shift, the strips below them as lines,
and the points below those by the exact kernel.

| Family | symbolic region (vertices) | exact members (largest graph) |
| --- | --- | --- |
| `t=0` | `k ≥ 8` (325) | `k = 0..7` (784 at `(0,0)`) |
| `t=1` | `k ≥ 12` (303) | `k = 0..11` (1,010) |
| `t=2` | `k ≥ 12` (297) | `k = 0..11` (1,220) |
| `t=3` | `k ≥ 12` (287) | `k = 0..11` (1,439) |
| `t=4` | `k ≥ 12` (281) | `k = 0..11` (1,632) |
| `t=5` | `k ≥ 16` (279) | `k = 0..15` (1,807) |
| `sector` | `s ≥ (2,2)` (277); strips `s1 = 0, 1` from `s2 ≥ 2`, `s2 = 0, 1` from `s1 ≥ 2` (277 each) | `(12,6), (13,6), (13,7), (14,7)` (277) |
| `k-t=1..5` | `t ≥ 8` (313, 291, 295, 281, 283) | `t = 0..7` (largest 436, 378, 351, 339, 331) |

Totals: 16 symbolic regions and 116 exact verdicts over 86 distinct members
(the 30 overlap points are decided twice, with equal counts); no member is
non-PIP (the driver refuses otherwise); no cap was reached. Every symbolic vertex has an
offset-zero descendant (`cone_offset_zero_reachable`, `kernel/psc/symbolic_cone.mojo:687`)
and every exact vertex has one (`exact_hits`, `kernel/symbolic_line_certificate.mojo:110-120`);
either failure raises. Each certified region agrees vertex for vertex with the
exact graph at one integer point, as a cross-check that is not part of the
proof (`kernel/class_b_cone_certificate.mojo:194-216`).
**Theorem C replay.** On the same final sources (the generic cover and the
bracket-order check), `class_b_cone_certificate.mojo plus` and `minus`
reproduce the archived Theorem C run (`archive/2026-10-08/class-b-cone-run/`):
the same certified regions at the same shifts, the same exact members on the
minus branch, and the same totals, 32 regions and 198 exact members on `+1`,
45 and 292 on `−1` (`class-b-replay-plus.log` and `class-b-replay-minus.log` in
the evidence packet).

**6.3 Theorem CA.** Let `(k,t)` satisfy `t ≤ 5` or `t ≤ k−1`. Then every
overlap of `σ_(k,t)` reachable from any of its swap seeds has an offset-zero
descendant (`HIT9(k,t)`). Status: repository-proved, computer-assisted, human
review pending.
*Proof.* The run of §6.2, Lemma S′ with Lemma S″ for the symbolic regions (I1),
`exact_hits` for the exact members, and the coverage of §6.1. ∎
Theorem L″'s two class-A rays are re-proved by a second decision method: the
cone engine certifies `t=0` from `k ≥ 8` and `t=1` from `k ≥ 12`, where the
Sturm line engine needs `k ≥ 104` and `k ≥ 124`, with the same symbolic counts
325 and 303.

**6.4 Corollary CA-1 (#452 on 𝒯_CA).** For every `(k,t) ∈ 𝒯_CA`, T1 and T1-H
hold: every vertex of `Γ_(k,t)`, transient ones included, has a first-hit path
of actual strict indexed child edges into Z, and every nonzero vertex enters
H. *Proof.* Theorem CA and the Transfer Lemma (I2, I3, §4.4). ∎
Its dependencies are Theorem CA and the elementary lemmas I2, I3/Lemma R and
the forward half of T0 (§4); it builds no Γ, so I2′ enters only through the
seed-patch builder Theorem CA already uses. It uses neither T0's converse nor
the #428–#432 premises.

**6.5 Doc-level consequences, not governed.** Theorem L″ and Theorem C
derive pure discrete spectrum from HIT9 through Corollary E2, which "covers all
four classes", manuscript Corollary `cor:scc-reduction`(ii) and Theorem
`thm:main-density`, "resting on Theorem E (unreviewed) and on the imported
Barge–Štimac–Williams theorem" (`docs/p1b-boundary-hitting-progress-2026-10-08.md:227-233`).
Besides HIT9 the chain reads PIP, `|det M| = 2` and Theorem E's normal form
(`docs/p1a-a1-prime-2026-10-05.md:624-627`), which Lemma TW supplies, so it
gives PDS for every member of 𝒯_CA with the same status and the same two
dependencies. Theorems L″ and C also state a finite balanced-pair automaton
(G1) through `prop:G1-from-half-coincidences`
(`manuscripts/PSC_balanced_pair_state_2026-09-13.tex:1080-1087`); that step is
not re-examined here, and G1 is not stated.

**6.6 What is left of #452.** The chamber minus 𝒯_CA is `{t ≥ 6, t ≥ k}`
(every point has `D ≥ 2`). The cone slopes `p/q = 3 − K/q` accumulate at 3, so
cones cover finitely many D only. The uniform remainder goes to R-A unless the
#577 stack's whole-chamber proof (§2) lands first.

## 7. Finite observations [F]

These come from scratch probes and are never universal. Graph completeness
rests on `build_indexed` alone (cap 6000, not hit, Cartesian verifier off).
- *Sector probe.* It covered 95 distinct graphs, at k = 24, t = 0..23; k = 30, t = 0..29; k = 12, t = 11..25; and k = 24, t = 23..49:
  - the D = 1 interior is one S18 set of 278 vertices, at k = 24 and k = 30;
  - the low and high layers at D = 1 have widths 5–6;
  - the D = 2 interior at K = 25, `ρ = 5..18`, is one set of 398 vertices, which K = 13 matches at `ρ = 5, 6`;
  - every vertex reaches H within 3 edges.
- *Agreement with Theorem CA.* Every symbolic S9 count of §6.2 is the probe's S18 count minus one: 325/326, 303/304, 297/298, 287/288, 281/282, 279/280, 277/278, 313/314, 291/292, 295/296, 281/282 and 283/284. This matches `Γ ∖ Reach(S9) = {R(E6)} = {(x,x,0,−1,0)}`, which the regression asserts at the apex `(12,6)`.
- *Scope correction (class B).* The D = 2 interior members have `l = 2`, inside class B's "untreated" strip `l < 4` (`docs/class-b-middle-certificate-2026-10-27.md:170`), not in its certified middle band.
- *Size and depth on k = 0.* `|Γ| = 120t + 1404` for t = 12..21; the maximum depth to H is `⌊(t+1)/2⌋ + 7` for t = 10..21, with no plateau.

## 8. Non-claims

- Theorem CA and Corollary CA-1 cover 𝒯_CA only. Nothing here proves BH,
  entry, A1′, G1 or PSC elsewhere. On `main`, T1 is open on `{t ≥ 6, t ≥ k}`;
the #577 stack's proof of the whole chamber is neither cited nor assessed here.
- Theorem CA is repository-proved, computer-assisted and human review
  pending. Like Theorem C it is not registered in the claim ledger;
  registering it, and Corollary CA-1, is a deliberate later act.
- I2′ is code reading backed by a finite regression, which compares label sets
  at six members, not ordered child lists or depths. Theorem CA does not use
  I2′ beyond the seed-patch builder of its own exact members.
- T0 stays "proposed". The #433 hub identity and the reversal note keep their
  quoted statuses. Nothing here uses the hub premises.
- R-S and R-β are deferred, not retired; R-B and R-L are redirects resting on
  [F]. Class-B certificates discharge nothing for class A.
- Absences (the twin statement, a class-A cone theorem, governed records) rest
  on greps at `71afd61`. The governed class-A records do not reach the chamber:
  `ClassABoundaryHittingLowGaps` has gaps `d ≤ 4`, and `ClassABoundaryHittingHighGaps`
  asserts `n ≥ 5d` only, "the strip n < 5d is not asserted"
  (`tools/make_ledger.py:156-159`), while the chamber has `n + 2 ≤ d ≤ 2n − 1`.
- Hosted acceptance of `.github/workflows/class-a-chamber-entry.yml` is pending.

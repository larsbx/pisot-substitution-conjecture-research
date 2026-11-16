# C4: the closure attempt of 2026-11-15/16 — six routes, their first failed premises, and what survived — 2026-11-16

**Status:** record of a proof attempt. **Universal C4 is not proved and
remains open.** Nothing here changes a governed claim status: C4, A1′ (#138),
BH (#139), #84, G1 and PSC stay as they were, and no ledger claim is
registered or promoted. The statements recorded below are written proofs or
proof outlines, conditional on the imports listed with each, verified by
independent adversarial re-derivation within the session that produced them
except where §4 and §11 say otherwise (those sections record, per statement,
who checked it and whether the repository holds a proof, an outline or no
proof text), not machine-checked; independent human review pending.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@febe7535`.

Six independent proof attempts were made on universal C4. Three ended with
an explicit obstruction and three with a theorem strictly weaker than C4.
This note keeps the exact place where each route stops, the statements that
survived verification, the new negative controls, and the structural reason
the attempt could not have succeeded in the form it was posed. The theorems
on the geometric property (F) class are stated and proved in the companion
[(F)-class note](c4-geometric-f-class-2026-11-16.md) (literature gate:
[(F)-class literature note](c4-geometric-f-class-literature-2026-11-16.md));
they are indexed here, not re-proved.

Reading guide: §3 for the outcome, §8–§10 for what it means, §14 for the
five "work shown" headings.

## 1. The target and its equivalent forms

**Standing class PIP3.** A substitution `σ` on `{0,1,2}`, nonerasing and
primitive, whose incidence matrix `M` (column `a` is the Parikh vector of
`σ(a)`) has characteristic polynomial irreducible over `ℚ` and Perron root
`β` a Pisot number. Then `det M ≠ 0`; `|det M| = 1` is **not** assumed.
`ℓ` is the positive left Perron row (tile lengths), `p(·)` the Parikh vector,
`g` and `g_R` the first- and last-letter maps.

A *balanced pair* is a pair `(u,v)` of nonempty words with `p(u) = p(v)`. It
is *irreducible* if no proper nonempty prefixes of `u` and `v` have equal
Parikh vectors, and *coincident* if `u = v` (then a single letter). The
*children* of `(u,v)` are the irreducible factors of `(σ(u), σ(v))`. A
*strict system* is a finite nonempty set of irreducible noncoincident
balanced pairs closed under children.

> **C4 (universal form, issue #461).** No `σ ∈ PIP3` has a strict system.

| Form | Statement | Source and status |
| --- | --- | --- |
| Rays | For every `m ≥ 1` and distinct letters `a, b` fixed by `g^m`, with `τ = σ^m` and `X_a = τ^ω(a)`: if no equal-Parikh cut `k` has `X_a[k] = X_b[k]`, then the equal-Parikh cuts of `(X_a, X_b)` have unbounded gaps. | Proposition 3 and Lemma F of the [cut-attractor note](c4-cut-attractor-window-2026-11-05.md); written proof, human review pending. |
| Tilings | The half-line `ℓ`-tilings `T_a, T_b` of two such rays never share a tile ⟹ their common vertices are not relatively dense. | Same; uses ℚ-independence of `ℓ` (irreducibility). |
| Overlap graph | For the root `(a,b,0)` of the ordered prefix-aligned overlap graph: a strict system exists iff some root has no reachable diagonal and every reachable overlap has a path to a common-endpoint overlap. | Draft PR #576 (`research/c4-periodic-ray-decision`), **unmerged, not on main**; quoted for orientation only. |

C4 is implied by left strong coincidence of all letter pairs (Theorem A(4)
of the [cut-pair note](c4-cut-pair-productivity-2026-11-04.md), Lean
`proof/PscVerif/PscVerif/StrictSystem.lean`; the hypothesis is #138, open).
The only hypothesis C4 has beyond that open problem is **bounded gaps**
([finite-domain note](c4-finite-domain-closure-2026-11-05.md) §4). The
attempt was therefore an attempt to make bounded gaps pay.

**Notation used below** (definitions and proofs in the (F)-class note). A
*state* is `(j,v)` with `j` a letter, `v ∈ ℤ³`, `0 ≤ ℓ·v < ℓ_j`. The
*prototile state map* is `f(j,v) = (j′, Mv − p(P))`, where `σ(j) = P j′ S`
is the factorisation with `ℓ·p(P) ≤ ℓ·Mv < ℓ·p(P) + ℓ_{j′}`. Vertex states
(`v = 0`) are forward invariant. **(F)** means: no `f`-periodic state has
`v ≠ 0`. This is the geometric property (F) of Minervino–Thuswaldner
(arXiv:1402.2002, Def. 9.3 / Prop. 9.4) and the "no terminal leftmost cycle"
class of Corollary LC5
([leftmost-chain note](p1b-leftmost-chain-periodic-pair-2026-10-05.md)).
`ν_L` (`ν_R`) is the maximal number of pairwise not left (right) strongly
coincident letters; `SC_all(σ)` means that every pair of distinct letters is
left strongly coincident, i.e. `ν_L = 1` (`SC_L` in the (F)-class note);
`cr` is the coincidence rank of Baker–Barge–Kwapisz (Def. 4.1); `e₂(M)` is
the sum of the principal `2×2` minors.

## 2. Method

**Frontier map.** Nine read-only surveys of main at `febe7535`, of the open
draft branches and of the literature: core reductions; draft PR #576; the
draft family branches (#560–#573); the geometric/measure route; the
algebraic/defect route; the hub/endpoint route; the side-notes ledger and
its controls; the Lean and kernel inventory; a literature scout. Their
common finding was the starting point: every route on main ends at
all-pairs strong coincidence or pure-discrete-spectrum strength, or at the
literal factorisation of `σ(u)`.

**Six routes.** Six independent proof attempts, each given the target of §1,
the retired routes of the cut-attractor note §7, and the standing negative
controls (Thue–Morse, `10/102/211` and its reversal, `1/012/1`,
`1/012/101`, `012/120/201`, three productive PIP3 specimens, the non-Pisot
`00001/011`, the abstract plastic-cubic survivor), and each told that an
obstruction is an acceptable outcome. Each had to say where irreducibility
or the Pisot property is used and where its argument stops on every
control. The controls C-D1 and C-D2 of §7 were found during the attempt.

**Verification.** Every verdict other than an obstruction was attacked by
three independent verifiers with different lenses (logic, counterexample,
prior art): nine passes, no refutation, corrections listed in §3 and
applied throughout. The three obstruction verdicts were single-pass when
the attempt ended. During landing, two further adversarial passes checked
twelve of their statements:

| Item | Statement checked | Route | Verdict |
| --- | --- | --- | --- |
| V1 | flat ordered system ⟹ `cr ≥ 3` (Theorem FL, §6.2) | phase-one, two-ray-words | confirmed with corrections |
| V2 | flat phase one ⟹ interior `f`-periodic state (Proposition PD) | phase-one | confirmed with corrections |
| V3 | overlap carrier disjoint from its swap; twin exclusion (Lemma OC) | phase-one | confirmed with corrections |
| V4 | recognizability identity `K ∩ E_u ∩ E_v = τ(K)` (Lemma RI) | two-ray-words | confirmed |
| V5 | partner orientation (Lemma PO) | two-ray-words | confirmed with corrections; one clause false as first stated |
| V6 | slice classes at a cut (Corollary ST) | two-ray-words | confirmed with corrections |
| W1 | Barge–Diamond in the length lattice (Theorem GBD) | bd-extension | confirmed with corrections |
| W2 | the bounded-gap statement (BG) is false; five counter-models; census | bd-extension | confirmed |
| W3 | coincidence among states of a strict system (Corollary SBD) | bd-extension | confirmed with corrections |
| W4 | dense eventual coincidence of the good pair (Proposition DC) | bd-extension | confirmed with corrections |
| W5 | degree-two defect identity and its consequences | two-ray-words | confirmed with corrections: not new on main |
| W6 | the controls C-D1 and C-D2 | two-ray-words | confirmed with corrections |

Not checked by anyone but its author (single-pass): see §11.

**What is and is not evidence.** All prover and verifier computations were
scratch Python in a session directory outside the repository. They are not
committed and are **not** evidence of record. Two Mojo regressions written
at landing replay the part that the repository can stand behind (§14). A
number is stated as a fact in this note only if one of those two
regressions, or a named regression already on main, pins it; every other
number carries the label *exploratory scratch observation*. The provers'
report files were never created (the harness returned their findings as
structured summaries), so the proofs below are the first written versions.

## 3. The six routes and their first failed premises

| Route | Idea | Verdict | Verification |
| --- | --- | --- | --- |
| bd-extension | Extend the Barge–Diamond maximal-configuration mechanism to a coincidence on a cut pair under bounded gaps | obstruction | W1–W4 at landing |
| zero-fibre-rank | Compute the coincidence rank from the zero fibre (`Φ`-periodic integer strands) | partial: Theorems FC1–FC3, P, N | three lenses |
| phase-one | Exclude strict systems whose root pair is transposed by `g` | obstruction | V1–V3 at landing |
| nonunit | `M`-adic residues at common vertices when `abs(det M) ≥ 2` | partial: T1, C2, T3 (§5) | three lenses |
| cohomology | Strict system ⟹ `dim H¹ > 3` (unit) through the pair space | partial: Theorem Fork; the unit case of FC3(b) | three lenses |
| two-ray-words | Word combinatorics of two fixed rays: third ray, recognizability, numeration | obstruction | V1, V4–V6, W5, W6 at landing |

The first failed premise of each route is quoted verbatim from its record
(as recorded), followed by the corrections that bind it.

**bd-extension.**

> First failed premise (FP): "some branching of some relatively maximal
> not-eventually-coincident configuration containing an overlap of the
> strict rays exchanges the two letters of a cut pair {c,c'} in A(C)". The
> Barge-Diamond mechanism can only deliver pairs of the form (letter carried
> by the configuration at a vertex P, letter not carried at P), and every
> delivered pair is strongly coincident; a cut pair is never strongly
> coincident (Theorem A(4)), and at a common vertex of the two rays both
> letters of the cut pair are already carried.

> Moreover the bounded-gap statement itself, "(BG) for a primitive
> substitution whose inflation is a Pisot number of degree >= 2, two
> periodic rays from a common vertex with relatively dense common vertices
> share a tile", is FALSE in the category where the mechanism is valid

Binding precision (W1): the mechanism's conclusion outside PIP is
*geometric* (same letter at the same real position), not equality of Parikh
prefixes.

**phase-one.**

> The route needs: "for sigma in PIP3 with letters a != b transposed by the
> first-letter map g, a strict pair (T, T') = (X_a, sigma(X_a)) whose set B
> of ordered bigons is disjoint from its swap forces a nonzero abelian
> invariant that is odd under the track swap" -- concretely a real
> functional theta on Z^3 with theta(E) >= 0 on every overlap offset
> E = P_T - P_T' (equivalently mean offset Ebar != 0; equivalently bigon
> Parikh rank < 3; equivalently -1 in spec M). [...] For PIP3 the only
> linear consequence of the swap symmetry is (M+I)*Ebar = 0, hence Ebar = 0,
> which is the repository's known crossing lemma and not a contradiction.

Correction (V1): the route's summary sentence "phase one cannot occur at
coincidence rank 2" holds only for *flat* phase one. A root pair that is
merely transposed by `g` may carry a mixed system (`B = swap(B)`), which
nothing here touches.

**two-ray-words.**

> The route needs: "For a primitive, nonsingular substitution with Pisot
> inflation, the configuration {a hub pair of tau-fixed rays with
> bounded-gap equal-Parikh cuts and no diagonal; a strongly coincident good
> pair; a third fixed ray (classes D,E) or a leaf letter (classes C,F); the
> two-ray recognizability identity K ∩ E_u ∩ E_v = tau(K) with all its
> cut-level density relations; Dumont-Thomas double representations forming
> a recurrent zero-shift component; legal seam bigrams} is contradictory."
> This is FALSE. It is realised in full by the new control
> C-D1 = 011/120/2012

Binding precision (V4, W6): "in full" is the route's wording. Pinned on
C-D1 (§7.1) are the two strict hub pairs with their closed system, the
coincident good pair, the identity first-letter map (three fixed rays) and
the legality of every literal birth type; the recognizability identity is
Lemma RI (`det M ≠ 0`). The cut-level density relations and the
Dumont–Thomas recurrent zero-shift component were checked by no one but the
route (single-pass, §11).

**zero-fibre-rank.**

> OBSTRUCTION for the universal targets: on the (F) class bounded gaps are
> automatic (part 1), so C4 there is exactly strong coincidence (= Pisot
> conjecture) for ternary (F) substitutions, i.e. Minervino-Thuswaldner
> Thm 9.9 without its strong-coincidence hypothesis; route (A) cannot close
> C4 without proving that, and cr <= 2 (route B) is provable only on (F):
> the first failed premise off (F) is 'an interior-type periodic strand of
> the zero fibre is coincident with one of two non-coincident vertex-type
> strands'.

Corrections (logic lens): "`cr ≤ 2` is provable only on (F)" overstates;
what is shown is that *this* proof covers only (F). `cr ≥ ν_R` is not
literally Baker–Barge–Kwapisz Remark 4.3 (half-open state convention), and
`Σ = Γ = ℤ³` rests in that paper on a one-line deferral to a source that
was not obtained during the attempts (§12); both repairs are written out in
the (F)-class note.

**nonunit.**

> Failed premise: "M-adic residue data of common vertices, child closure and
> the nonunit first-defect-degree bound are jointly contradictory for every
> nonunit PIP3." They are jointly satisfied by actual strict systems of 54
> primitive nonsingular nonunit (det -2, reducible) ternary substitutions
> with images <= 3.

Corrections (logic and counterexample lenses): the premise is shown to fail
only on *reducible* sources. Over PIP3 it is equivalent to nonunit C4 and is
not refuted; this is an obstruction to the method. The count 54 is an
exploratory scratch observation under search caps.

**cohomology.**

> first failed premise: the partner correspondence of a strict component,
> pi_1: Omega_Sigma -> Omega_sigma (top-track map of the bigon tiling
> space), is not a homeomorphism or covering map, so no transfer from the
> pair space to Omega_sigma exists (Barge 2015 Lemma 13 has no analogue for
> cr >= 3).

Correction (all three lenses): only non-injectivity is proved, and only
for unit `σ` with `dim H¹ = 3` (Theorem Fork). Read: "for unit PIP3 with
`dim H¹ = 3`, `π₁` is never injective; whether it is a covering is open,
and nothing is known for `dim H¹ ≥ 4` or for nonunit `σ`."

## 4. What survived: index of results

Classes: **E** elementary (no literature import); **C** conditional on the
listed imports; **M** replayed by a Mojo regression; **S** exploratory
scratch observation, not replayable from the repository; **1** single-pass,
not independently verified. For E and C a second mark says what the
repository records: **p** a written proof (here or in the (F)-class note);
**o** a proof outline only; **n** no proof text (the statement was confirmed
by a landing verifier whose derivation exists only in session scratch).
Nothing is machine-checked, and independent human review is pending for
every row. "Endpoint class" below means the class of the first-letter map
`g`, not a class of this legend.

| Label | Statement (all hypotheses in the cited place) | Class | Verified by | Where |
| --- | --- | --- | --- | --- |
| Theorem FC1 | `σ ∈ PIP3` with (F): any two `τ`-fixed rays have bounded-gap equal-Parikh cuts; a strict system exists iff some pair of distinct `g`-periodic letters is not left strongly coincident | E·p; M on the corpus | three lenses | (F)-class note |
| Theorem FC2 | `σ ∈ PIP3` with (F): `cr = ν_L = ν_R ≤ 2`; so `C4(σ) ⟺ SC_all(σ) ⟺ cr = 1 ⟺` pure discrete spectrum | C·p | three lenses | (F)-class note |
| Corollary H | Universal C4 implies pure discrete spectrum for every `σ ∈ PIP3` with (F) | C·p | three lenses | (F)-class note; §8 |
| Theorem P | `σ ∈ PIP3`, `det M` odd, `cr = 2` ⟹ `tr M ≡ e₂(M) (mod 2)` and `dim H¹ ≥ 5` | C·p | three lenses | (F)-class note |
| Theorem FC3 | (F) and one of: `ν_L = 1` or `ν_R = 1` (prior art); `det M` odd and `dim H¹ ≤ 4`; `det M` odd and `tr M ≢ e₂(M)` ⟹ `cr = 1`, no strict system | C·p; class counts M | three lenses | (F)-class note |
| Theorem N | A strict system forces `cr ≥ 2`; with `det M` odd and (`dim H¹ ≤ 4` or `tr ≢ e₂`) it forces `cr ≥ 3` and failure of (F) | C·p | three lenses | (F)-class note |
| Theorem Fork | Unit `σ ∈ PIP3`, `dim H¹ = 3`, strict component `Z`: every `(T,T′) ∈ Z` has a second partner `T″` never coincident with `T′` | C·p | three lenses (proof reconstructed) | (F)-class note |
| Lemma RL, Theorem T1, Proposition C2 | staggered-seam descent and the seam criterion; restates results on main | E·p | three lenses | §5 |
| Proposition PW | for primitive `σ` with `det M ≠ 0`, passing to a power adds no exclusion to the seam criterion | E·p | not re-derived by a verifier before the audit of this note | §5.4 |
| Theorem T3 | `F1_c`, `F3_c` (`c ≥ 3`) are in PIP3 with `det M = c` and have no strict system | E·p. M for `3 ≤ c ≤ 63`: the hypotheses of C2 (PIP3, `det M = c`, empty legal birth-type list). The exclusion itself is replayed only for `3 ≤ c ≤ 8`, through pinned left strong-coincidence witnesses and Theorem A(4) | three lenses | §5 |
| Theorem GBD, Corollary SBD, Proposition DC | Barge–Diamond's mechanism for any Pisot inflation of degree `≥ 2`, irreducibility not needed | GBD: o, and not import-free as recorded (the outline defers to the proof of Barge–Diamond Theorem 1, read in the length lattice and not reproduced here); SBD: E·p given GBD; DC: E·o given GBD | W1, W3, W4 | §6.1 |
| Theorem FL | flat ordered system ⟹ `cr ≥ 3` | C·p | V1 | §6.2 |
| Proposition PD, Lemma OC | flat phase one ⟹ (F) fails; overlap-carrier orientation | PD: o (Barge–Diamond Theorem 1 is used in endpoint class E, nothing else is imported); OC: E·o | V2, V3 | §6.2 |
| Lemma RI, Lemma PO, Corollary ST | recognizability identity; partner orientation; slice classes | RI: E·p. PO: (i) E·p; (ii) C·p, the proof written at the audit of this note; (iii) E·p. ST: elementary part E·p; conditional part C·n | V4, V5, V6 | §6.3 |
| Controls C-D1, C-D2, `1/012/101` | reducible, irrational Pisot inflation, strict system present | M | W2, W6 | §7 |

## 5. The nonunit route: staggered seams and two families

Everything in this section is elementary. Irreducibility and the Pisot
property are used only to place the two families in PIP3. For that reason
none of it can prove universal C4: every reducible strict control with
`det M ≠ 0` satisfies it.

### 5.1 Elementary facts

Let `σ` be nonerasing and `C` a strict system.

- (E1) An irreducible noncoincident balanced pair has length at least 2,
  distinct first letters and distinct last letters. (Equal first letters
  give a balanced prefix of length 1, so the pair is one coincident letter;
  the last letters are symmetric.)
- (E2) Every irreducible factor of `σⁿ(T)`, `T ∈ C`, is in `C`: the cut set
  of a concatenation of balanced blocks is the union of the blocks' cut
  sets.
- (E3) The first-letter pair `(a,b)` of a state satisfies `gⁿ(a) ≠ gⁿ(b)`
  for all `n` (first child, E1); the last-letter pair likewise under `g_R`
  (last child).

The *legal bigrams* `L₂` are the least set containing every bigram internal
to an image `σ(a)` and closed under `xy ↦ g_R(x) g(y)`
([legal-seams note](c4-legal-seams-2026-11-04.md)).

### 5.2 Ray legality

**Lemma RL (ray legality; the nonunit route's "Lemma R").** Let `σ` be
primitive and `C` a strict system. Then there are `m ≥ 1` and letters
`a ≠ b` with `g^m(a) = a`, `g^m(b) = b` such that, with `τ = σ^m` and
`X_a = τ^ω(a)`, the blocks between consecutive equal-Parikh cuts of the ray
pairs `(σ^j X_a, σ^j X_b)`, `0 ≤ j < m`, form a strict system `C′ ⊆ C`.
Both words of every state of `C′`, and every bigram of either ray that
straddles a cut, are factors of some `σ^N(a)` or `σ^N(b)`; in particular
those bigrams lie in `L₂`.

*Proof.* The first-child map `φ` sends `T ∈ C` to the first irreducible
factor of `σ(T)`, which is in `C`. `C` is finite, so `φ^m(T₀) = T₀` for
some `T₀ = (u₀,v₀)` and `m ≥ 1`. By (E2), `φ^k(T)` is the first factor of
`σ^k(T)`, so `u₀` is a prefix of `τ(u₀)` and `v₀` of `τ(v₀)`. Their first
letters `a, b` are therefore fixed by `g^m`, and `a ≠ b` by (E1). `τⁿ(T₀)`
is a balanced prefix of `τ^{n+1}(T₀) = τⁿ(τ(T₀))`, its factors are in `C`
by (E2), and `τⁿ(u₀) → X_a`, `τⁿ(v₀) → X_b` (primitivity makes the lengths
grow). So `(X_a, X_b)` is a concatenation of states of `C`. The blocks of
`(σ^j X_a, σ^j X_b)` are the factors of `σ^j` of those blocks, again in `C`
by (E2); the children of a block at level `j` are blocks at level `j+1`,
and `σ^m X_a = X_a`. So the union `C′` over `0 ≤ j < m` is child-closed.
Every finite factor of `σ^j X_a` is a factor of `σ^{j+mn}(a)` for large
`n`. ∎

*Hypotheses.* Finiteness of `C`, child closure, primitivity. No
irreducibility, no Pisot property, no determinant condition. On main the
same legality is stated for a phase-zero strongly connected carrier and for
the carrier modulo track swap
([seam-birth note](c4-seam-birth-orbits-2026-11-04.md)); Lemma RL gives it
without choosing a hub, a track or a phase, which is what
`psc.c4_seam_families.legal_local_birth_types` relies on.

### 5.3 Staggered-seam descent

**Theorem T1 (staggered-seam descent; not claimed as new).** Let `σ` be
nonerasing on a finite alphabet with a positive left eigenvector `ℓ` for an
eigenvalue `β > 1`, `C` a strict system, `L_max = max_{T∈C} ℓ·p(u_T)`.

(a) Let `T = (u,v) ∈ C` and let tiles `u_i`, `v_j` have `ℓ`-intervals
meeting in length `δ > 0`; put `w = p(v[:j]) − p(u[:i]) ∈ ℤ^d`. For every
`n` with `βⁿδ > L_max` there are proper prefixes `P` of `σⁿ(u_i)` and `Q` of
`σⁿ(v_j)` with `p(P) − p(Q) = Mⁿw`.

(b) There are letters `c_k, d_k` and shifts `w_k`, `0 ≤ k ≤ n`, with
`w_n = w`, `w_0 = 0` and `w_{k−1} = M w_k + p(Q_k) − p(P_k)`, where `P_k`
(`Q_k`) is the proper prefix of `σ(c_k)` (`σ(d_k)`) before `c_{k−1}`
(`d_{k−1}`); at every level the tiles `c_k`, `d_k` overlap and lie in one
state of `C`.

(c) If `det M ≠ 0`, every state has an overlap with `w ≠ 0`, and beneath
each such overlap there is a **staggered seam**: letters `c, c′, x, y` and
factorisations `σ(c) = P x S`, `σ(c′) = Q y S′` with `x ≠ y` and
`0 ≠ p(P) − p(Q) ∈ M ℤ^d`, such that `(x,y)` is the first-letter pair of a
state and the two letters before the cut are the last-letter pair of a
state.

*Proof.* (a) By (E2) consecutive cuts of `σⁿ(T)` are at `ℓ`-distance at most
`L_max`. The inflated overlap `[βⁿ lo, βⁿ hi)` has length `βⁿδ > L_max`, so
the least cut position `z ≥ βⁿ lo` satisfies `z < βⁿ hi`. The top prefix
ending at `z` is `σⁿ(u[:i]) P` with `P` a proper prefix of `σⁿ(u_i)`, the
bottom prefix is `σⁿ(v[:j]) Q`, and equality of Parikh vectors is
`Mⁿ p(u[:i]) + p(P) = Mⁿ p(v[:j]) + p(Q)`.
(b) Let `c_k` be the letter of `σ^{n−k}(u)` whose `σ^k`-block contains the
cut, `s_k` the Parikh vector of the prefix before it; then
`s_{k−1} = M s_k + p(P_k)`. Define `d_k, t_k` on the bottom and
`w_k = t_k − s_k`. At `k = 0` both letters start at the cut, so `w_0 = 0`.
Both level-`k` blocks contain the cut position in their half-open
intervals, so the tiles `c_k, d_k` overlap; overlapping tiles are never
separated by a cut, so by (E2) they lie in one state.
(c) By (E1), `|u| ≥ 2` and `u_0 ≠ v_0`, so one of `(u_1,v_0)`, `(u_0,v_1)`,
`(u_1,v_1)` is an overlap, with shift `−e_{u_0}`, `e_{v_0}` or
`e_{v_0} − e_{u_0}`, all nonzero. Let `k* = max{k : w_k = 0} < n`. Then
`p(P_{k*+1}) − p(Q_{k*+1}) = M w_{k*+1} ≠ 0`, the only place where
`det M ≠ 0` is used. The level-`k*` cut is interior (index 0 would force
`w_k = 0` for all `k ≥ k*`), so it separates two consecutive factors of
`σ^{n−k*}(T)`, which are states by (E2); (E1) and (E3) give the letter
conditions. ∎

### 5.4 The seam criterion

A staggered seam is *admissible* if `{x,y}` never collapses under `g`, and
there are before-letters `x⁻, y⁻` with `g_Rⁿ(x⁻) ≠ g_Rⁿ(y⁻)` for all `n`,
where the before-letter on the top is the last letter of `P` if `P` is
nonempty and otherwise `g_R(e)` for some letter `e` with `ec ∈ L₂`
(likewise on the bottom). The existential reading for an empty prefix is a
verifier correction; the proof and the code always used it.

**Proposition C2 (seam criterion; restates results on main).** Let `σ` be
primitive with `det M ≠ 0`. If `σ` has no admissible staggered seam, then
`σ` has no strict system.

*Proof.* A strict system contains the legal subsystem `C′` of Lemma RL.
Theorem T1(c) applied to `C′` gives a staggered seam whose next letters and
before-letters are first and last pairs of states, hence never collapse
(E3). If `P` is empty, the top letter `c` is not the first letter of its
word (the cut is interior), and its predecessor `e` gives a bigram `ec` of
a ray, so `ec ∈ L₂`. The seam is admissible. ∎

*Relation to the code.* An admissible staggered seam is a member
`(c, |P|, c′, |Q|)` of the list returned by
`psc.c4_seam_families.legal_local_birth_types`, which is the on-main sieve
`L_σ` filtered by the on-main legal-predecessor rule. An empty list
therefore puts a primitive `σ` with `det M ≠ 0` under Proposition C2. The
list also keeps types with `p(P) = p(Q)`, which Theorem T1 shows are not
needed. Primitivity cannot be dropped: `1/0/22` is not primitive, has
`det M = −2` and an empty `L_σ` (the only digit `r > 0` is in `σ(2) = 22`;
against a digit zero its residue `(0,0,1)` is not in `M ℤ³`, and against
itself the next letters are equal), and `{(01,10), (10,01)}` is a strict
system of it.

**Proposition PW (powers add nothing).** Let `σ` be primitive with
`det M ≠ 0`. If `σ` has an admissible staggered seam, so does `σ^q` for
every `q ≥ 1`, with residues taken modulo `M^q ℤ^d`.

*Proof.* Write `p(P) − p(Q) = M w`, `w ≠ 0`. Replace `P, Q` by
`σ^{q−1}(P), σ^{q−1}(Q)`, proper prefixes of `σ^q(c)`, `σ^q(c′)`: the
difference of Parikh vectors is `M^{q−1}·M w = M^q w ≠ 0` (`M` is
injective), the next letters are `g^{q−1}(x), g^{q−1}(y)`, the
before-letters are `g_R^{q−1}(x⁻), g_R^{q−1}(y⁻)`, and none of these pairs
collapses under the endpoint maps `g^q`, `g_R^q` of `σ^q`. If `P` is empty,
the before-letter `g_R^{q−1}(x⁻) = g_R^q(e)` is the last letter of
`σ^q(e)`, and `ec ∈ L₂(σ) = L₂(σ^q)`: for primitive `σ` both are the set of
bigrams of the language of `σ` (a bigram of `σⁿ(a)` is internal to the
image of a letter or is `g_R(x) g(y)` for a bigram `xy` of `σ^{n−1}(a)`;
conversely every letter occurs in the language and the language is closed
under `σ`). ∎

*Status.* Asserted by the route; one of the three lenses listed it as
holding, without a derivation. The proof was written at landing and was
re-derived only at the audit of this note, where the two hypotheses and the
sentence on the empty prefix were added.

### 5.5 Two families

**Theorem T3 (two nonunit families).** For every integer `c ≥ 3`,

```text
F1_c = (0^{c−1} 1,   1 2 0^{c−1},  0^c)        χ = x³ − c x² − c
F3_c = (0^{c−1} 1 0, 0 2 1,        2 0)        χ = x³ − (c+2) x² + 2c x − c
```

are in PIP3 with `det M = c`, have no admissible staggered seam, and hence
have no strict system.

*PIP3.* `F1_c`: `M = [[c−1,c−1,c],[1,1,0],[0,1,0]]`, and
`χ(x) = x²(x−c) − c` is negative on `(−∞, c]`, increasing on `[c, ∞)`, with
`χ(c+1) = c² + c + 1 > 0`. `F3_c`: `M = [[c,1,1],[1,1,0],[0,1,1]]`, and
`χ(x) = x²(x−2) − c(x−1)²` is negative for `x ≤ 2` (both terms are
nonpositive and not both zero), negative on `(2, c]` because
`h(x) = x²(x−2)/(x−1)²` is increasing for `x > 1` and `h(c) < c`, increasing
on `[c, ∞)` (`χ′(c) = c(c−2) > 0`, vertex of `χ′` at `(c+2)/3 < c`), with
`χ(c+1) = c² − c − 1 > 0`. In both cases there is exactly one real root
`β ∈ (c, c+1)`, hence no integer root, hence `χ` is irreducible (a monic
integer cubic without an integer root has no rational root); the other
two roots are complex conjugates of squared modulus `c/β < 1`. The letter
graph has the cycle `0 → 1 → 2 → 0` and a loop at `0`, so `σ` is primitive.

*Seam table of `F1_c`.* `M ℤ³ = {v : v₀ + v₁ ≡ 0 (mod c)}` (index `c`; the
three columns of `M` satisfy the congruence). `g = (0,1,0)`,
`g_R = (1,0,0)`. A pair of next letters survives `g` only if it is `{0,1}`
or `{1,2}`; a pair of before-letters survives `g_R` only if it is `{0,1}`
or `{0,2}`.

| Occurrence (image, digit `r`) | Prefix Parikh vector | `v₀+v₁ mod c` | Next letter | Letter before |
| --- | --- | --- | --- | --- |
| `σ(0)`, `0 ≤ r ≤ c−2` | `(r,0,0)` | `r` | 0 | 0, or image boundary at `r = 0` |
| `σ(0)`, `r = c−1` | `(c−1,0,0)` | `c−1` | 1 | 0 |
| `σ(1)`, `r = 0` | `(0,0,0)` | 0 | 1 | image boundary |
| `σ(1)`, `r = 1` | `(0,1,0)` | 1 | 2 | 1 |
| `σ(1)`, `r = 2` | `(0,1,1)` | 1 | 0 | 2 |
| `σ(1)`, `3 ≤ r ≤ c` | `(r−2,1,1)` | `r−1` | 0 | 0 |
| `σ(2)`, `0 ≤ r ≤ c−1` | `(r,0,0)` | `r` | 0 | 0, or image boundary at `r = 0` |

Residue-matched pairs with distinct next letters, and what removes each
(numbers (1)–(4) are the conditions of the on-main sieve, §5.6):

| Next letters | Matched occurrences | Removed by |
| --- | --- | --- |
| `{1,2}` | none: `2` follows only residue 1, `1` follows residues `c−1` and `0` | residue, because `c−1 ≢ 1 (mod c)` for `c ≥ 3` |
| `{0,2}` | `(σ(1), r=1)` against the three next-`0` occurrences of residue 1 | (3): `g(0) = g(2)` |
| `{0,1}` | `(σ(0), r=c−1)` against `(σ(1), r=c)`: vectors differ by `(1,−1,−1)`. The next-`0` occurrences of residue `c−1` are `(σ(1), r=c)` and `(σ(2), r=c−1)` (`(σ(1), r=2)` has residue `1 ≢ c−1`), and the letter before `(σ(1), r=c)` is `0` because `0^{c−2}` is nonempty for `c ≥ 3` | (4): both before-letters are `0` |
| `{0,1}` | `(σ(0), r=c−1)` against `(σ(2), r=c−1)`: equal vectors | (4): both before-letters are `0`; not staggered |
| `{0,1}` | `(σ(1), r=0)` against `(σ(0), r=0)` and `(σ(2), r=0)` | (1): both digits zero |

So the on-main sieve `L_σ` is already empty for `F1_c`; legality is not
needed.

*Seam table of `F3_c`.* `M ℤ³ = {v : v₀ ≡ v₂ (mod c)}`. `g = (0,0,2)`,
`g_R = (0,1,0)`. Surviving next pairs: `{0,2}`, `{1,2}`; surviving
before-pairs: `{0,1}`, `{1,2}`. `L₂ = {00, 01, 02, 10, 20, 21}`: these are
the internal bigrams, and the set is closed under `xy ↦ g_R(x) g(y)`. The
bigram `12` is illegal.

| Occurrence (image, digit `r`) | Prefix Parikh vector | `v₀−v₂ mod c` | Next letter | Letter before |
| --- | --- | --- | --- | --- |
| `σ(0)`, `0 ≤ r ≤ c−2` | `(r,0,0)` | `r` | 0 | 0, or image boundary at `r = 0` |
| `σ(0)`, `r = c−1` | `(c−1,0,0)` | `c−1` | 1 | 0 |
| `σ(0)`, `r = c` | `(c−1,1,0)` | `c−1` | 0 | 1 |
| `σ(1)`, `r = 0` | `(0,0,0)` | 0 | 0 | image boundary |
| `σ(1)`, `r = 1` | `(1,0,0)` | 1 | 2 | 0 |
| `σ(1)`, `r = 2` | `(1,0,1)` | 0 | 1 | 2 |
| `σ(2)`, `r = 0` | `(0,0,0)` | 0 | 2 | image boundary |
| `σ(2)`, `r = 1` | `(0,0,1)` | `c−1` | 0 | 2 |

| Next letters | Matched occurrences | Removed by |
| --- | --- | --- |
| `{0,1}` | any | (3): `g(0) = g(1)` |
| `{0,2}` | `(σ(1), r=1)` (residue 1) against `(σ(0), r=1)`, its only match for `c ≥ 3`: the other next-`0` occurrences have residue `r ≠ 1` (`σ(0)`, `r ≤ c−2`), `0` (`(σ(1), r=0)`) or `c−1` (`(σ(0), r=c)` and `(σ(2), r=1)`), and `c−1 ≢ 1 (mod c)` for `c ≥ 3`; equal vectors `(1,0,0)` | (4): both before-letters are `0`; not staggered |
| `{0,2}` | `(σ(2), r=0)` against `(σ(0), r=0)` and `(σ(1), r=0)` | (1): both digits zero |
| `{1,2}` | `(σ(0), r=c−1)`: residue `c−1`, while `2` follows residues 1 and 0 | residue, because `c−1 ∉ {0,1} (mod c)` for `c ≥ 3` |
| `{1,2}` | `(σ(1), r=2)` (residue 0) against `(σ(2), r=0)`, its only match: vectors differ by `(1,0,1) = M e₂` | legal predecessor only, see below |

The last row is the one live seam. Its top before-letter is `2`. Its bottom
cut is at an image boundary, so the bottom before-letter is `g_R(e)` for a
predecessor `e` of the letter `2`. The on-main sieve allows all three
predecessors, giving before-pairs `(2,0)` (collapses) and `(2,1)` (never
collapses), so on main `L_σ = {(1,2,2,0), (2,0,1,2)}`. The only legal
bigram ending in `2` is `02`, so `e = 0`, the before-pair is `(2,0)`, and
it collapses under `g_R`. No admissible staggered seam remains. ∎

*Where `c ≥ 3` is used.* (i) `c−1 ≢ 1 (mod c)`: in `F1_c` in the `{1,2}`
row and in the list of next-`0` occurrences of residue `c−1`; in `F3_c` in
the `{1,2}` residue row and in the `{0,2}` row, where it keeps
`(σ(0), r=c)` and `(σ(2), r=1)` from matching `(σ(1), r=1)`. (ii) `0^{c−2}`
is nonempty: in `F1_c` the letter before `(σ(1), r=c)` is `0`, not `2`. At
`c = 2` both families are in PIP3 with `det M = 2` and keep legal types
(pinned, §14): `(0,1,1,1)`, `(0,1,1,2)` and their swaps for `F1_2`, where
(i) fails in the `{1,2}` row and (i), (ii) fail together in the first
`{0,1}` row; `(0,2,1,1)` and its swap for `F3_2`, where (i) fails in the
`{0,2}` row.

### 5.6 Prior art (binding)

- **Proposition C2 is not new.** It restates the *uniform zero-candidate
  eliminator* of the
  [bilateral-birth note](c4-bilateral-birth-rigidity-2026-11-02.md) §9
  (for primitive `σ`, `L_σ = ∅` and `det M ≠ 0` exclude a strict system;
  conditions (1) not both digits zero, (2) `p(P) − p(Q) ∈ M ℤ³` (the
  vector called `c` on main), (3) next letters not eventually equal under
  `g`, (4) before-letters not eventually equal under `g_R`;
  `unresolved_local_birth_types` in `kernel/psc/c4_cut_alignment.mojo`)
  with the legal-predecessor refinement of the
  [legal-seams](c4-legal-seams-2026-11-04.md) and
  [seam-birth](c4-seam-birth-orbits-2026-11-04.md) notes. Theorem T1 is a
  self-contained re-derivation of the newborn-residue lemma. Two small
  additions: Lemma RL gives the legality without a hub, a track or a
  phase; and a strict system contains a seam with `p(P) ≠ p(Q)`. The
  second changed no exclusion on the tested sets (exploratory scratch
  observation).
- **`F1_c` is a verbatim instance** of the on-main eliminator (unrefined
  `L_σ = ∅`). **`F3_c` needs the hub-free legal-predecessor reading**: on
  main `L_σ` has exactly the two types `(1,2,2,0)`, `(2,0,1,2)`, removed
  because `12` is illegal. Neither family is recorded on main or on a draft
  branch; "new" means two new instances.
- **The method is not new for nonunit families.** Draft PR #576 (unmerged)
  excludes `σ_{k,r} = (1, 0 1^k 2, 0^r 1)`, `det M = r ≥ 2`, by the same
  residue-seam argument, and main has the nonunit families
  `(01, 1^a 2 1^b, 012)` by strong coincidence. After the relabelling
  `0 → 1 → 2 → 0`, `F3_c` is `(01, 1^{c−1} 2 1, 102)`: the incidence matrix
  of those families with a word order for the third image that the
  [direct-source note](c4-direct-source-coincidence-2026-11-04.md) does not
  cover.
- **The families add nothing beyond Theorem A(4) where tested.** For
  `3 ≤ c ≤ 8` all three letter pairs of every member have left
  strong-coincidence witnesses, at levels `(4,1,5)` for `F1_c` and
  `(1,4,2)` for `F3_c` in pair order `{0,1},{0,2},{1,2}` (pinned). The
  pair of `g`-periodic letters, `{0,1}` resp. `{0,2}`, is witnessed at
  level 4. The earlier wording "a level-4 witness for each member" was
  inexact for the pair `{1,2}` of `F1_c`. The value of Theorem T3 is one
  argument for every `c`, without a witness.

### 5.7 Why the residue route stops

- All 1,926 nonunit corpus members have `det M = 2` (on main:
  `kernel/tests/test_h1_census.mojo`). *Exploratory scratch observations*,
  reproduced by the three verifiers' independent scratch code: 1,320 of
  them are excluded already because an endpoint map collapses every pair;
  of the other 606, none is in the class of Proposition C2; for
  `det M = 3` and images of length at most 4, 132 of 6,960 non-trivial
  members are, and no incidence matrix is covered for all its word orders.
- For a nonunit `σ ∈ PIP3`, `D = |det M| = β·|α₂α₃| < β ≤` the longest
  image length (`α₂, α₃` the other two roots), so the longest image has two
  distinct proper prefixes with equal residue. Residues alone cannot
  separate all cut positions; only the letter filters exclude. (This is a
  counting heuristic, not a statement about `L_σ`: Theorem T3 itself uses
  residue separation.)
- Proposition PW: passing to powers adds no exclusion.
- *Exploratory scratch observation:* among primitive nonsingular ternary
  substitutions with images of length at most 3, 54 nonunit ones (all
  `det M = −2`, all reducible) have strict systems found within search
  caps, and each satisfies every statement of Theorem T1 with all its
  actual seams admissible. So on reducible sources the residue conditions,
  child closure and the letter filters of this criterion are jointly
  satisfiable (scratch, within caps).
- *Route remark, not proved and not checked by a verifier:* the seam
  criterion reads only residues modulo `M ℤ^d` and letter data, and on the
  tested sets with `|det M| = 2` it excluded neither a PIP3 corpus member
  beyond the endpoint filters nor, as it must not, a reducible source
  carrying a strict system. Nothing is claimed about residue data in
  general. The route's sentence "the carrier depends only on the
  `ℤ_p[M]`-modules for `p | det M` and cannot see irreducibility over `ℚ`"
  is not adopted: it was not proved, and read literally it is false, since
  the `ℤ_p[M]`-module `ℤ_p³` determines `χ_M`. Nothing here bears on the
  matrix-adic carrier route on main
  ([matrix-adic continuation](c4-madic-residue-2026-11-11.md)).

## 6. Statements from the three obstruction routes (verified forms)

These are necessary conditions or mechanism statements. None excludes a
strict system for PIP3. Each is given in the form the landing verifier
confirmed; the corrections are part of the statement. Proof text added at
the audit of this note is marked as such.

### 6.1 The Barge–Diamond mechanism in the length lattice

**Theorem GBD (route label G-BD).** Let `σ: A → A⁺` be a nonerasing
substitution on a finite alphabet and `ℓ: A → (0,∞)` with
`ℓ(σ(a)) = λ ℓ(a)` for every `a`, where `λ` is a Pisot number of degree at
least 2. Then there are letters `a ≠ b`, `n ≥ 1` and factorisations
`σⁿ(a) = p c s`, `σⁿ(b) = p′ c s′` with `ℓ(p) = ℓ(p′)`.

Not needed: primitivity, irreducibility of `χ_M`, any condition on the
eigenvalues of `M` that are not conjugates of `λ`. The conclusion is
geometric: equality of the Parikh vectors of `p, p′` is **not** obtained,
and is false in this generality (below).

*Proof outline.* Reduce to a terminal strongly connected sub-alphabet; it
has at least two letters because `λ` is irrational, and there `ℓ` is a
multiple of a vector with entries in `ℚ(λ)`. Work in the lattice
`Λ = Σ_a ℤ ℓ(a) ⊂ ℚ(λ)` with `‖x‖_s` the largest modulus of the other
embeddings. (F1) `x ≠ 0 ⟹ ‖x‖_s > 0` (degree `≥ 2`). (F2) bounded real
value and bounded `‖·‖_s` leave finitely many points of `Λ`. Trapping:
`‖λx + ℓ(P)‖_s ≤ ρ‖x‖_s + c₀` with `ρ < 1` the largest conjugate modulus, so
`{‖x‖_s ≤ B′}` is forward invariant and absorbing for any
`B′ > c₀/(1−ρ)`. From here the proof of Barge–Diamond Theorem 1 runs
verbatim with tiles (letter, position in `Λ`) in place of lattice segments:
a not eventually coincident configuration of maximum size, its slices, Case
1 (an alternative continuation at a vertex forces an eventually coincident
pair issuing from that vertex) and Case 2 (determinism gives a period `v`
with `p‖v‖_s ≤ 2B′` for arbitrarily large `p`, contradicting F1). The Pisot
property is used at trapping and (F2); irreducibility is used nowhere.

*Label.* Barge–Diamond's proof read in the length lattice. Novelty is not
claimed and was not assessed (no literature gate); Barge's later framework
already takes "Pisot" to mean Pisot inflation.

*The qualifier "geometric" cannot be dropped* (W1, exact but single-pass,
*exploratory scratch observation*): of the 5,646 primitive reducible
ternary substitutions with images of length at most 3 and irrational Pisot
inflation, 108 have no pair of letters that is strongly coincident in the
equal-Parikh sense, although all three pairs are geometrically eventually
coincident; all have third eigenvalue `±2`. Example: `1/202/011`,
`χ = (x+2)(x²−2x−1)`.

**Corollary SBD (route label S-BD).** Let `τ` be a substitution with a
positive length function `ℓ`, `ℓ(τ(a)) = μ ℓ(a)`, `μ` a Pisot number of
degree at least 2. Let `S` be a finite nonempty set of ordered pairs
`B = (u_B, v_B)` of nonempty words with `ℓ(u_B) = ℓ(v_B)` such that each
`(τ(u_B), τ(v_B))` is a concatenation `Σ(B)` of members of `S`. Then **there
exist** states `B ≠ B′`, `n ≥ 1` and a state `C` with `Σⁿ(B) = X C Y`,
`Σⁿ(B′) = X′ C Y′` and `ℓ(u_X) = ℓ(u_{X′})`. If no member of `S` has
`u = v`, such `B, B′` are never swaps of each other.

*Proof.* Theorem GBD for the substitution `Σ` on the alphabet `S` with
length `L(B) = ℓ(u_B)`. If `B′` is the swap of `B` and `C = (c₁,c₂)` occurs
at the same position in both, then the word `τⁿ(u_B)` carries the two
words `c₁` and `c₂`, of equal length, at one position, so `c₁ = c₂`. ∎
The statement is existential (it is false for
"every pair of non-swap states"); "not swaps" is a consequence, not a
hypothesis. For `τ = σ^k`, `σ ∈ PIP3`, equal lengths mean equal Parikh
vectors. It holds on every reducible strict control with irrational
inflation, which is why it excludes nothing.

**Proposition DC (dense coincidence of the good pair).** Under the
hypotheses of Theorem GBD on three letters `{h,a,b}`, suppose neither
`{h,a}` nor `{h,b}` is eventually coincident. Then there is `ε > 0` such
that every overlap of a tile of `σⁿ(a)` with a tile of `σⁿ(b)` (words
aligned at `0`) inside `λⁿ·(0,ε)` is eventually coincident. If `a` and `b`
are periodic under `g`, every overlap of the fixed rays `X_a, X_b` is
eventually coincident and their shared tiles have asymptotic density 1.

*Proof outline (W4).* Let `K` be the maximum size of a not eventually
coincident configuration. In Case 1 of Theorem GBD the exchanged letters
must be `a` and `b`, so two maximum configurations share a common part of
size `K−1`; an overlap of the two branches near the vertex that were not
eventually coincident would complete a configuration of size `K+1`. ∎
Corrections: density is proved only near the common vertex unless both
letters are `g`-periodic; the record's phrase "`X_a` and `X_b` coincide on
a dense open set" is wrong (the rays never share a tile on
`(0, min(ℓ_a, ℓ_b))`); in PIP3 the hypothesis "exactly one strongly
coincident pair" is not known to be satisfiable, so there the proposition
may be vacuous. Its realised instances are the reducible controls.

**What the mechanism can deliver.** On three letters with good pair
`{a,b}` and hub `h`, a branching exchanges a strongly coincident pair
issuing from one vertex: the good pair, unless a hub pair is strongly
coincident. A cut pair of a strict system is never strongly coincident
(Theorem A(4)), and at a common vertex of the two rays both of its letters
are already carried. So the mechanism never outputs a cut pair. Three
letters give two hub pairs and one good pair, and Barge–Diamond supplies
exactly the good pair: there is no collision. With two letters the unique
pair is both, which is the only reason the binary case closes.

### 6.2 Flat systems

A finite set `B` of ordered irreducible noncoincident balanced pairs is
*flat* if `B ∩ swap(B) = ∅`, where `swap(u,v) = (v,u)`; *mixed* if
`B = swap(B)`.

**Theorem FL (flat ⟹ `cr ≥ 3`; route labels: phase-one "Theorem C",
two-ray-words "Cor. O′").** Let `σ ∈ PIP3`, `τ = σ^m`, and `B` a finite
nonempty flat set of ordered irreducible noncoincident balanced pairs of
legal words, closed under `τ`-children. Then `cr(σ) ≥ 3`.

Instances: a flat rooted system of either phase; any ordered `τ`-sink `S`
of a strict system with `S ≠ swap(S)` (two sinks are equal or disjoint; the
words of a sink are legal, because by the proof of Lemma RL applied to the
sink its states are blocks of pairs of periodic rays).
Contrapositive: **if `cr(σ) ≤ 2`, every strongly connected child-closed
ordered component of a strict system is swap-symmetric.**

*Proof.* (1) Fix `(u₀,v₀) ∈ B`. By (E2) each patch
`(τⁿ(u₀), τⁿ(v₀))` is a concatenation of members of `B`, and its words are
legal. The bi-infinite pairs all of whose finite windows occur in these
patches form a nonempty closed translation-invariant set (compactness; the
patches grow by primitivity); let `Z` be a minimal closed invariant subset.
Every member of `Z` is tiled by bigons of `B`, and each projection of `Z`
is a nonempty closed invariant subset of the hull, which is minimal, so
both projections are the whole hull. (An arbitrary bi-infinite
concatenation of bigons of `B` need not be legal at its junctions, which is
why `Z` is taken inside these patches.) (2) A pair of `Z` shares no tile:
a shared tile is an equal-Parikh cut followed by equal letters (`ℓ` is
injective on `ℤ³`), a coincident factor. (3) If `(S⁻,S)` and `(S,S⁺)` are
in `Z`, then `Φ^k S⁻` and `Φ^k S⁺` share no tile for any `k ≥ 0`: inside a
deep inflation of a shared tile, two consecutive common vertices of the
first pair cut out some `(p,q) ∈ B`, and the same two vertices cut out
`(q,p)` from the second pair, so `(q,p) ∈ B`. (4) Consecutive strands
share a vertex, and the return module is `ℤ³`, so all three lie over one
point of the base of the geometric realisation; they are pairwise
non-coincident by (2) and (3), and the definition of `cr` gives
`cr ≥ 3`. ∎

*Imports.* Baker–Barge–Kwapisz Def. 4.1 (a definition) and return module
`= ℤ³` (Theorem R of the
[periodic-pair fibre gate](p1b-periodic-pair-fibre-literature-gate-2026-10-02.md),
repository-proved). Their Thm 4.2 is needed only to identify this `cr` with
the generic fibre cardinality. The route's original import from the
introduction of arXiv:1505.04408 is unnecessary and is dropped. The
argument does not depend on the alphabet size.

*Scope.* Vacuous on every computed domain: no strict system with
irreducible `χ_M` was found within any budget. Step (3) is the only part
testable outside PIP; *exploratory scratch observation:* it holds on all
2,856 flat reducible systems enumerated by the verifier and fails on all
1,296 mixed ones.

*Consequence on (F), conditional on the imports of FC2.* `cr ≤ 2` on (F),
so a strict system of a `σ ∈ PIP3` with (F) has only swap-symmetric ordered
sinks. The same conclusion has a derivation that avoids the coincidence
rank and uses only FC1, Theorem A(4) and Barge–Diamond Theorem 1 (written
out at the audit of this note). By the proof of Lemma RL applied to a sink
`S`, `S` contains the blocks of a ray pair `(X_a, X_b)` with `a ≠ b` fixed
by a power of `g`. By FC1 the inflations of an occurrence of `b` in `X_a`
and of an occurrence of `a` in `X_b` start at cuts, with first pairs
`(b,z)` and `(z′,a)`. If `z = a` or `z′ = b`, a block of `S` has first pair
`(b,a)`; its inflations begin with ever longer prefixes of `(X_b, X_a)`,
whose first block is the swap of the first block of `(X_a, X_b)`, so `S`
meets `swap(S)` and equals it. Otherwise `z = z′` is the third letter, and `{a,b}`, `{b,z}`,
`{z,a}` are all first-letter pairs of states, so none is left strongly
coincident (Theorem A(4)), against Barge–Diamond Theorem 1. The verifier
(V1(f)) described this derivation as needing no import; that wording is not
adopted, because the cyclic case is excluded only through Barge–Diamond:
`012/120/201`, where Barge–Diamond's conclusion fails, has the flat system
`(012,120)`, `(120,201)`, `(201,012)` with cyclic first pairs. For flat
phase one, Proposition PD below gives failure of (F) directly.

**Proposition PD (flat phase one ⟹ (F) fails; route label "Theorem D").**
Let `σ ∈ PIP3` with `g(a) = b`, `g(b) = a`, `T = X_a = lim σ^{2k}(a)`,
`T′ = σ(T)`, and suppose `(T,T′)` is strict and flat. Then `f` has a
periodic state `(j,u)` with `u ∈ ℤ³`, `0 < ℓ·u < ℓ_j`; so (F) fails. If `g`
fixes the third letter (endpoint class E; if `g` maps it to `a` or `b`,
endpoint class F), the cycle reached from any tile of that letter has even
length.

*Proof outline.* A tile whose letter never starts a common vertex along
its inflation orbit (the fixed letter in endpoint class E; a suitable tile
on `T` or `T′` in the two sub-cases of endpoint class F) stays strictly
inside a tile of the other tiling at an integral offset; the offsets follow
`f` and are finitely many by the Pisot property. ∎ Irreducibility gives
"common vertex = cut", Barge–Diamond is used only in endpoint class E.
Corrections: "even period" means even cycle length; in endpoint class E
flatness is needed only for evenness (a transposed pair that is not left
strongly coincident already keeps the fixed letter off every common
vertex); the record treated only one of the two sub-cases of endpoint class
F, the other is its mirror.

**Lemma OC (overlap carrier; route label "Lemma B").** Let `σ` be
nonerasing with a positive length eigenvector, `(T,T′)` a strict ray pair
fixed by `τ = σ^m` or exchanged by `σ`, with flat ordered bigon set. Let
`O₀` be the set of ordered overlap types `(i,j,E)`: a `T`-tile `i` at
prefix Parikh vector `Q`, a `T′`-tile `j` at `Q′`, open intervals meeting,
`E = Q − Q′`. Then (a) `O₀ ∩ swap(O₀) = ∅`, where
`swap(i,j,E) = (j,i,−E)`; (b) if `(x,j,E)` and `(j,y,−E)` are in `O₀` with
`0 ≤ ℓ·E < ℓ_j`, then for no admissible depth `n` do `σⁿ(x)` and `σⁿ(y)`
have a coincidence after an equal-Parikh prefix `ρ` with
`ℓ·ρ < βⁿ(ℓ_j − ℓ·E)`. Here `n` is *admissible* if `σⁿ` maps the pair
`(T,T′)` to itself or to `(T′,T)`: `n` a multiple of `m` in the `τ`-fixed
case, every `n ≥ 1` in the exchanged case. (The record uses the word
without defining it; this is the reading the proof outline needs.)

*Proof outline.* (a) Two occurrences with exchanged tracks inflate to the
same pair of supertiles with the same relative shift; a long overlap
contains two consecutive cuts and yields a bigon and its swap. (b) The
coincident letter starts inside the supertile `σⁿ(j)` on the other track in
both occurrences, giving an overlap type and its swap. ∎ No irreducibility
and no Pisot property. Corrections: the sharp form is the quantitative one;
plain left strong coincidence of `(x,y)` is not enough for the proof. The
reported ternary checks exercised only part (a).

### 6.3 Two-ray words

**Lemma RI (recognizability identity; route label "Lemma R").** Let `τ` be
a substitution with `det M_τ ≠ 0` and `u, v` two `τ`-fixed rays. With `K`
the set of equal-Parikh cuts, `E_u = {|τ(u[0:j))| : j ≥ 0}`, `E_v`
likewise: `K ∩ E_u ∩ E_v = τ(K)`, and the same at every level.

*Proof.* `k = |τ(u[0:j))| = |τ(v[0:j′))| ∈ K` gives
`M_τ p(u[0:j)) = M_τ p(v[0:j′))`, hence `j = j′ ∈ K`. ∎ It fails for
Thue–Morse (`det = 0`). The condition is sufficient, not necessary. It
holds on every strict control with `det ≠ 0`, so it carries no
obstruction. The density consequences the route drew from it were not
checked.

**Lemma PO (partner orientation; route label "Lemma O").** Let
`(X_h, X_a)` be a strict ray pair of `τ` and `B` the ordered bigon set of
`(X_h, X_a)`. A *marked pair* is a pair `(x, y)` of bi-infinite words, read
index by index, with a vector `δ ∈ ℤ³`, its Parikh offset (top minus
bottom) at index 0; its *cuts* are the indices at which the running offset
vanishes. The window of `(X_h, X_a)` at index `k` carries
`δ = p(X_h[0:k)) − p(X_a[0:k))`. Let `Z` be a minimal shift-invariant
closed set of marked pairs all of whose windows occur in `(X_h, X_a)`
arbitrarily far out. (i) For primitive `τ` both projections of `Z` are the
whole subshift. (ii) For `τ` a power of a `σ ∈ PIP3`: the Parikh offset of
a pair of `Z` is determined by the unmarked pair; if `B` is flat, the upper
and lower partners of every point are distinct and their cut sets with it
are disjoint (if `(y⁻, x)` and `(x, y⁺)` are in `Z`, then `y⁻ ≠ y⁺` and no
index is a cut of both). (iii) For primitive `τ`: if no cut of `(X_h, X_a)`
has the letter `a` as top first letter, then no occurrence of a prefix of
`X_a` in the top ray starts at a cut (immediate), so by compactness `X_a`
is the top word of a one-sided marked pair `(X_a, W)`, all of whose windows
occur in `(X_h, X_a)`, with nonzero Parikh offset at its origin.

Status of each clause. (i) elementary: a projection of `Z` is a nonempty
closed shift-invariant subset of a minimal subshift. (ii) the route's
record contains **no proof**. The proof below was written at the audit of
this note from the landing verifier's argument (V5) and re-derived there.
It is conditional on Baker–Barge–Kwapisz Prop. 2.3 (which rests on
recognizability) for the offset and for the distinctness of the partners,
and it uses three letters, Barge–Diamond Theorem 1, Theorem A(4) and
flatness for the cut sets. In the first version of this note `B` was "its
ordered bigon set", which could be read as the bigon set of `Z`; the proof
needs a set closed under `τ`-children, so `B` is the bigon set of the ray
pair. (iii) as first stated, "for any primitive `τ`" with flat meaning
`B ∩ swap(B) = ∅`, it is **false**: `012/120/201` with root `(0,1)` is a
counterexample (exploratory scratch observation: all 2,848 occurrences sit
at cuts). The hypothesis above repairs it, and the conclusion is then a
compactness statement: the offsets of the occurrences are nonzero and take
finitely many values. The hypothesis holds for a flat phase-zero system in
PIP3, by Barge–Diamond Theorem 1, Theorem A(4) and flatness (the cut-set
argument below, applied to `(X_h, X_a)` and a cut with first pair `(a, z)`).

*Proof of (ii) (written at the audit of this note).* Apply
Baker–Barge–Kwapisz §2 to `τ`, which is primitive, translation-aperiodic
and Pisot; here `V = ℝ³`, and `E^u ∩ ℤ³ = {0}` because `β` is irrational.

(∗) If a bi-infinite strand `γ` and its translate `γ + w` are both 0-th
terms of elements of the strand space `F_τ^←`, then `w ∈ E^u`. Indeed,
write `w = w_u + w_s` in `E^u ⊕ E^s`. Translating an orbit `(γ_k)` by
`(M_τ^k w_u)` gives an orbit in the same cylinder, so `γ + w_u` is such a
0-th term too. It agrees with `γ + w` modulo `E^s`, so the two are equal by
the injectivity in Prop. 2.3; a strand is not invariant under a nonzero
translation along `E^s`, so `w_s = 0`.

*Offset.* Let `(x, y; δ) ∈ Z`. Its windows occur in `(X_h, X_a)` at indices
`k_n → ∞`. The strands of `X_h` and `X_a` from `0 ∈ ℤ³` are fixed by
`Φ_τ` and lie in the cylinder `C^{R₀}`. Translate both by `−t_n`, where
`t_n` is the `E^u`-component of `p(X_h[0:k_n))`. Along a subsequence these
translates, and for every `j ≥ 0` their `Φ_τ^j`-preimages (the same two
strands translated by `−M_τ^{−j} t_n`), converge (compactness and a
diagonal argument). The limits at `j = 0` are the strand of `x` with
index-0 vertex at some `v ∈ E^s` and the strand of `y` with index-0 vertex
`v − δ`, and both are 0-th terms of elements of `F_τ^←`. If
`(x, y; δ′) ∈ Z` as well, it gives in the same way the strand of `x` with
index-0 vertex `v′ ∈ E^s` and the strand of `y` with index-0 vertex
`v′ − δ′`. By (∗) for `x`, `v′ − v ∈ E^u ∩ E^s = {0}`; by (∗) for `y`,
`δ − δ′ ∈ E^u ∩ ℤ³ = {0}`.

*Distinct partners.* Let `(y, x; δ₁)` and `(x, y; δ₂)` be in `Z`. The same
construction gives strands of `y` and `x` with index-0 vertices `v` and
`v − δ₁`, and strands of `x` and `y` with index-0 vertices `v′` and
`v′ − δ₂`. By (∗) for `x` and for `y`, both `v′ − v + δ₁` and
`v′ − v − δ₂` lie in `E^u`, so `δ₁ + δ₂ ∈ E^u ∩ ℤ³ = {0}`. Then the two
marked pairs have the same cuts, and each bigon `(p, q)` of the first gives
the bigon `(q, p)` of the second. Both are in `B`, against flatness.

*Cut sets.* Let `(y⁻, x)` and `(x, y⁺)` be in `Z` and suppose index `k` is
a cut of both, with letters `p₁, c, p₂` of `y⁻, x, y⁺` after it. The blocks
starting at `k` are in `B`, with first pairs `(p₁, c)` and `(c, p₂)`.
Replace `τ` by a power `τ′` such that the first letters `p₁′, c′, p₂′` of
`τ′(p₁), τ′(c), τ′(p₂)` are fixed by the first-letter map of `τ′`.
Inflating the two blocks by powers of `τ′`, as in the proof of Lemma RL,
gives `τ′`-fixed rays for which `(X_{p₁′}, X_{c′})` and `(X_{c′}, X_{p₂′})`
are concatenations of members of `B`, and `p₁′ ≠ c′ ≠ p₂′` by (E3). If
`p₁′ = p₂′`, the first block `(P, Q)` of the first pair and the first block
`(Q, P)` of the second are both in `B`. Otherwise the three letters are
distinct. `{p₁′, c′}` and `{c′, p₂′}` are first-letter pairs of states of
the strict system `B`, so they are not left strongly coincident (Theorem
A(4)), hence `{p₁′, p₂′}` is (Barge–Diamond Theorem 1; three letters). So
`X_{p₁′}` and `X_{p₂′}` share a tile after equal Parikh prefixes, and with
it all its inflations. Inside a long shared stretch two consecutive cuts of
`(X_{p₁′}, X_{c′})` cut out some `(w, q) ∈ B`. The same two Parikh vertices
are cuts of `(X_{c′}, X_{p₂′})`, consecutive because a cut between them
would be a cut of the first pair, and they cut out `(q, w) ∈ B`. Both cases
contradict flatness. ∎

Not machine-checked. The clause is vacuous on every computed domain: no
strict system with irreducible `χ_M` is known.

**Corollary ST (slice classes; route label "Cor. T").** Let `σ ∈ PIP3` with
letters `{h,a,b}`, `{h,a}` not left strongly coincident,
`m = min(ℓ_h, ℓ_a, ℓ_b)`. For `x ≠ y` let `C_xy` be the set of
`s ∈ (0,m)` such that for some `k` the tile of `σ^k(x)` containing `β^k s`
is also a tile of `σ^k(y)`. Then `C_ha = ∅` and `C_ab ∩ C_hb = ∅`
(elementary). Conditional on Baker–Barge–Kwapisz Lemma 6.2(i) (whose proof
rests on their Thm 4.2 and Remark 4.3) and return module `= ℤ³`: positive
measure of `(0,m) ∖ (C_ab ∪ C_hb)` forces `cr ≥ 3`; if `cr = 2` the union
is conull.

*Proof of the elementary part (written at the audit of this note).* A tile
of `σ^k(h)` that is also a tile of `σ^k(a)` is a left strong coincidence of
`{h,a}`, since `ℓ` is injective on `ℤ³` and equal positions are therefore
equal Parikh prefixes; so `C_ha = ∅`. If `s ∈ C_ab ∩ C_hb`, witnessed at
levels `k₁` and `k₂`, put `k = max(k₁, k₂)`. A shared tile inflates to a
shared patch, and `β^k s < β^k m` lies in all three words, so the tile of
`σ^k(b)` containing `β^k s` is a tile of `σ^k(a)` and of `σ^k(h)`. Hence
`s ∈ C_ha`, a contradiction. ∎ The conditional part has no proof text in
the repository: it was confirmed by one landing verifier (V6) against the
text of Baker–Barge–Kwapisz §6, and that derivation exists only in session
scratch.

Correction: the statement uses neither the strict system nor bounded gaps.
Its only hypothesis beyond PIP3 is that `{h,a}` is not left strongly
coincident, so it has strong-coincidence strength and cannot see bounded
gaps.

**Degree-two defect identity (W5): not new.** The identity
`D₂(τu, τv) = (Λ²M) D₂(u,v)`, `ρ(N) = β`, and "for an irreducible non-Pisot
cubic every strict system has `D₂ ≡ 0`" are Lemma 0, R0 and Theorem R2 of
the [general-structure note](c4-general-structure-2026-11-06.md). The
route's open question "does irreducibility alone exclude strict ray pairs
on three letters" is that note's statement (H). Only one remark was not
found on main: a primitive binary substitution with irreducible `χ_M` has
no strict system (an irreducible noncoincident binary pair has `D₂ ≠ 0`,
so `|det M| ≤ β` and the second root has modulus at most 1; an irreducible
quadratic has no root of modulus 0 or 1, so `χ_M` is of Pisot type, and
Barge–Diamond with `d = 2` finishes). It is the `d = 2` instance of R2's
argument.

## 7. Negative controls: two new, one standing, and what each refutes

### 7.1 Pinned by `kernel/tests/test_c4_reducible_pisot_controls.mojo`

C-D1 and C-D2 are new. `1/012/101` is a standing control: it is one of the
28 strict carriers already pinned on main
(`kernel/tests/test_c4_quotient_spectrum.mojo`: 6 ordered states under
`σ`, Parikh rank 2, quotient root `−1`); new here are its 3-state `σ²`
system, the factorisation of `χ_M` and the behaviour of the screens. All
three are primitive; each has a rational eigenvalue `+1` or `−1` and an
irreducible Pisot quadratic cofactor, so the inflation factor is an
irrational Pisot number and only irreducibility of `χ_M` is missing.

| Control | `det M`, `χ_M` | Strict pairs of fixed rays | Coincident pair | Refutes |
| --- | --- | --- | --- | --- |
| C-D1 `= 011/120/2012` | `−1`, `(x−1)(x²−3x−1)`; `g` the identity | `(X₀,X₁)` and `(X₀,X₂)`: one closed system of 18 ordered states, no state the swap of another, longest state 13, ordered first pairs `(0,1),(0,2)`, last pairs `(2,0),(2,1)`, Parikh rank 2 | `(X₁,X₂)`: left witness `[2,3,2]` | every letter-, window- or seam-level argument for a flat phase-zero hub configuration that does not use irreducibility |
| C-D2 `= 010/1222/2012` | `1`, `(x−1)(x²−4x+1)`; `g` the identity | `(X₀,X₁)`: 21 states, first pair `(0,1)`; `(X₁,X₂)`: 23 states, first pairs `(1,0),(1,2)`; longest state 56; the 23-state system contains the swap of all 21 and none unswapped; Parikh rank 2 | `(X₀,X₂)`: left witness `[3,14,2]` | the same; and its two strict pairs carry two different ordered systems |
| `1/012/101` | `1`, `(x+1)(x²−2x−1)`, `β = 1+√2`; `g = (1,0,1)` | `(X₀,X₁)` under `σ²`: 3 states `(01,10)`, `(21,12)`, `(2101,1012)`, no swaps; under `σ`: those 3 and their swaps | `{0,2}`: left witness `[1,0,1]` | "primitive, unit, irrational Pisot inflation, transposed root ⟹ no strict system" |

Conventions. A left witness is `[level n, zero-based letter index i,
letter]`: `i` letters precede the common letter and the prefixes of length
`i` have equal Parikh vectors. So "diagonal at cut 3" and "at cut 14" in
the attempt's records are letter indices, not cut ordinals; in C-D2 the
common letter follows three noncoincident blocks cut at 6, 9 and 14. On
`ℚ³` modulo the Parikh span, `M` acts by the rational root (`+1`, `+1`,
and `−1` under `σ` resp. `(−1)² = 1` under `σ²`). A state cap one below a
system reports *capped*, never a verdict.

Which screen rejects them is pinned too: `psc.pisot.is_pisot_charpoly`
accepts the cubics of C-D1 and C-D2 (it counts the root `+1` inside
`(−1,1]`), so `is_pip` rejects them through irreducibility alone.

The legal filter of §5 keeps every literal birth type of these strict
systems and of `10/102/211`: `[interior cuts, distinct types, types
missing from the legal list]` is `[69,6,0]` for C-D1, `[83,1,0]` and
`[94,1,0]` for the two systems of C-D2, `[8,6,0]` for `1/012/101` under
`σ`, `[12,3,0]` for `10/102/211`. So the seam criterion is not vacuous and
not unsound on them.

### 7.2 Exploratory scratch observations (not replayable from the repository)

The strict-system landscape for images of length at most 3 is already on
the ledger (entry of 2026-11-06: 276 primitive substitutions carrying 294
strict systems in 28 classes, scratch; the class representatives are pinned
natively, among them `1/012/101`, `1/012/121` and `01/201/112`). The
observations below restrict it to irrational Pisot inflation and add the
geometric reading.

- **(BG) is false** (W2, confirmed by an independent scratch verifier). For
  `1/012/101`, `1/021/202`, `10/102/211`, `01/201/112` and `1/012/121` the
  ordered overlap closure of a stated ray pair from the common vertex is
  finite, contains no coincidence, and every overlap reaches a zero-shift
  overlap: the rays share no tile at any real position and their common
  vertices are relatively dense. Maximum sizes of a not eventually
  coincident configuration: 2, 2, 3, 3, 5.
- **Census** (W2): of the 5,646 primitive ternary substitutions with images
  of length at most 3, reducible `χ_M` and irrational Pisot inflation,
  5,520 have three geometrically eventually coincident letter pairs and 126
  have exactly one; all 126 carry a strict hub configuration, with third
  eigenvalue `+1` (84) or `−1` (42).
- **Two senses of "strict" on reducible controls.** For `10/102/211`,
  `01/201/112`, `1/012/121` and C-D1 every geometric common vertex is an
  equal-Parikh cut (exact lifted closures); for `1/012/101`, `1/021/202`
  and C-D2 about half are not. The first statement would sharpen the
  ledger's "no non-cut common vertex to depth 5 (budget)" for `10/102/211`
  (entry of 2026-11-05, which stands); it is a scratch observation and
  corrects nothing.
- **Class D** (W6): 90 class-D substitutions with images of length 2 to 4
  have two strict ray pairs and one coincident pair, within search budgets
  and unchanged at five times the budget. Only 36 of them have irrational
  Pisot inflation; the other 54 are singular with integer inflation. The
  record's "90 such substitutions" after "unimodular, Pisot-inflation" is
  corrected accordingly.
- **Return module** (V1): on `10/102/211`, `01/201/112` and C-D1 it has
  rank 2, and the lattice of return lengths has index 3 in the lattice
  `ℓ·ℤ³` of tile positions; on C-D2 and `1/012/101` the index is 2. An
  integer height `φ` with `φM = ±φ` takes three consecutive values on the
  whole overlap carrier: the partners of a tiling are stacked linearly.

### 7.3 Where each argument stops on each strict control

| Control (strict system present) | What it lacks | Where the arguments stop |
| --- | --- | --- |
| Thue–Morse `01/10` | irreducibility; `det M = 0`; inflation of degree 1 | GBD: hypothesis fails and the conclusion is false (no coincident pair). FC1's mechanism is realised and *produces* the strict system; FC2 stops at Barge–Diamond (`ν_L = 2 = d`); Theorem P at odd norm. FL: the system is mixed. C2, RI: `det M = 0`. |
| `01/2/120` | singular; inflation 2 | mixed (20 states with all six ordered first pairs, scratch); GBD hypothesis fails. |
| `012/120/201` | `χ = x²(x−3)` | no strongly coincident pair at all; flat with three sheets closing cyclically, so the *conclusion* of FL holds and nothing is contradicted; refutes Lemma PO(iii) for arbitrary primitive `τ`. |
| `1/012/1` | `χ = x(x−2)(x+1)`; periodic | the model flat phase-one system; height `φ = (1,−1,1)`, `φM = −φ`; outside C2 (`det M = 0`). |
| `10/102/211`, `01/201/112` | `χ = (x−1)(x²−2x−2)`, `det M = −2` | `ℓ·(2,0,−1) = 0`: `ℓ` is not injective on `ℤ³`, so the hypotheses of FC1 are not met; FL steps (1)–(3) hold, step (4) fails (return lengths of index 3; both scratch); Theorem P stops at even norm; C2: admissible staggered seams exist; GBD, SBD, DC, OC, RI all **hold**. |
| `1/012/101` | `χ = (x+1)(x²−2x−1)` | unit, odd determinant, and `dim H¹ = 2`, the degree of its inflation (scratch): the arithmetic hypotheses of FC3(b) hold, and so does the analogue of Fork's cohomological hypothesis. Both arguments stop at alignment: the return lengths have index 2 and the two tracks lie in different cosets (scratch), so the strict pair is not in one fibre. `ker(M+I) ≠ 0`, so the mean offset is not forced to vanish. |
| C-D1, C-D2 | `χ = (x−1)·`(Pisot quadratic) | the three-ray configuration of §7.1 holds (pinned); FL steps (1)–(3) hold, step (4) fails (return lengths of index 3, resp. 2; both scratch); C2: the legal filter keeps every birth type; GBD and SBD hold. |

Productive PIP3 controls (no strict system) bound the theorems from the
other side: `01/12/021` fails (F) through the fixed state `(2; (−1,0,1))`
with `(M − I)v = e₀` (pinned by `kernel/tests/test_c4_geometric_f.mojo`),
and `1/02/002`, `01/20/200` fail (F) as well (scratch). So "interior
periodic address ⟹ strict system" is false, and the (F)-class theorems
are sufficient conditions only. The non-Pisot binary `00001/011` is outside
the (F)-class statements, Theorem GBD, Theorem FL and Proposition PD (no
Pisot property, hence no finiteness of relative states or offsets); the
statements that do not assume the Pisot property (§5, Lemma OC, Lemma RI)
apply to it. The abstract plastic-cubic degree-five survivor is not a word
object.

## 8. Why this route to C4 is now known to be circular on the (F) class

The C4 route was kept alive by one asymmetry: C4 follows from all-pairs
strong coincidence, but it only needs to exclude *bounded-gap*
configurations, and a bounded-gap hypothesis might be easier to
contradict. Theorem FC1 removes that asymmetry on the (F) class.

For `σ ∈ PIP3` with (F), every relative state of a vertex of one fixed ray
in the other reaches a vertex state after a uniformly bounded number of
steps. Hence every vertex of either ray becomes a common vertex after `N`
inflations, and the equal-Parikh cuts of **every** pair of `τ`-fixed rays
have gaps at most `β^{mN} ℓ_max`. On (F) the bounded-gap hypothesis is
automatic. So there:

```text
σ has a strict system  ⟺  some pair of distinct g-periodic letters is not left SC
                       ⟺  ¬ SC_all(σ)                       [FC1; elementary]
                       ⟺  cr(σ) = 2  ⟺  not pure discrete   [FC2 and Baker–Barge–Kwapisz Cor. 5.2; conditional]
```

*Corollary H of the (F)-class note, restated* (conditional on the imports
of Theorem FC2 and on Baker–Barge–Kwapisz Cor. 5.2). If no `σ ∈ PIP3` has a
strict system, then every `σ ∈ PIP3` with (F), unit or not, has `cr = 1`:
all letter pairs are strongly coincident on both sides and the tiling flow
has pure discrete spectrum. So a proof of universal C4 contains a proof of
pure discrete spectrum for every ternary irreducible Pisot substitution
with (F). The one criterion for the (F) class in the sources read,
Minervino–Thuswaldner Thm 9.9, has strong coincidence as a hypothesis and
is stated as a tiling property of the self-replicating multiple tiling; its
identification with pure discrete spectrum of the tiling flow for nonunit
`σ` was not checked against a source.

Consequences for the programme:

- On (F), C4 is not weaker than #138. Proving C4 there *is* proving strong
  coincidence there. The sentence "the only content of C4 beyond #138 is
  the bounded-gap slack" ([finite-domain note](c4-finite-domain-closure-2026-11-05.md)
  §4) is sharpened: on (F) that slack is empty.
- (F) is not a thin class: it holds on 1,794 of the 4,554 corpus specimens,
  and on those the conclusion of FC1 is replayed on all 1,956 pairs of
  periodic first letters (pinned). On the other 2,760 specimens every one
  of the 2,790 such pairs has a relative state absorbed by an interior
  cycle (pinned): some vertices never become common vertices, FC1's
  mechanism does not apply, and bounded gaps are not automatic by this
  argument.
- This does not say C4 is false, or harder than #138 (it is implied by
  it). It says that any argument that proves C4 uniformly must, on (F),
  prove all-pairs strong coincidence outright, and so cannot be an
  argument "from bounded gaps".
- On the corpus nothing changes: C4 holds there by the finite-domain
  theorem `C4StandingCorpus`.

## 9. What a proof must use

1. **Irreducibility, beyond ℚ-independence of the tile lengths.** Every
   fact derived at the level of letters, windows, seams, recognizability
   and numeration uses only primitivity, `det M ≠ 0` and bounded
   discrepancy, and is realised by C-D1 and C-D2 (pinned as far as §7.1
   goes; the density and numeration parts are single-pass, §11). The one
   thing those controls lack at the level of lengths, injectivity of `ℓ`
   on `ℤ³`, is exactly what FC1 uses, and FC1 *produces* strict systems
   instead of excluding them. What separates PIP3 from the reducible
   controls in every checked case (scratch) is of higher rank: the return
   module is all of `ℤ³`, so there is no integer height `φ` with
   `φM = ±φ` along which partners stack, and the partners of a tiling must
   close up inside one finite fibre. A proof must use irreducibility in a
   step that fails on C-D1 and C-D2. In this attempt irreducibility
   entered, beyond ℚ-independence of the tile lengths, only through the
   fibre structure (return module `= ℤ³`) and through the Galois structure
   of the spectrum (the mechanism behind Theorem P), both of which are
   statements about the tiling space of `σ`. These are the candidates
   found, not an exhaustive list.
2. **The Barge–Diamond mechanism is not enough.** By Theorem GBD it needs
   only a Pisot inflation of degree at least 2, and the reducible
   Pisot-inflation controls satisfy all of its hypotheses and conclusions
   while carrying strict pairs. It delivers the good pair and never a cut
   pair (§6.1).
3. **The seam criterion's residue test did not separate PIP3 from
   reducible sources** (§5.7; exploratory scratch observation, not a
   theorem). It excluded no nonunit corpus member beyond the endpoint
   filters (all of them have `det M = 2`), reducible `det M = −2` strict
   systems satisfy every condition it uses, and passing to powers adds
   nothing (Proposition PW).
4. **Off (F), the obstruction is interior-type periodic strands.** The
   proof of `cr ≤ 2` covers exactly the case where every member of the
   zero fibre has the origin as a vertex. Off (F), three pairwise
   non-coincident strands must include an interior-type one, which avoids
   every cut of a strict pair; deciding whether it is coincident with the
   pair is an overlap-coincidence question.
5. **On (F) bounded gaps give no leverage** (§8). An argument for C4 that
   is to be weaker than #138 must use the bounded-gap hypothesis; on (F)
   that hypothesis is automatic, so there any proof of C4 is a proof of
   all-pairs left strong coincidence.

Where each standing hypothesis enters the statements of this increment:

| Hypothesis | Used for | Fails on |
| --- | --- | --- |
| `χ_M` irreducible | `ℓ` injective on `ℤ³` (common vertex = equal-Parikh cut; the states of `f`); return module `= ℤ³` (FL step 4, FC2, alignment in Fork); `G₀ = 0` and `χ_{Mⁿ}` minimal for `βⁿ` (Theorem P); `ker(M ± I) = 0` | all reducible controls of §7 |
| Pisot property | finitely many relative states and offsets (FC1, PD); trapping and finiteness in GBD; Barge–Diamond; finite fibres | `00001/011` |
| inflation of degree `≥ 2` | GBD: a nonzero period has a nonzero conjugate | Thue–Morse, `012/120/201`, `01/2/120` |
| `det M ≠ 0` | T1(c), C2, RI | Thue–Morse, `1/012/1`, `012/120/201` |
| `det M` odd | Barge 2015 Lemma 20 and Thm 22; Theorem P; FC3(b),(c); Theorem N | the 1,926 corpus members with `det M = 2`; `10/102/211` |
| `det M = ±1` | Theorem Fork (integral cohomology `ℤ³`, torus classes of index one); Proposition R of the cut-attractor note | nonunit PIP3 |
| three letters | Barge–Diamond gives `ν ≤ 2` and the hub structure | — |
| (F) | FC1, FC2 | 2,760 corpus specimens |

## 10. Remaining open statements, in their sharpest form

1. **On (F): exclude `ν_L = 2`.** For `σ ∈ PIP3` with (F), every pair of
   distinct `g`-periodic letters is left strongly coincident. Equivalent
   there to C4 (FC1, elementary) and, conditional on the imports of FC2
   and on Baker–Barge–Kwapisz Cor. 5.2, to `cr = 1` and to pure discrete
   spectrum. Recorded as proved under the hypotheses of FC3. Open: `det M`
   even; `det M` odd with `tr M ≡ e₂(M)` and `dim H¹ ≥ 5`. That open
   arithmetic class contains 354 of the 510 corpus (F) specimens with two
   periodic letters on both sides: 174 with `det M = 2`, 180 odd (pinned).
   These are class counts, not open cases: on the corpus the statement
   holds (`C4StandingCorpus` with FC1).
2. **Off (F): the zero-fibre form of C4.** No two non-coincident members
   of the zero fibre (the `Φ`-periodic integer strands) have relatively
   dense common vertices; for a given pair, common vertices are relatively
   dense iff the vertices with transient relative state are. This is
   Proposition 3 and Lemma F read in the zero fibre (prior-art lens:
   Sirvent–Solomyak Thm 5.6 (iii′)); it was not separately verified. The
   specific missing step is the zero-fibre route's failed premise: an
   interior-type periodic strand is coincident with one of two
   non-coincident vertex-type strands.
3. **The `cr = 2` wall.** If `cr(σ) ≤ 2`, every ordered sink of a strict
   system is swap-symmetric (Theorem FL). For unit `σ`, with Proposition R
   and Lemma G of the cut-attractor note (conditional on that note's
   imports (I1), (I2); (I2) is Barge–Kwapisz 2006, not re-read there and
   not obtained during this attempt), at `cr = 2` C4 is equivalent to
   `int(R_h ∩ R_a) = int(R_h ∩ R_b) = ∅`; no such form is recorded for
   nonunit `σ`. Theorem P confines `cr = 2` with odd determinant to
   `tr M ≡ e₂(M)` and `dim H¹ ≥ 5`.
4. **Phase one, statement (N).** For `σ ∈ PIP3` and a pair `{a,b}`
   transposed by `g`, the rays `X_a` and `X_b` cannot simultaneously share
   no tile, have common vertices at bounded gaps, and have ordered bigon
   set disjoint from its swap. (N) follows from left strong coincidence of
   the transposed pair; no weaker sufficient statement was found. Flat
   phase one forces `cr ≥ 3` and failure of (F); mixed phase one is
   untouched.
5. **Unit, `dim H¹ = 3`.** By Theorem Fork every strict component has
   forked partners with disjoint cut sets, and (F) fails. Open: exclude
   the fork. Whether `π₁` is a covering is open; nothing is known for
   `dim H¹ ≥ 4` or for nonunit `σ`.
6. **Nonunit.** C4 for nonunit PIP3 has no uniform mechanism on the
   seam-criterion route of §5 (§5.7). The matrix-adic carrier route on main
   is a separate programme and is not assessed here.
7. **Subtile form** (the open quantifier on main, cut-attractor note §7;
   unit `σ` only, conditional on the imports of Proposition R): for every
   unit `σ ∈ PIP3` with `cr(σ) = 2` and every pair `{c,c′}` without a left
   strong-coincidence witness, `int(R_c ∩ R_c′) = ∅`. On that class it is
   equivalent to C4 (item 3). Without the restriction to `cr = 2` only the
   direction of Lemma G is available: the statement is sufficient for C4
   and not known to be equivalent to it. The two-ray-words record describes
   it as of strong-coincidence strength, and that route ends there.

Do not re-run the six routes as posed. A new attempt should start from one
of the statements above, and should say in advance which step fails on
C-D1, C-D2 and `1/012/101`.

## 11. Obstruction-route facts and their verification status

The last two rows concern the nonunit route, a partial verdict; they are
listed here because no verifier re-derived them before the audit of this
note.

| Fact | Route | Status |
| --- | --- | --- |
| Theorem GBD | bd-extension | confirmed with corrections (W1): take `B′ > c₀/(1−ρ)`; "lengths in `ℚ(λ)`" removable; geometric sense essential |
| (BG) false; five counter-models; census 5,646 = 5,520 + 126 | bd-extension | confirmed (W2); scratch |
| Corollary SBD | bd-extension | confirmed with corrections (W3): existential |
| Proposition DC | bd-extension | confirmed with corrections (W4); "coincide on a dense open set" **wrong as written** |
| Branching form "BD+", relative-maximality theorem | bd-extension | single-pass; only the part the proof of DC needs was re-derived |
| Shifts must be restricted to the lattice `ℓ·ℤ³` | bd-extension | single-pass tooling finding |
| Theorem FL | phase-one, two-ray-words | confirmed with corrections (V1): flat only; imports reduced |
| Proposition PD | phase-one | confirmed with corrections (V2) |
| Lemma OC | phase-one | confirmed with corrections (V3) |
| Bigon substitution identities `σ∘U = V∘Σ′`, `S = −N′` | phase-one | single-pass |
| `(M+I)·Ē = 0` | phase-one | single-pass; equivalent to a statement on main |
| "Every nonsingular flat phase-one system found has eigenvalue `−1`" | phase-one | single-pass scratch observation on instances that closed within caps |
| Transposed pairs are left strongly coincident for all PIP3 with images `≤ 5` | phase-one | single-pass scratch scan |
| Lemma RI | two-ray-words | confirmed (V4); its density consequences unchecked |
| Lemma PO | two-ray-words | confirmed with corrections (V5); clause (iii) **false as first stated**; clause (ii) had no recorded proof, and one was written at the audit of this note (§6.3) |
| Corollary ST | two-ray-words | confirmed with corrections (V6) |
| Degree-two identity and consequences | two-ray-words | confirmed with corrections (W5): **not new**, see §6.3 |
| C-D1, C-D2 | two-ray-words | confirmed with corrections (W6); pinned by a Mojo regression |
| "90 such class-D substitutions" | two-ray-words | **corrected** (W6; exploratory scratch observation, counts under search budgets): 36 with irrational Pisot inflation, 54 singular |
| Periodic strict pairs over rational torus points; numeration dictionary | two-ray-words | single-pass |
| Every `g`-cyclic root reaches a diagonal on the corpus, on the shell of maximal image length 4, and on a seeded sample with images `≤ 6`; pre-diagonal runs of 47, 429, 693 bigons | two-ray-words | single-pass scratch scans; budgets not exhausted |
| FC1 "maximal transient 38" | zero-fibre-rank | **withdrawn**: a 3,000-letter prefix scan; the exact value over the complete relative-state closure is 51 (pinned) |
| "`π₁` is not a covering map"; "`ℤ/2` for `1/012/1`" | cohomology | **corrected**: not injective; periodic, quotient `ℤ/3` |
| Covering-degree parity (that route's own "Theorem P", unrelated to Theorem P of §4), cross-seam lemma, ERP proposition | cohomology | not verified; not used |
| Proposition PW (powers add nothing) | nonunit | asserted by the route; proof written at landing; re-derived only at the audit of this note (§5.4) |
| "The carrier cannot see irreducibility over `ℚ`" | nonunit | route remark; not proved, not verified, **not adopted** (§5.7) |

Nothing above was refuted outright. The entries marked wrong, false,
corrected or withdrawn are kept here so that the earlier wording is not
reused.

## 12. Imports

"Read" means read in the primary text during the attempt of 2026-11-15/16,
before any repository code or proof text of this increment was written.

| Source | Statement | Hypotheses | Used in this note for | Read? |
| --- | --- | --- | --- | --- |
| Barge–Diamond, *Coincidence for substitutions of Pisot type*, Bull. Soc. Math. France 130 (2002) 619–626 | Theorem 1: distinct letters `j, r` and `n, k` with `φⁿ(j)`, `φⁿ(r)` having the same `k`-th letter after prefixes with equal abelianisation | substitution of Pisot type: all non-Perron eigenvalues of modulus strictly between 0 and 1; no unimodularity | hub structure; GBD (its proof, read in the length lattice); PD in endpoint class E; PO(ii) and the remark on PO(iii); the FC1 derivation of §6.2 | in full by three routes and reproduced line by line; taken from the repository gate by two others |
| Baker–Barge–Kwapisz, *Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces with an application to β-shifts*, Ann. Inst. Fourier 56 (2006) 2213–2248 | Def. 4.1; Thm 4.2; Remark 4.3; Prop. 2.3; Lemma 6.2(i); Thm 5.1; Cor. 5.2 | primitive, translation-aperiodic, Pisot inflation; reducible and non-unimodular allowed | FL (Def. 4.1); PO(ii) (§2 and Prop. 2.3); ST (Lemma 6.2(i)); §8 and Corollary H (Thm 5.1, Cor. 5.2, through the (F)-class note) | yes. Its sentence "`Σ = Γ` for irreducible Pisot" defers to Barge–Kwapisz 2006, which was not obtained during the attempt, and is replaced by Theorem R on main |
| Barge, *Factors of Pisot tiling spaces and the Coincidence Rank Conjecture*, Bull. Soc. Math. France 143 (2015), arXiv:1301.7094 | as tabulated in the (F)-class note §1: Thm 4(1)–(5); Thm 5; Thm 12; Lemmas 13, 14; Prop. 19; Lemma 20; sequence (4.1); Thm 22 and the count of periodic words in its proof; the proper version of its §4 | primitive, non-periodic Pisot substitution; Thm 22: inflation of degree `d`, odd norm, `cr = 2` ⟹ `dim H¹ ≥ 2d−1` | the (F)-class theorems only | yes (in full by one route); the proofs of Thm 4 and the references for the proper version were not followed |
| Barge–Diamond, *Cohomology in one-dimensional substitution tiling spaces*, Proc. Amer. Math. Soc. 136 (2008), arXiv:math/0702669 | as tabulated in the (F)-class note §1: Lemma 2, Corollary 3, Theorem 4 and its proof | primitive aperiodic | the (F)-class theorems only | yes, by one route |
| Barge, *Pure discrete spectrum for a class of one-dimensional substitution tiling systems*, Discrete Contin. Dyn. Syst. 36 (2016), arXiv:1403.7826 | Lemma 3.11 and Thm 3.13 | primitive Pisot, injective on initial letters, constant on final letters | description only: that hypothesis makes the vertex sets of fibre-mates disjoint, the reverse of what C4 needs | yes |
| Minervino–Thuswaldner, *The geometry of non-unit Pisot substitutions*, arXiv:1402.2002 | Def. 9.3, Prop. 9.4, Thm 9.9 | irreducible Pisot, non-unit allowed | naming (F); the remark after Corollary H in §8; in no proof | yes (those parts) |
| Barge, *The Pisot conjecture for β-substitutions*, arXiv:1505.04408 | §1 items (2)–(3); §3 (Property (W)); Cor. 17 | Pisot β-substitutions | description only: Property (W) concerns the tiling space of the β-substitution itself and does not transfer; the phase-one route's use of §1 is dropped (V1) | abstract, §3 and Cor. 17 only |
| Barge–Kwapisz, *Geometric theory of unimodular Pisot substitutions*, Amer. J. Math. 128 (2006) | — | unimodular | **not obtained during the attempt; no statement of this note imports it.** It is import (I2) of Proposition R on main, which §10 items 3 and 7 quote as conditional | not during the attempt; what was read of it at the audit of the (F)-class notes is recorded in the (F)-class literature note |
| Repository | Theorem A (Lean `StrictSystem.lean`); Propositions 2, 3 and Lemma F (cut-attractor note); Theorem R (periodic-pair fibre gate); §9 eliminator; legal-seams and seam-birth notes | as stated there | throughout | — |

The remaining sources of the (F)-class theorems (Barge–Kellendonk
arXiv:1108.4065; Barge–Bruin–Jones–Sadun arXiv:1001.2027; Akiyama–Lee,
European J. Combin. 39 (2014)) are tabulated in the (F)-class literature
note.

## 13. Stop/go record

- **Proposed claims.** (i) C4 for the families `F1_c`, `F3_c`; (ii) three
  reducible strict controls as executable negative controls; (iii) the
  mechanism statements of §6.
- **Prior art and terminology.** §5.6 for (i). For (iii): Barge–Diamond
  2002 (configurations, eventual coincidence); Barge 2016 (dense eventual
  coincidence under a final-letter hypothesis); coincidence rank and
  fibres in Baker–Barge–Kwapisz 2006 and Barge 2015; the degree-two
  identities on main. The prior-art verifier of the nonunit route checked
  the families against the repository's literature gates and from memory;
  no web search was run for them, and the literature novelty of GBD and
  SBD was not assessed.
- **Hypotheses that transfer.** Barge–Diamond Theorem 1 has no
  unimodularity hypothesis and applies to nonunit PIP3. Barge 2015 Thm 22
  needs odd norm, not unit. **Do not transfer:** anything in
  Baker–Barge–Kwapisz that rests on `Σ = Γ` to the reducible controls
  (return module of index 2 or 3, scratch); Barge 2016 beyond its
  final-letter class; the equal-Parikh form of Barge–Diamond's conclusion
  outside Pisot type.
- **Negative controls.** §7.
- **Decision.** Redirect. (i) is recorded as two instances of the on-main
  eliminator, with no novelty claim for the criterion. (ii) proceeds to a
  Mojo regression. (iii) is recorded as verified necessary conditions and
  an obstruction, with no claim that any of it narrows C4 on PIP3.

## 14. Work shown

### Assumptions and hypotheses

Standing class PIP3 of §1; nonunit matrices allowed throughout except in
Theorem Fork. Each statement of §5 and §6 lists its own hypotheses, and
the table of §9 says where irreducibility, the Pisot property, the degree
of the inflation, `det M ≠ 0`, odd determinant, unimodularity, the
alphabet size and (F) enter. Legality of the words of a strict system is
derived (Lemma RL), not assumed. Imports are in §12. Finite-domain
statements are about the 4,554-member corpus or about the parameter range
`3 ≤ c ≤ 63`; Theorem T3 for all `c ≥ 3` rests on the written tables of
§5.5, not on the regression.

### Derivation / reduction

§5 (proofs of Lemma RL, Theorem T1, Propositions C2 and PW, Theorem T3
with both seam tables); §6 (statements of the obstruction-route results in
their verified forms, each with a proof, a proof outline or neither, as
marked in §4); §8 (the reduction of C4 to all-pairs left strong coincidence
on (F), from Theorem FC1 of the (F)-class note). The finite objects certified by the two regressions are:
for each stated pair of fixed rays of a control, the ordered child closure
of its first balanced block, validated against every literal factor
occurrence; for each family member, the complete list of local birth
types under the four conditions of §5.6 and the legal-predecessor rule;
for each corpus specimen, every `f`-periodic state inside a certified box
and the complete closure of relative states of each pair of periodic first
letters.

### Evidence and replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_reducible_pisot_controls.mojo)
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_geometric_f.mojo)
PYTHONPATH=tools python3 -m claim_governance.cli --root .
```

Both regressions were re-run while this note was written and exited 0
(the first in seconds with a warm build cache, 13–14 s including
compilation at the build stage; the second in about 1m45s on one core).
Each ends with a `require_contract` declaration; neither declares a ledger
claim.

`kernel/tests/test_c4_reducible_pisot_controls.mojo` (helper:
`kernel/psc/c4_seam_families.mojo`) pins:

- C-D1, C-D2 and `1/012/101`: incidence, determinant, cubic, the exact
  factorisation into a rational root and an irreducible Pisot quadratic,
  primitivity, and rejection by every irreducibility screen; the strict
  systems, coincident pairs and filter triples of §7.1.
- `F1_c` and `F3_c` for `3 ≤ c ≤ 63` (61 parameters): the incidence
  matrices and cubics of §5.5, `det M = c`, primitive, irreducible Pisot
  by the corpus screen and the Routh screen; on-main `L_σ` empty for
  `F1_c`; exactly the types `(1,2,2,0)`, `(2,0,1,2)` for `F3_c`, both
  removed by the legal-predecessor rule; legal bigrams of `F3_c` exactly
  `00, 01, 02, 10, 20, 21`; no hub-based phase-zero birth seam at any of
  the 18 hub and track choices.
- Controls against a vacuous pass: at `c = 2` both families are in PIP3
  with `det M = 2` and keep legal types (4 of 4 for `F1_2`, 2 of 4 for
  `F3_2`); `c = 64` exceeds the 64-letter image budget of the on-main
  sieve and is refused, not decided; singular incidence is refused. The
  non-primitive `1/0/22` (`det M = −2`, empty on-main `L_σ`, strict system
  `(01,10)`, `(10,01)`) is refused by the legal list, whose emptiness is an
  exclusion only for primitive input (added to the regression at the audit
  of the code).
- Left strong-coincidence levels `(4,1,5)` and `(1,4,2)` for
  `3 ≤ c ≤ 8`.
- Caps: a state cap one below a system reports capped; an exhausted level
  budget returns no witness; an exhausted word budget raises.

`kernel/tests/test_c4_geometric_f.mojo` (module:
`kernel/psc/c4_geometric_f.mojo`) pins, over the 4,554 corpus specimens on
348 incidence matrices:

- (F) on 1,794 specimens, invariant under image reversal on all 4,554;
  3,756 interior `f`-cycles with 12,828 states, longest period 13; least
  interior period over the other 2,760 specimens
  `1:816 2:252 3:744 4:228 5:492 6:12 7:24 8:72 10:84 11:12 13:24`.
- The bridge to Corollary LC5: terminal leftmost cycles equal
  `2 Σ gcd(|C|,|G|)` on every specimen, 10,584 in all on 2,760 specimens,
  longest 39, none exactly on the 1,794 (F) specimens.
- FC1: 1,956 pairs of periodic first letters on (F) specimens, each of
  their 97,992 relative states reaching a vertex state, maximal transient
  51 `f`-steps (24 pairs); 2,790 pairs on the other specimens, each with a
  relative state absorbed by an interior cycle.
- Arithmetic classes: 2,628 odd determinants, of them 2,136 with
  `dim H¹ ≤ 4`, 1,344 with `tr M ≢ e₂(M)`, 2,352 with either. Of the 1,794
  (F) specimens, 1,284 have an endpoint map with fewer than two periodic
  letters; of the other 510, 84 have odd determinant and `dim H¹ ≤ 4`, 120
  odd determinant and `tr M ≢ e₂(M)`, 156 either, 354 neither (174 with
  `det M = 2`, 180 odd).
- The certified radii: pinned on five fixtures and by their sums (8,562
  over the 348 incidence matrices, 99,078 over the specimens); a search in
  any other box returns no verdict.
- Fail-closed behaviour: non-PIP3 and malformed input, a state or overlap
  cap, a point that is not a state, letters that are not periodic, and an
  orbit closing on an uncertified cycle all raise (`test_refusals`);
  `fc3_profile` refuses non-PIP3 input. The
  module also raises when a radius cannot be certified or exceeds its cap;
  that path is not exercised by the regression. The census counts classes;
  it certifies no coincidence rank, no strong coincidence and no spectrum.

Everything else quoted in this note with a number is an exploratory
scratch observation from session scratch that is not in the repository.

### Negative controls

§7: two new reducible strict controls with irrational Pisot inflation and
the standing control `1/012/101` (pinned), the five geometric
counter-models to (BG) and the two censuses
(scratch), and the table of where each argument stops. Rejected stronger
variants kept on record: (BG); "Barge–Diamond's conclusion holds in the
equal-Parikh sense for reducible Pisot inflation"; "phase one cannot occur
at coincidence rank 2" (flat only); Lemma PO(iii) for arbitrary primitive
`τ`; "`X_a` and `X_b` coincide on a dense open set"; a uniform transient 38
for FC1; "`π₁` is not a covering map". Budget refusals: `c = 64`; capped
closures; the scratch searches' "cap" and "no cut" outcomes are exhausted
budgets, not verdicts.

### Non-claims / remaining gaps

- Universal C4, A1′ (#138), BH (#139), #84, G1 and PSC are open. No
  governed claim changes status and no ledger claim is added.
- Nothing here excludes a strict system for any `σ ∈ PIP3` outside the
  hypotheses of Theorem FC3 and of Proposition C2 (with its instances in
  Theorem T3), and every specimen those statements reach on the corpus
  was already covered by `C4StandingCorpus`.
- No strong coincidence or pure discrete spectrum is asserted on (F)
  outside FC3; `cr ≤ 2` is not asserted off (F); nothing is asserted for
  even determinant beyond FC1, FC2 and the seam criterion.
- Theorem T3 for `c ≥ 64` rests on the written proof only. The families
  are not shown to lie outside what strong coincidence already covers.
- The statements of §6 are necessary conditions and mechanism facts. They
  hold on reducible strict controls and exclude nothing on PIP3. Theorem
  FL and Proposition PD are vacuous on every computed domain.
- Novelty of Theorem GBD and Corollary SBD relative to the literature was
  not assessed.
- The scratch censuses and scans are not evidence of record; a capped or
  cut-free search is not a mathematical verdict.
- The next unresolved quantifiers are those of §10.

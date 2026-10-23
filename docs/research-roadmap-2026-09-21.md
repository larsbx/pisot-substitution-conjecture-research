# PSC research roadmap — 2026-09-21

**Status:** live completion roadmap for the current research frontier. This file is a planning/status surface, not a proof source. The authoritative claim taxonomy remains `docs/claim-status-and-source-map-2026-09-13.md`; theorem statements remain in `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`; machine dependencies remain generated from `tools/make_ledger.py`.

**Standing target:** pure discrete spectrum for primitive irreducible Pisot substitutions in the repository's standing regime, **without** silently adding seed legality, unique decodability, finite injectivity, rational/integer independence, or unimodularity.

**2026-10-23 narrowed targets (read first):** the
[direct-attack frontier](direct-attack-frontier-2026-10-23.md) states how #84,
#138 and #139 have narrowed: #84 is exactly A1′ ∧ BH, #138 is one-sided A1′,
and #139 is the existential occurrence-compatible BH. It also records what is
settled inside each target and ranks the remaining direct lines of attack.
Orientation only; no status change.

**2026-10-23 #139 tracker repair (latest, supersedes tracker status only):**
[issue #139](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/139)
was GitHub-closed as completed at 10:09:55 UTC without satisfying the universal
BH proof obligation and was **reopened** at 17:45:32 UTC. Universal strict-zipper
offset-zero hitting for all cyclic seed-reachable overlaps in ternary PIP
(including non-unit cases) remains **OPEN**. Accepted family-specific hitting
certificates and finite-domain replays do not change that statement; other
historical snapshots below remain unchanged. Exact evidence and closure
criterion: [issue-139 reconciliation](issue-139-tracker-mathematics-reconciliation-2026-10-23.md).
This update changes no claim-status record or mathematical theorem.

**2026-10-23 #138 historical status clarification:** GitHub #138 was closed on
2026-09-26 at 06:15:09 UTC and reopened on 2026-10-01 at 20:50:15 UTC; it
was already **open** at this audit. An earlier closing event is not a
proved theorem. The current indispensable aligned lemma is *one-sided* A1′
for the residual fixed-letter hub pair; the two-sided/suffix statement
remains optional stronger scope. [Dated evidence](issue-138-tracker-history-2026-10-23.md).
No mathematical status or proof-ledger output is changed.

**2026-10-23 G1 status clarification:** do not say the proven relation
`PDS ⇒ G1` remains open. Since 2026-10-04, `PDSImpliesRepoG1` has
status **repository-proved**; `PDSImpliesSeedwiseTermination` is also
repository-proved. Universal `G1` is **open** only in the distinct
unconditional sense because universal PDS/PSC and alternative universal
sufficient premises remain open. These statements are consistent, not
conflicting tracker states. See
[G1/PDS necessity status](g1-pds-necessity-status-2026-10-23.md).
Neither #138's nor #139's tracker correction may demote those completed nodes.


## October 21 continuation beyond accepted class D

PR #298 records completed class-D integration; that gate is not reopened.
The [October 22 scoped G1 corollary](class-d-g1-corollary-2026-10-22.md)
applies the existing half-coincidence implication to that accepted scope.
Both full `b=0` branches have certified uniform hitting depths (minus four,
plus six), although no uniform spectral contraction margin exists there;
their all-level BPA word-length bounds still depend on `a`. This supplies
no universal G1 or spectrum conclusion.
The [class-A run-index proof and replay](p1b-class-a-run-index-2026-10-21.md)
now give a genuine seed-reachable recurrent family with n/10 < L_n <= n+2.
A parameter-independent hitting-depth K is therefore unavailable, even on
the minimal plus slope-one class-A line. Use a run-indexed carrier and a
parameter-dependent rank: B_k -> B_(k-1) is the concrete productive mechanism
already proved for the explicit family. Coverage of all reachable states,
other residual A regions and the residual C domain is still required.
The universal two-obstruction premises remain open; independent human review
of the new written proof remains pending. Finite graphs through n=24 and a
full independent n=18 replay are calibration, not all-parameter coverage.

## PRIMARY COMPLETION THEOREM — 2026-10-19

The project is now organized around one theorem and two universal lemmas.

> **Two-obstruction completion theorem.** For a ternary PIP substitution,
> if **(A)** every aligned pair of distinct letters is eventually coincident
> and **(B)** every cyclic vertex of the unconditionally finite seed-patch
> overlap graph has an offset-zero descendant, then every seed-reachable
> overlap is productive and the tiling flow has pure discrete spectrum.

The proof is now in the manuscript as
`thm:two-obstruction-completion`. It is short because the surrounding
architecture is already closed: seed-patch overlap finiteness,
closed-obstruction extraction, the boundary-coincidence dictionary and the
density-to-PDS spectral bridge are established inputs.

For ternary PIP, the two universal lemmas are already reduced to the exact
forms below:

1. **A1′ / #138 — residual hub-word theorem.** By the endpoint normal form and
   the squaring reduction, a universal proof only has to exclude the
   fixed-letter bad hub edge: if two letters fixed by the first-letter map
   form the residual bad edge, they must be eventually coincident. This
   one-sided statement is sufficient for the completion theorem; reversal is
   not a separate universal premise.
2. **BH / #139 — occurrence-compatible coverage theorem.** Every cyclic
   seed-reachable strict-zipper overlap must enter the reverse offset-zero
   basin through a composable ordered occurrence path. In the non-unit case
   this must respect the full representation; a Euclidean-only or
   unimodular-lattice argument is not sufficient.

These are the **primary mathematical tasks**. G1b-2, SCC Producer, K2,
realization and further censuses are now secondary unless they directly prove
A1′ or BH. The spectral bridge, finite-box sufficiency, necessity of G1 and
the mathematical meaning of the exact certificates are accepted load-bearing
inputs under the project-progression convention; do not reopen them as routine
research tasks.

**Completion criterion:** prove one-sided A1′ and BH universally with no independent
tile-length-independence, legality, FI or unimodularity assumption. Then #84
closes and the general PDS conclusion follows immediately from
`thm:two-obstruction-completion`.


**Review policy:** **Independent human review is a final validation gate, not a research-progress gate.** A `human review pending` label is non-blocking validation debt: proof development, provisional dependency use, and assembly of a complete closure candidate continue. Independent review is performed on the assembled closure chain afterward. The label itself remains truthful and no open mathematical premise is promoted by this policy. Machine source: `claim_governance.toml [review_policy]`.

**Project-acceptance convention (2026-10-19):** when a repository theorem or
finite/scoped certificate is mechanically sufficient at its exact recorded
scope — proof/certificate complete, hypotheses preserved, and required exact
replay/CI receipts present — it is implicitly approved for continued project
progression and may be load-bearing. This is **not** a claim of completed
independent human review. Independent human validation remains the final
validation phase, while finite-domain and family-scoped quantifiers remain
unchanged.

**2026-10-19 reconciliation (`main@e062e330`, after merged PR #277):**
general PSC, #84, #138, #139, formal productivity and G1 remain open. The two
class-D `b=0` boundary lines are no longer pending candidates: PR #277 merged
their complete scoped certificate machinery and exact occurrence-agreement
checks. What remains in class D is exactly the two positive-`b` interiors
`s=±1, a>=0, b>=1`; a literal transport of the `b=0` occurrence spine is
refuted by the recorded rank-one update, so the next theorem must be genuinely
two-parameter and occurrence-aware. Issue #9's 2026-10-07 `completed` closure
is routing/track completion only: C4 itself was not proved, and its residual
hub-word/alignment obligations live in the current C4 notes and successor
issues. Mechanically sufficient scoped results are project-accepted for
progression under the policy above; this changes no universal quantifier and
does not claim independent human review.

**2026-10-16 synchronization (`main@b378392`):** general PSC, #84, #138,
#139, formal productivity, and G1 remain open; no immutable accepted proof of
the general conjecture is present on `main`. The merged Sirvent–Solomyak
transfer and Barge-class imports add exact symbolic-PDS scope, including 1,248
standing-corpus detector witnesses, without changing a universal gate. At that historical snapshot, the residual PIP class-D region had been reduced to two parameter quadrants and the boundary certificates were still unmerged; the 2026-10-19 reconciliation above supersedes that planning state. The Nakaishi source audit, radius-10
boxwalk witness, projected-path semantics correction, K2 conditional result,
and ternary good-exit family are negative controls or conditional reductions,
not closure. Exact occurrence replay and the whole child-closed set of outgoing
branches are now mandatory for #139 work. The current provenance boundary is
`completion-ledger-2026-10-16.md`; PRs #263/#266 were later integrated by merged PR #277; PR #273 remains candidate work.

**2026-10-14 Ω/G1 continuation (`main@7a84a914` inspected):** Ω is a
repository-proved per-specimen equivalence, not uniform productivity. The
existing depth note now assembles the weaker complete-box offset-zero
certificate directly into all-seed G1, using only Ω1 and Proposition 4, and
gives the all-level integer bound `2 L^(K+2)` (§7 of
[bpa-termination-by-overlap-depth-2026-10-02.md](bpa-termination-by-overlap-depth-2026-10-02.md)).
This bypasses the PDS/necessity imports for G1 certification; it does not
prove the universal common-boundary predicate. Work on #139 therefore
continues immediately using the unreviewed repository implications, with
#138 separately required for Ω's productivity/PDS assembly. Preserve the
distinction between seed-graph depth and box recurrent depth, and preserve
the catch-up-free controls: a terminal leftmost cycle is not a strict-zipper
obstruction. General PSC, G1 and the hitting gates remain open.

**2026-10-09 synchronization (`main@4caca9a`, through PR #246):** general PSC,
#84, #138, #139, formal productivity and G1 remain open. Theorem Ω now
supports an exact finite-domain PDS theorem on 145,806 substitutions, while
Theorems L/L′/L″ and W give computer-assisted, human-review-pending boundary
hitting on 47 one-parameter lines and declared two-parameter class-D wedges
(including every PIP class-D member with `r >= q - 1`). These are scoped
closures, not evidence for promoting a universal claim. The current provenance
and obligation boundary is recorded in `completion-ledger-2026-10-09.md`.

**2026-10-02 synchronization:** PRs #181–#188 add the aligned fixed-edge /
alternating-E normal form, exact M-adic carry reduction, two conditional routes
from overlap hypotheses to G1 (manuscript Propositions 5.46–5.47), and complete
separation evidence on the 24,486-member ternary total-image-length-at-most-8 class.
None discharges seedwise overlap productivity, either obstruction branch, G1,
or PSC.

**2026-10-05 synchronization (PRs #210–#213):** two results change the shape of
this plan without moving any open premise.

1. **G1 is now necessary, not optional.** Pure discrete spectrum implies finite
   `B_sigma` (manuscript Proposition `prop:PDS-implies-G1`, ledger
   `PDSImpliesRepoG1`, the Theorem S route; independently audited 2026-10-04,
   **human review pending**). So the finiteness programme is a consequence of
   the conjecture rather than an independent obligation, and a substitution
   with an infinite `B_sigma` would refute PSC.
2. **Former Open Problem 4.24 is answered.** PDS implies termination with
   coincidence from every seed `(ab, ba)`, legal factor or not (manuscript
   Theorem `thm:seedwise`, ledger `PDSImpliesSeedwiseTermination`).

Planning consequence, carried into §11 and §12 below: by Corollary 5 of the
half-coincidence route, **#139 alone suffices for G1**, while #138 is needed
for productivity and PDS but not for finiteness. Closing #139 therefore buys
G1 as a by-product. Neither result discharges #84, #138, #139 or PSC, all of
which remain open. The imports behind Theorem S assume neither unimodularity
nor irreducibility; one soft link is recorded in
`coincidence-rank-imports-literature-gate-2026-10-04.md` §4, and the status
audit is `audit-2026-10-04.md`.

**2026-10-05 weekly completion audit integration (`main@96bed675`, after PR #215):**
the general conjecture remains **open**, but the completion boundary is now
concentrated enough to guide proof effort sharply.

- The shortest route still has exactly one open premise: seedwise overlap
  productivity (#84), split into aligned #138 and strict-zipper #139.
- Unique decodability, including every substitution power, is **closed** from
  full incidence rank; it is not a Level-2 hypothesis and must not be re-added
  as one. The live Level-2 gap is labelled first-return/renewal finiteness
  (G1b-2), not decoding.
- Pure discrete spectrum implies G1 and seedwise termination with coincidence
  from every swap seed; both repository results are independently audited but
  **human review remains pending**. Thus G1 is necessary for PSC, while it is
  still not a premise of the shortest #84 route.
- #139 is the highest-leverage proof branch: its exclusion alone gives G1 by
  Proposition 5.47/Corollary 5. #138 remains independently necessary for the
  productivity/PDS assembly unless a stronger theorem bypasses the split.
- The 2026-10-04 exact evidence materially narrows mechanism search:
  13,260 formal overlap carriers contain no closed survivor; `SC_all` has no
  failure on the 408,798 total-image-length-at-most-10 domain; and the recorded
  PPVC/SC combination yields the finite-domain PDS statement on 145,806
  substitutions, a finite-domain theorem since 2026-10-08 (see below).
- The proposed one-tile reduction is false: 360 standing-corpus substitutions
  have recurrent vertices with no catch-up witness and 210 are entirely
  catch-up-free. The broader total-length-at-most-8 computation has 654
  catch-up-free specimens. One-step M-adic valuation ascent is false on every
  one of those 210 and 654 specimens; observed ascent depth reaches 25.
- Literature use remains hypothesis-sensitive: the Akiyama–Lee
  overlap/strong-coincidence implication needs its height-group hypothesis;
  Barge–Kwapisz geometric realization is unimodular-only; non-unit #139 must
  retain the finite-place coordinates of the Minervino–Thuswaldner
  representation space; and the Barge coincidence-rank fibre criterion used
  in `PDS => G1` still has one source-chain item awaiting primary-proof
  human review.

This roadmap is the weekly completion ledger as well as the live planning
surface: theorem-level results, conditional implications, finite-domain
statements, empirical mechanisms, and review dependencies must remain
separate below. No item in this synchronization promotes #84, #138, #139, G1,
or general PSC.

**Reference update at `main@ff9e5d3`:** PR #154's
[Penrose 2D interface bridge](bridges/penrose-2d-to-psc-interface-program.md)
and PR #157's [Padovan / Plastic-A conjecture program](post-proof-padovan-plastic-a-conjectures-2026-09-23.md)
are non-load-bearing research references. The Penrose analogies are strongest
for P2/G1b-2 and P4 realization; its P1b/#139 comparison supplies no adelic
hitting theorem. PR #191 repairs CI and source integrity. These merges change
no mathematical status or closure priority: #84, #138, #139, G1, and general
PSC remain open.

## 1. Completion architecture

The shortest current route is still G1-free:

```text
primitive irreducible Pisot
=> G1b-1 bounded discrepancy                          [PROVED]
=> finite exact seed-patch overlap graph              [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN: #84 / Open Problem 5.35]
=> coincidence density one / dense good set           [PROVED]
=> pure discrete spectrum                             [IMPORTED: Barge–Štimac–Williams]
```

The only open premise on this route is **seedwise overlap productivity**. The live obstruction normal form splits that gate into two mathematically different branches:

```text
bad closed irreducible nonproductive overlap SCC S
=> aligned branch: S exposes a non-eventually-coincident letter pair
   [#138: two-sided strong coincidence]
OR
=> strict-zipper branch: S has no offset-zero vertex and all ordered
   child factorizations remain strict
   [#139: contracting-space prefix-hitting problem].
```

This split replaces the older roadmap item "aligned/zipper obstruction" with two explicit theorem programs. Neither branch may be hidden inside a computational bound or imported through a theorem with stronger hypotheses.

## 2. Status vocabulary

Use the following distinctions throughout planning and review:

- **Repository theorem:** proved in-repo at the stated generality.
- **Imported theorem:** literature result with exact hypotheses checked.
- **Finite-domain theorem:** exact statement over a fully enumerated finite domain only.
- **Empirical evidence:** exact or numerical observation without universal completeness.
- **Conditional theorem:** valid once named open premises are supplied.
- **Conjectural bridge:** plausible mechanism without a proof or imported theorem.
- **Open dependency:** theorem still required for completion.

A finite census, collar depth, coincidence depth, automaton size, or lack of counterexamples is never promoted to a universal theorem without an independent completeness theorem.

## 3. Stable base — closed and not to be reopened as assumptions

### 3.1 Full incidence rank and unique decodability

**CLOSED.** Full incidence rank follows in the standing irreducible/nonzero-determinant setting. The defect theorem then gives unique decodability of the substitution image code, and the same argument applies to powers because `det M_{sigma^r}=(det M_sigma)^r != 0`.

**Firewall:** UD is a derived theorem. Adding it as an independent standing hypothesis would weaken the target and is prohibited.

### 3.2 G1b-1 bounded discrepancy

**CLOSED.** The PR #69 reconstruction proves bounded discrepancy from primitivity and Pisot contraction. It does not use unimodularity and does not imply finite BPA.

### 3.3 Finite exact seed-overlap graph

**CLOSED.** Bounded discrepancy yields a finite exact graph of overlaps reachable from a periodic swap seed. The periodic comparison patch uses two tile types; `ab` need not be a legal factor of the substitution language.

**Firewall:** seed legality is not a hypothesis of Theorem 5.38 or issue #84.

### 3.4 Bad-SCC normal form

**CLOSED.** A failure of seedwise productivity reduces to a finite child-closed irreducible nonproductive SCC `S` with full-rank intersection-vector span, inherited Galois spectrum, and Perron growth `PF(N_S)=beta`.

**Consequence:** do not search for a rank-deficiency contradiction. The hard obstruction is full rank.

### 3.5 Density-to-PDS bridge

**CLOSED on the repository side plus imported theorem.** The coincidence-density/dense-good-set equivalence is repository-proved; Barge–Štimac–Williams is imported with the needed hypotheses audited. G1 is not a prerequisite of this route.

## 4. P1 — close Open Problem 5.35 / issue #84

### P1a — aligned branch: issue #138

**Target:** prove that every pair of distinct letters in every ternary primitive irreducible Pisot substitution is eventually coincident, and likewise for the reversed substitution, or prove a strictly weaker statement that is still sufficient to eliminate every aligned bad SCC from #84.

**Established inputs:**

- offset-zero/right-aligned seed overlaps are exactly the prefix/suffix strong-coincidence cases;
- a bad aligned SCC exposes a pair that is not eventually coincident;
- Barge–Diamond supplies the repository's one-good-pair input and the hub-letter eliminator/normal form;
- endpoint maps of a bad aligned component are already sharply restricted;
- a conditional automaton bound controls the least coincidence level once nonemptiness is known.

**Exact finite evidence:** the current exact 4,554-member corpus satisfies the tested two-sided strong-coincidence condition. The exact automaton run decides 40,986 ordered letter pairs and re-derives every witness; the maximum prefix/suffix strong-coincidence depth is 15.

This is **finite evidence only**. It does not establish a uniform automaton-size bound, a uniform coincidence-depth bound, or the universal ternary theorem.

#### P1a literature gate

Before adding new machinery, keep the exact scope of the classical results visible:

- Arnoux–Ito: strong-coincidence/Rauzy consequences in the stated unimodular framework;
- Barge–Diamond: all-pairs result for two letters and an existence result in general, not the desired ternary all-pairs theorem;
- Hollander–Solomyak and Sirvent–Solomyak: two-symbol PDS/balanced-pair results in their stated settings;
- known special families: evidence for mechanisms, not a replacement for the universal ternary theorem.

**Attribution firewall:** never cite Barge–Diamond as an all-pairs theorem in alphabet size three.

#### P1a 2026-10-01 milestone

The recurrent first-child pair dynamics is now completely normalized after
fixing a Barge–Diamond-good edge. A bad aligned orbit has only two recurrent
templates:

1. a **fixed bad hub edge**; or
2. the unique **alternating type-E template**, where the hub is fixed and the
   two letters of the good edge are swapped.

There is no recurrent aligned pair cycle of period greater than two. In the
alternating template the good edge never synchronizes at the left endpoint, so
its Barge–Diamond eventual-coincidence witness is necessarily an **interior**
balanced-prefix witness. See
`docs/p1a-aligned-cycle-normal-form-2026-10-01.md`.

#### P1a next proof tasks

1. **A1 — fixed-edge interior forcing (open):** prove the fixed-edge
   interior-forcing lemma using substitution-word / balanced-prefix structure
   beyond the endpoint map. Corollary 2.2 does not supply an interior witness
   for this template.
2. **A2 — alternating-E interior-witness transport (open):** transport the
   interior good-edge witness supplied by Corollary 2.2 into a zero-return
   boundary descendant of one of the two bad hub edges, or derive a
   contradiction with closed nonproductivity. The established interior
   witness is specific to A2.
3. Apply the same reduction to the suffix branch by reversal.
4. If a proposed argument uses Rauzy geometry, classify every imported step as
   unit-only or non-unit-safe before using it.

**Closure evidence:** a proof that eliminates both fixed-edge and alternating-E
aligned templates for all ternary PIP substitutions, with reversal handled
explicitly and no FI, legality, or unimodularity assumption.

### P1b — strict-zipper branch: issue #139

**2026-10-20 UTC scoped advance:** the entire PIP minus class-D branch
p=q-1 now has a boundary-hitting certificate. PR #290 supplies the uniform
a>=2,b>=1 seed carrier; the two omitted strips a=0,1 certify at n=b-1
thresholds 42/72, with every finite prefix checked. A native aggregate replays
b=0, both strips, the core, ranked descent and conditional geometry using the
lock-matched Mojo compiler. Combined with the existing r>=q-1 wedge theorem,
this covers all minus class D. See `p1b-minus-boundary-strips-2026-10-20.md`.
Full Pixi/CI integration and independent human review remain pending. PR #293
reports all plus components complete; its validation/aggregate integration is
separate. Universal #139 remains open, with A/C and growing vertex families
still outside these class-D results.

**Target:** eliminate a closed irreducible nonproductive overlap SCC with no offset-zero vertex by forcing a prefix-Parikh boundary hit.

For an overlap offset `w`, the required hit is

```text
exists m: M^m w in P_m(i) - P_m(j),
```

where `P_m(i)` and `P_m(j)` are proper-prefix Parikh sets. Every vertex of a closed strict-zipper SCC lies on a cycle with ordered increment address `(d_0,...,d_{r-1})` satisfying

```text
(I - M^r) w_0 = sum_{k=0}^{r-1} M^{r-1-k} d_k.
```

Thus the offsets form finitely many purely periodic algebraic addresses. The unresolved step is to force one of them into the prefix-difference set.

#### What is settled negatively

Do **not** spend the next cycle reproving any of the following as if it were sufficient:

- cycle algebra alone;
- a zero-shift-free affine pump contradiction;
- bounded symbolic context by itself;
- generic Perron growth;
- `PF(N_S)=beta` as an immediate contradiction;
- the existing contracting **lower** bound on hitting depth.

The determinant-two regression already contains a six-edge zero-shift-free affine pump inside a productive graph, and the pump survives every tested collar radius. The current lower bound says a hit cannot happen too early; completion needs an upper-bound, recurrence, covering, or separation theorem that forces a hit.

#### P1b literature baseline — completed by PR #141

Issue #139 requires a source-by-source transfer audit:

| Source | Safe role in roadmap | Generality warning |
| --- | --- | --- |
| Ito–Rao | super-coincidence/geometric coincidence machinery in its stated setting | unit/unimodular hypotheses must not be erased |
| Barge–Kwapisz | geometric coincidence and the cited converse machinery | explicitly unimodular; cannot be imported unchanged into the non-unit branch |
| Akiyama–Lee | exact overlap algorithm and residual-component spectral criterion | `rho(residual)=beta` is the hard case, not an automatic contradiction |
| Minervino–Thuswaldner | non-unit Rauzy geometry and representation space with finite-place factors | this is the correct warning against a purely Euclidean internal space |
| Barge 2016/2018 family results | identify classes where PDS is proved and the mechanism used | family theorems do not close the universal PIP branch |

The transfer table is now complete in `p1b-strict-zipper-literature-gate-2026-09-21.md`, with machine-readable hypotheses in `p1b-strict-zipper-transfer-matrix.json`. It leaves one named open obligation, **AdelicPeriodicOffsetHitting**: force a realized purely periodic offset orbit to meet the actual prefix-difference cylinder in the full non-unit representation space.

**2026-10-14 Nakaishi source-transfer stop/go:** The first-entry contradiction used in arXiv:2401.07771v1, §13 Proposition 5 is **not available as an imported recurrence lemma**. Its §12 first-second-coordinate measure satisfies \(s_j=m(E_0\cup H_j)\), while the cumulative first-*joint*-entry measure is \(m(H_j)\). The exact identity includes the additional \(m(E_0\cap H_j)\) term; on the paper's own recurrent fibre that correction converges to \(m(E_0)>0\), so the purported contradiction disappears. **Stop** importing this recurrence-to-polynomial-cancellation implication unchanged. **Proceed** only if a separately proved, hypothesis-sensitive algebraic argument excludes joint returns after an early second-coordinate-only visit, or produces an exact occurrence-compatible target hit without that subtraction. Retain the full non-unit/adelic and ordered-occurrence obligations of #139. Evidence: `nakaishi-2024-first-entry-audit-2026-10-13.md` (2026-10-14 continuation); general PSC, #84, #138, #139 and G1 remain open.


**2026-10-14 Quantifier/scale repair gate (PR #261 reconciliation):** A fully mixing binary SFT already exhibits the positive-measure early-only-then-joint event missing in Nakaishi Proposition 5; its exact rational first-hit probabilities are in the existing Nakaishi audit. A repair via Theorem 3 cannot rest on the single chosen pair (x,y): it must prove **positive-measure algebraic support** (persistent nonvanishing for a measured set, not one point) and **shrinking-scale membership** in \(O_{N_k+1}\) at the actual simultaneous return times (the source's fixed \(B(\epsilon)\) does not imply this). A conditional positive-measure return-exclusion lemma is stated and proved in the audit. Even a repaired symbolic conclusion must provide a fixed-offset, occurrence-labelled witness before transfer to #139. This is a source-transfer refinement, not #139 closure or a new dependency of the shortest route. No enlargement of the current finite census is justified by it.

**2026-10-14 Theorem-3 radius/source and address-projection gate:** A further primary-source audit of Nakaishi arXiv:2401.07771v1 found an **independent statement/proof mismatch**: Definition 9's Archimedean radius for \(O_{d+1}\) scales by \(c^{1/d}\), while Theorem 3's proof equation (16) requires \(c^{1/(n-1)}\), with \(0<c<1\); for visit times \(d\ge n\), the printed neighborhood is **larger** and the proof's claimed bound does not follow. \(O_1\) is undefined by the printed formula. The theorem must not be imported in its printed strength without repair. A restricted exact-diagonal conclusion is recoverable **conditional on the source's Garsia and special-cylinder tail estimates**: synchronized address pairs whose *full adelic images already coincide* satisfy the exact integral identity
\[
 \sum_{k<d}M^k(\pi(p_k)-\pi(q_k))=w.
\]
Irreducibility makes \(z\mapsto\langle z,v\rangle\) injective; legal prefix-suffix paths turn the sum into an occurrence-labelled **unscaled** prefix difference for the depth-\(d\) ancestor letters. The special cylinder makes those two ancestors equal, whereas #139 asks for \(M^d w_{\mathrm{PSC}}\) with the specified fixed realized vertex/letters. Even Fibonacci gives a countercalibration to silently replacing \(w\in D_d\) by \(M^d w\in D_d\). **Proceed** with a strictly stated *diagonal-compatible ancestry and affine-offset transport* lemma, not generic weak mixing or an unproved shift of exponent. In addition, the shrinking-radius limsup of scale-matched joint visits lies on the exact diagonal, so recurrence of a generic positive-measure pair set cannot by itself supply infinitely many such visits. The revised existing audit gives proofs, hypotheses and exact negative control. Nothing here closes #139, #84, #138, G1 or PSC.

**2026-10-14 Exact affine-transport obstruction:** Nakaishi's source prefix-suffix digits have the reverse temporal order from our forward overlap inflation. For prescribed initial integer offset \(u\), replay of those **ordered** digit occurrences yields
\[
u_d=M^d u-\sum_{k<d}M^k(\pi(p_k)-\pi(q_k)).
\]
Thus even an exact source-diagonal polynomial cancellation \(W_d=w_{\rm src}\) forces a zero-offset child only with \(w_{\rm src}=M^d u\), not merely because \(w_{\rm src}\in P_d(i)-P_d(j)\). This is a *proved exact transport criterion*, conditional on occurrence legality for the graph. Moreover, the non-unit quadratic PIP substitution \(a\mapsto aaab,\ b\mapsto ab\), \(M=\left(\begin{smallmatrix}3&1\\1&1\end{smallmatrix}\right)\), admits for every \(d\ge1\) **actual legal SFT address pairs** agreeing from \(d\) onward, with exact adelic diagonal displacement \(W_t=M^{d-1}e_a\) for all \(t\ge d\) and infinitely many synchronized special-cylinder visits, but \(W_t\notin M^t\mathbb Z^2\) at any such \(t\). This *rules out automatic integer-offset ancestry transport from an arbitrary Nakaishi SFT diagonal*, not a transport theorem restricted to seed-patch-realized overlap/tiling Gamma classes. **Proceed** only with a geometric-realization-dependent theorem forcing the correct \(M\)-adic residue, prescribed offset, orientation and actual graph replay; reuse the existing finite-cokernel kernel as a diagnostic, not an oracle for universal forcing. The old need for a scale-matched visit remains if approaching through nonexact pairs. See `nakaishi-2024-first-entry-audit-2026-10-13.md`, §"Exact reverse-address affine transport and a non-unit obstruction". General #139, #84, #138, G1 and PSC remain OPEN.

**2026-10-15 realized-overlap calibration:** An explicit seed-patch interior overlap for the non-unit quadratic substitution a->aaab, b->ab has a recurring nonzero-offset child path.
At the state S=(a,a,e_b), the top-second-a / bottom-first-a child choice returns S.
For every r repetitions, the exact prefix difference is W_r=(M^r-I)e_b, which is not in M^r Z^2 by the parity obstruction e_b not in M Z^2.
The same realized state is productive: S -> (a,a,-e_a+e_b) -> (a,a,0), using different ordered child occurrences.
Thus realized recurrence alone is insufficient for forcing the proposed Nakaishi-to-PSC M-adic transport; the genuinely open target is a child-closed nonproductive SCC, with its entire collection of outgoing realized children.
This is a negative control, not a PSC counterexample or a proof of issue #139. See the updated Nakaishi audit and P1b adelic target specification.

**2026-10-15 two-parameter ternary good-edge theorem:** The Nakaishi realization audit now has a fully **ternary** non-unit PIP family, not just the quadratic calibration. For all integers k>=3, 2<=h<=k, `a -> a^k b c^h, b -> ab, c -> a` is primitive irreducible Pisot with det(M)=-h (proved by exact cubic sign brackets and absence of integer roots). The *actually seed-reachable* overlap S=(a,a,e_b) supports an indefinitely repeatable nonzero child loop whose gain W_t=(M^t-I)e_b lies outside M^t Z^3 at every t>=2. Yet two different legal labelled child choices reach (c,a,0) in ONE inflation and a tile coincidence (a,a,0) in TWO, uniformly in both unbounded parameters. This is a **scoped constructive family theorem for one explicitly identified seed vertex**, not whole-family overlap productivity and not #139 closure. It shows precisely why an individual periodic path has no standing against a **child-closed bad SCC**: a good *alternative* outgoing edge settles that vertex. Further progress must supply a universal *good-branch existence* mechanism across all child-closed nonproductive candidates, not additional one-path congruence controls. See `nakaishi-2024-first-entry-audit-2026-10-13.md` (infinite ternary family) and P1b adelic specification negative control 7. For k>3 or h>2, mathematical validity is independent of the Mojo cubic screen's image-length<=6 executable limit; do not expand the screen silently. General #139/#84/#138/G1/PSC remain open.

**2026-10-16 prior-art correction (stop on family PDS):** The full two-parameter ternary family in the preceding October 15 paragraph is **already globally pure discrete by published literature**, not a new family-level PSC advance. Its images all begin with `a` and end respectively in `c,b,a`; reversal yields `a -> c^h b a^k, b -> ba, c -> a` with **injective initial-letter map and constant final letter**. Since the family is primitive nonperiodic Pisot, **Barge (2016), Theorem 3.13**, gives pure discrete tiling flow for every allowed `k,h`, and reflection preserves that spectrum. **Sirvent–Solomyak (2002), Corollary 5.2** transfers the flow conclusion to the symbolic action for the irreducible Pisot family. These are **already imported** through `docs/sadic-transfer-literature-gate-2026-10-11.md`, ledger `BargeClassFlowPDS`/`BargeClassSymbolicPDS`, and the canonical `psc.barge_class` detector; this is not a new theorem import. The October 15 uniformly short path for one chosen overlap remains an exact local calibration, but does not independently prove the entire family is productive or establish a uniform depth bound for other vertices. Further work on this family as a candidate counterexample to PSC/#139 is **stopped**. Use it only to test proposed all-child good-edge mechanisms, while prioritizing outside-mirror-Barge open class-D/#139 regions. The repository's derived `PDS => PPVC/G1/FP` consequences retain their review-pending status. Full correction: `docs/nakaishi-2024-first-entry-audit-2026-10-13.md` (October 16). The general PSC, #84, #138, and #139 remain OPEN.

**2026-10-16 class-D prior-art stop:** Every class-D word system `x -> x y^p c, c -> c y^q x, y -> c y^r c` has first-letter map `f=(x,c,c)` and last-letter map `g=(c,x,c)`. Their powers satisfy `f^n=f`, `g^odd=(c,x,c)`, `g^even=(x,c,x)`. Thus **for all parameter values and powers**, both first and last letter maps are noninjective and nonconstant; images of `x,c` have different first and last letters, so no common-prefix/suffix rotation exists. This **proves the Barge-class power/rotation shortcut is unavailable on the whole determinant-two class D**, including the now-merged `b=0` boundary certificates (integrated by PR #277) and the still-open `b>0` interiors. This is a literature-applicability stop, not a PDS obstruction; other conjugacies are not excluded. See `p1b-class-d-barge-power-rotation-stop-2026-10-16.md` for the elementary all-powers proof and exact sample Mojo regression. **Continue** on actual uniform boundary-hitting certificates/coverage, not `barge_witness` power sweeps. Universal PSC/#139 statuses remain open.

**2026-10-16 class-D certificate reconciliation (merged by PR #277; project-accepted for progression at its scoped certificate level, no universal promotion):** The full directed-support candidate from PR #263 and the independent occurrence-labelled target-aware cover from PR #266 are integrated as separate canonical Mojo engines with their original sealed evidence packets preserved. On the minus `b=0` line, the complete-template certificate covers every integer `a>=4` (145 vertices, 781 directed edges, offset-zero depth <=4) plus finite prefix `a=0..3`. The target-aware certificate independently covers every `a>=2` using a 145-label seed-containing child-closed upper cover, 139 selected **whole-image occurrence** edges of strict descent and maximum depth 4; its smaller `a=2,3` full graphs differ in directed edge support. Both agree on all labelled states, rank values, and selected edges for `a>=4` under a new independent reconciliation check. The plus `b=0` complete-template candidate covers `a>=7` (718 vertices, 4326 edges, maximum half-depth 6) plus `a=0..6` by uncapped exact field graphs. These are **complete boundary line parameterizations**, not coverage of the two-dimensional residual region.

The exact residual Pisot parameter map from §4d is `s=p-q in {-1,+1}; d=q-r>=2; a=d-2>=0; b=r-2d+2s+2>=0`. It covers every residual PIP class-D member once. Existing Corollary W1 covers `r>=q-1`; the reconciled new certificates address precisely `b=0`, on both signs. **Both interiors `s=±1, a>=0,b>=1` remain OPEN**—neither PR establishes full class-D boundary hitting or general #139. The boundary-line certificates are merged and their integration/reconciliation receipts are part of PR #277; they are project-accepted for progression at this scoped level. This does not cover either positive-`b` interior or promote general #139. The family note `p1b-boundary-hitting-progress-2026-10-08.md` §§4e–4m records full occurrence and parameter proofs, the independent comparison, numerical counts, refusal controls, provenance and next exact uniform (a,b) obligation. Human review is nonblocking but theorem status remains truthful. Do not promote G1/PDS or universal PSC based solely on line candidates.

#### P1b non-unimodular theorem target

The desired theorem must be formulated in the full contracting representation needed by the non-unit case: Euclidean contracting embeddings together with the required finite-place/non-Archimedean factors. A purely Euclidean proof is acceptable only if it separately proves that the omitted finite-place coordinates are irrelevant.

The high-value target is a uniform statement of one of the following forms:

1. **recurrence/covering:** every purely periodic bad offset in the finite digit set must meet a prefix-difference Rauzy piece;
2. **separation:** a closed strict-zipper nonproductive SCC would violate a proven separation property of the full representation;
3. **finite return:** the prefix-difference dynamics has a uniform return mechanism forcing an offset-zero descendant.

The theorem must be uniform in `|S|`; another necessary-condition sieve without a completeness statement is not completion progress.

#### P1b 2026-10-01 milestone

The finite-place side now has an exact M-adic prefix-difference filter. A
level-`m` hit requires the occurrence-labelled prefix difference to be zero
in `Z^3 / M^m Z^3`. On the determinant-two golden regression only 11 of 35
level-two occurrence pairs survive; on the unimodular Tribonacci control all
12 survive, as the trivial cokernel requires.

More importantly, the descaled zero-class candidate sets obey exactly the
existing occurrence-labelled affine overlap update. Thus quotient iteration
alone does not yet supply the missing forcing theorem: after descaling it reconstructs the reverse zero-offset basin of the
same affine graph. A separate finite-quotient completeness or coverage theorem
could still establish entry into that basin and is not excluded by this
identity. See `docs/p1b-madic-carry-reduction-2026-10-01.md`.

#### P1b 2026-10-08 synchronisation

Since the 2026-10-01 milestone, #139's obligation (boundary hitting at every
seed-reachable strict-zipper vertex) is decidable per specimen (`BH ⟺ PPVC`
on the box automaton, #211). On the catch-up-free `|det M| = 2` class it is
the whole of PSC, outside the open part of Theorem K's family (#232,
Proposition Z). It is proved on 47 infinite one-parameter families of
Theorem E's classes: Theorem L (#232), Theorem L′ (#234) and Theorem L″
(`p1b-boundary-hitting-progress-2026-10-08.md`). By Theorem W of the same
note, it is also proved on two-parameter wedges: every PIP member of class D
with `r ≥ q − 1`. These results are computer-assisted and human-review
pending. The universal, uniform-in-`|S|` statement is untouched. The PR-by-PR
account and the ordered next steps are in that note.

#### P1b next proof tasks

1. Cover the rest of class D below `r = q - 1`: first the second
   constant-graph cone, then its Pisot-boundary fringe.
2. Establish two-parameter wedges in classes A and C.
3. Treat the growing seed graphs on the class-A slope-one boundary by vertex
   families rather than a fixed graph.
4. Extract a uniform boundary-hitting depth `K` for the catch-up-free
   determinant-two class. This is the first listed step that would meet #139's
   uniform acceptance criterion on that class.
5. For any broader argument, require a proved occurrence-compatible adelic
   coverage map; preserve ordered child occurrences, exact arithmetic, and the
   existing pump/collar/non-unit controls.

**Closure evidence:** a uniform full-representation hitting/coverage theorem
eliminating every strict-zipper bad SCC, or a further exact reduction that
strictly shrinks that theorem without reverting to another necessary-condition
sieve.

### P1 assembly

Issue #84 closes when the aligned and strict branches are both excluded, or when a single stronger theorem excludes every bad closed SCC directly.

No proof of G1b-2, finite BPA, concentration, wedge productivity, or realization is required by the current shortest PDS theorem.

## 5. P2 — Level 2 / G1b-2 renewal finiteness

**Status: OPEN, stronger parallel program; G1 is now known to be necessary for
PDS, but G1b-2 is not a dependency of the shortest #84 route.**

The target remains:

```text
G1b-1 bounded discrepancy [PROVED]
=> G1b-2 renewal finiteness [OPEN]
=> finite BPA (G1).
```

The decoding issue is closed. Full incidence rank gives `det M != 0`; the
defect-theorem argument gives unique decodability of
`{sigma(a): a in A}`, and the same argument applies to every power because
`det M_{sigma^r} = (det M_sigma)^r != 0`. **UD is therefore a derived theorem,
not a Level-2 assumption.**

What remains open is memory/return control. Bounded discrepancy controls the
difference walk but not the length, labels, order, or return memory of an
irreducible balanced pair. The standing corpus makes the separation explicit:
maximum reachable discrepancy is 14 while a reachable balanced-pair state has
length 48,020.

The useful structural program is

```text
realizable labelled first-return word
=> level-scaled contracting/adelic address
=> finite local return types / uniform discreteness
=> G1b-2.
```

**Retired Level-2 inference:** the old upgrade
`UD => uniformly bounded coincidence padding => finite BPA` is not available.
The complete-cutting phase argument controls only its own recurrence regime,
and the former predecessor-contraction inequality fails because a selected
child can carry only part of the inflated parent while noncoincident mass moves
to siblings. A replacement theorem must control realizable labelled returns,
not merely the norm of the cumulative difference.

**Independence/unimodularity firewall:**

- UD is already derived and may not be assumed as an extra premise.
- Any rational/integer tile-length independence used to identify geometric
  cuts with Parikh cuts must be derived from the standing irreducible/full-
  degree setting at the point of use, not added to the theorem statement.
- A bounded difference alphabet does not imply finite BPA.
- Do not replace the full non-unit internal space by a Euclidean stable plane.
- Do not treat `pi_s(Z^A)` as a discrete lattice.
- Preserve labels and order; the unlabelled cumulative difference walk is not
  a state classifier.

**Closure evidence:** a uniform finite-return theorem for every realizable
labelled first return in the standing PIP regime, with no independent UD,
tile-length-independence, or unimodularity assumption.


## 6. P3 — finite-BPA SCC route

**Status: OPEN parallel route, conditional on G1.**

Once a finite closed recurrent noncoincident carrier exists:

```text
K2 == 0  => concentration problem      [OPEN]
K2 != 0  => wedge productivity problem [OPEN].
```

The degree-two carrier-span theorem is proved. Full rational wedge span is a classification constraint, not a productivity theorem.

The exact 4,554-member corpus has zero survivors in the current degree-two and degree-three finite certificates. Those are finite-domain theorems only.

**Next task:** only pursue a new carrier invariant if it uses ordered/ancestral data absent from the child-count and wedge-span reductions. Do not add another fixed-size sieve unless it has a credible uniform completeness theorem.

## 7. P4 — realization / MEF / coincidence-rank route

**Status: OPEN bridge, secondary.**

Keep distinct:

```text
formal recurrent obstruction
!= global realization
!= survival through a finite collar.
```

The G0–G6 interface remains the governing checklist. The empirical fact that formal producer-free cycles die in tested collars is evidence, not a realization theorem.

**Closure evidence:** a rigorous implication from the formal recurrent obstruction to a globally realized tiling obstruction, or a uniform theorem excluding such realization.

## 8. Computational program

### Current exact evidence

On the declared 4,554-member ternary short-image PIP corpus:

- overlap graphs built / capped / failed: `4554 / 0 / 0`;
- total exact overlap vertices: `1,118,850`;
- largest graph: `2,640`;
- specimens containing a nonproductive overlap: `0`;
- maximum first-coincidence depth: `18`;
- maximum first left-aligned depth: `17`;
- maximum prefix/suffix strong-coincidence depth: `15`;
- ordered letter pairs decided by the coincidence automata: `40,986`, with
  every witness re-derived;
- unit/non-unit split: 2,628 unimodular and 1,926 determinant-two specimens;
- maximum reachable balanced-pair discrepancy is 14 while a reachable state
  reaches length 48,020.

The exact formal-carrier census on the same corpus is a stronger negative
control than the historical collar heuristic:

- formal carriers: **13,260**;
- realized / unrealized: **6,078 / 7,182**;
- closed carriers: **0** in both classes;
- formal nonproductive states outside the certified box: **0**.

See `evidence/formal-overlap-carriers-2026-10-04/summary.txt`. The old
unreproducible historical figures for producer-free cycles/collar death are
not a closure input.

The exact strong-coincidence census reports no `SC_all` failure on:

- the standing 4,554 corpus;
- the 24,486 total-image-length-at-most-8 domain;
- the 135,990 image-length-at-most-4 domain;
- the 408,798 total-image-length-at-most-10 domain.

With the separately recorded PPVC runs, the repository records a
**finite-domain PDS statement on 145,806 substitutions** (the union of image
length at most 4 and total image length at most 8). This is not a universal
theorem. *Update 2026-10-08:* it is recorded as the finite-domain theorem
`BoundedPureDiscreteSpectrum`. It no longer depends on Proposition V(2) or
Theorem B: Theorem Ω of `docs/pds-certificate-from-the-box-automaton-2026-10-07.md`
needs only the elementary step 1 of Proposition V, and either the imported
Lee–Moody–Solomyak criterion or Theorem 5.38. The two larger rows are guarded
by `.github/workflows/box-automaton-evidence.yml`. See also
`docs/strong-coincidence-census-2026-10-04.md`.

The exact catch-up/hit-witness census falsifies the proposed universal
one-tile reduction. Among 1,154,040 recurrent nonzero vertices in the standing
corpus, 1,056,816 reach a catch-up witness and 97,224 are simultaneous-only;
360 substitutions fail universal catch-up and 210 are entirely catch-up-free.
The total-image-length-at-most-8 computation contains 654 catch-up-free
substitutions. The proposed one-step M-adic valuation ascent then fails on all
210 and all 654 catch-up-free specimens; observed ascent depth reaches 25.

On the broader 24,486-member total-image-length-at-most-8 class, the canonical
separation sweep completed with no inconclusive specimen at its declared caps:
23,634 specimens have finite least separation radius (maximum `9`), while
852 have an exact proper-power collapse witness by level `6`. The radius
histogram is
`1:2264, 2:13688, 3:6092, 4:1230, 5:288, 6:60, 9:12`, independently
reproduced.

The exact cubic arithmetic audit reports zero disagreements against the
independent oracle on its declared tests, including wide-magnitude
Perron-sign checks.

### Generalization warning

The 4,554 corpus is not determinant-representative of the full non-unit
problem. The broader image-length-at-most-four screen contains determinant
classes `-2,-1,+1,+2,+3`, whereas the standing corpus contains only
`-1,+1,+2`.

Therefore determinant-two success or failure must not be promoted to "the
non-unimodular case", and no finite-domain depth/radius/collar maximum is a
universal bound without an independent completeness theorem.

### Role of computation going forward

Use computation to:

- falsify a named proposed universal lemma quickly;
- retain minimal replayable countermodels;
- measure which extra ordered/address data separate good from bad recurrence;
- audit source-to-code theorem predicates and finite-domain theorem premises;
- stress non-unit determinant classes outside the original corpus.

Do not use another deeper finite search as the closure condition for P1a,
P1b, or G1b-2 unless a separate theorem proves the search complete.


## 9. Hypothesis and attribution firewall

Every roadmap item must fail review if it silently uses any of the following:

1. **Seed legality:** `ab` need not be a language factor.
2. **Independent tile-length independence:** derive rational/integer
   independence from the standing irreducible/full-degree setting where used;
   cite that derivation at every load-bearing balanced-cut step.
3. **Independent UD:** UD, including UD for powers, is already derived from
   full incidence rank and may not be promoted to a standing assumption.
4. **FI / boundary injectivity / prefix-suffix permutation:** extra hypotheses
   unless explicitly stated as a restricted theorem.
5. **Unimodularity:** `|det M|=1` may define a restricted subtheorem, never
   the general completion theorem.
6. **Purely Euclidean non-unit geometry:** forbidden unless the finite-place
   coordinates are proved irrelevant. For #139, the Minervino–Thuswaldner
   adelic representation is the safe ambient model.
7. **Stable-lattice shortcut:** `pi_s(Z^A)` is not to be treated as a
   discrete lattice in the needed non-unit generality.
8. **Formal-to-real realization:** a graph cycle is not automatically a
   realized tiling object.
9. **Finite-search completeness:** no corpus/collar/depth threshold is
   universal without an independent theorem.
10. **Rank deficiency:** bad overlap SCCs are already known to be full rank.
11. **Residual spectral gap by naming:** Akiyama–Lee makes the residual
    spectral comparison load-bearing; `rho=beta` is the hard case, not an
    automatic contradiction.
12. **Akiyama–Lee strong-coincidence shortcut:** do not import an
    overlap-coincidence-to-strong-coincidence implication without its
    height-group hypothesis. The non-unit project route supplies the needed
    return/height information only through the separately proved Theorem R,
    which remains human-review pending.
13. **Barge–Kwapisz generalization:** their geometric-realization machinery is
    unimodular; deleting that hypothesis would silently change the theorem.
14. **Coincidence-rank source-chain overstatement:** `PDS => G1` is
    repository-proved at the current ledger status, but the imported
    disjoint-fibre/coincidence-rank item recorded from Barge still has a
    primary-proof source-chain check pending. Preserve the human-review flag.
15. **Strong-coincidence over-attribution:** do not turn the two-letter
    Barge–Diamond result into a ternary all-pairs theorem.
16. **Special-family promotion:** beta-substitution, injective-initial /
    constant-final, or other family theorems settle those classes only.
17. **Preprint promotion:** claimed general proofs remain non-load-bearing
    until their hypotheses, theorem version, and proof status are independently
    validated.

The generality audit is part of completion, not editorial cleanup: any proof
that reaches PSC only after inserting independence, legality, FI, or
unimodularity has proved a weaker theorem and does not close the roadmap.


## 10. Retired or demoted attacks

Do not spend primary proof effort on:

- `UD => bounded total padding`;
- bounded discrepancy alone `=>` finite BPA;
- the old predecessor-contraction inequality for a selected BPA child;
- naive contraction of the zero-sum hyperplane;
- uniformly short cores in every long balanced state;
- unlabelled difference-walk classification;
- universal exclusion of recurrent noncoincident cycles;
- one-step descent of a contracting norm as the forcing theorem;
- endpoint-only hitting;
- the claim that every recurrent vertex reaches a catch-up witness;
- one-step M-adic valuation ascent on the catch-up-free class;
- a universal law `K_V <= c/log(1/mu)` without new structure;
- rank-deficient bad SCCs;
- generic Perron-growth contradiction;
- automatic `rho(residual)<beta`;
- affine-cycle pumping without symbolic/realization control;
- bounded collars as a completeness theorem;
- a unimodular-only argument presented as general PSC;
- another fixed-size SCC sieve without a path to uniformity.

Countermodels and failed routes remain part of the project evidence and should
stay replayable. A falsified bridge is a closed item in the completion ledger:
do not quietly resurrect it under a new name.


## 11. Prioritized completion ledger

| Priority | Item | Status | Evidence needed to close | Immediate next deliverable |
| --- | --- | --- | --- | --- |
| **P0** | Status/provenance synchronization | reconciled through `main@e062e330`; this roadmap is the live completion surface | roadmap, proof ladder, claim map, manuscript, generated ledger and README preserve the same theorem/review boundary | keep imported/scoped theorems, conditional reductions, negative controls, open PR candidates, and universal open claims distinct |
| **P1b** | Strict-zipper hitting (#139) | **OPEN critical; highest leverage** — class D accepted through #298; explicit class-A family has n/10 < L_n <= n+2 | prove occurrence-compatible coverage of all residual A/C states | use run-indexed carriers and parameter-dependent ranks; a parameter-independent K is refuted |
| **P1a** | Aligned strong coincidence (#138) | **OPEN critical; the two templates are one at the square (Theorem C, 2026-10-05); A1′ proved on the whole catch-up-free `|det M| = 2` class (Theorem E), with all-pairs strong coincidence on its two-odd-letter part (Corollary H1) and outside one explicit family (Theorem K); inside that family Theorems Φ, Λ, Λ′, Λ″ close four `Delta` cells and Theorem Ζ every `Delta` with `Z_2` bounded (2026-10-07)** | uniform proof of A1′ (a bad edge whose letters are both `h`-fixed is eventually coincident), including reversal | on Theorem K's family, close unbounded `Z_2` (Lemma P1 linearized, `2 zfloor`; A1′ note §3m); in general, prove A1′ from the fixed-letter hypothesis, not via transitivity of eventual coincidence |
| **P1** | Seedwise overlap productivity (#84) | **OPEN — sole shortest-route premise** | P1a + P1b, or one stronger theorem excluding every bad closed SCC | assemble only after branch closure; do not substitute a larger finite census |
| **Validation** | Independent human review, including the `PDS => G1` dependency package | **FINAL validation debt, non-blocking** — mechanically sufficient results are project-accepted for progression at their exact scopes; this is not an independent-human-review claim | after a complete closure candidate exists, independently review the assembled chain, including Theorem R, Proposition F, Theorem B/Lemma C and the Barge fibre/coincidence-rank source chain | do not divert P1 work to review gating; preserve truthful `human review pending` labels and perform final review after closure assembly |
| **P2** | G1b-2 renewal finiteness | **OPEN parallel; G1 is necessary for PDS but this is the least load-bearing of the three G1 routes** | uniform finite-return theorem for realizable labelled first returns | develop non-unit level-scaled labelled return/address theory; do not reuse UD-padding or predecessor contraction |
| **P3a** | Concentration, `K2=0` | **OPEN parallel under G1** | uniform exclusion of strict zero-wedge closed carriers | use ordered/ancestral information absent from current span data |
| **P3b** | Wedge productivity, `K2!=0` | **OPEN parallel under G1** | theorem converting full wedge span plus recurrence/order into coincidence | identify an order-sensitive invariant beyond the existing span classification |
| **P4** | Realization / MEF bridge | **OPEN secondary** | theorem relating formal recurrence to global realization, or excluding realization uniformly | preserve the formal/realized/collar firewall while testing any candidate bridge |
| **Support** | Exact computation and arithmetic | **strong finite evidence, not universal closure** — 13,260 formal carriers with no closed survivor; `SC_all` no failure through 408,798; finite-domain PDS statement on 145,806 | no amount of additional depth closes PSC without a completeness theorem | use exact runs to kill named mechanisms and preserve minimal countermodels, especially across non-unit determinant classes |
| **Estate** | Verification/provenance safeguards | **partially open** — large PPVC runs remain outside CI and branch protection/enforced status checks are administrative gaps | CI/governance coverage matching the claims actually cited | improve verification plumbing without changing mathematical status |


## 12. Highest-value task order

For the next research cycle:

1. **#139: extend beyond accepted class D with run-indexed coverage.**
   Preserve #298's accepted scope and receipts. The exact A/C residual map
   and minimal class-A family are in the October 21 continuation above.
   Extend its explicit descending B_k family to a complete seed-reachable
   carrier. Every proposed quotient path must lift to an ordered occurrence
   path at the same parameter. The proved unbounded hitting depth rules out
   a constant-depth reduction; parameter-dependent termination remains viable.
2. **#138 template exclusion in parallel.** The aligned recurrent dynamics has
   only a fixed bad hub edge (A1) or the alternating type-E template (A2).
   For A1, prove the open fixed-edge interior-forcing lemma using
   substitution-word / balanced-prefix structure. For A2 only, transport the
   interior Barge–Diamond-good-edge witness supplied by Corollary 2.2 into a
   zero-return boundary descendant or derive a contradiction with closed
   nonproductivity. Handle both suffix cases by reversal. Theorem C
   (`p1a-template-collapse-2026-10-05.md`) makes the two templates one at the
   square: the obligation is A1′, *two one-sided fixed points anchored at a
   common point share a tile*. On the catch-up-free `|det M| = 2` class it is
   proved (Theorem E), and all-pairs strong coincidence holds there except on
   one explicit family (Theorem K, `p1a-a1-prime-2026-10-05.md` §3e); inside
   it the cells `delta = e_z`, `(s, Delta) = (+1, 1), (−1, −1), (−1, 0)` and
   every `Delta` with `s = +1, Z_2 <= 2` or `s = −1, Z_2 <= 3` are closed
   (Theorems Φ, Λ, Λ′, Λ″, Ζ; §§3g–3m). Unbounded `Z_2` is the open part,
   where Lemma P1 is needed only linearly (side-notes ledger, 2026-10-07).
3. **Keep review debt off the mathematical critical path.**
   Continue directly toward complete closure using correctly classified
   repository proofs and imports even when they remain `human review pending`.
   Preserve those labels, collect the source-chain obligations, and perform
   independent human review on the assembled closure chain as the final
   validation phase rather than as a prerequisite for P1 work.
4. **Keep G1b-2 active as the Level-2 theorem, not as a hidden PSC dependency.**
   The target is labelled first-return finiteness in the full non-unit
   representation. UD is closed; bounded discrepancy and a finite difference
   alphabet do not control return memory.
5. **Use the catch-up-free and affine-pump specimens as mandatory negative
   controls.** Any proposed local monotone, valuation ascent, Euclidean-only
   hitting theorem, or endpoint-only forcing rule must first survive the 210
   standing and 654 total-length-at-most-8 catch-up-free cases.
6. **Do not expand fixed-size sieves unless they test a specific uniform
   lemma.** The 408,798-substitution `SC_all` result and 145,806 finite-domain
   PDS statement are calibration evidence, not substitutes for #138/#139.
7. **Enforce the hypothesis firewall during proof construction, not after it.**
   Every use of tile-length independence, a lattice, a torus, a Euclidean
   internal space, strong coincidence, or coincidence rank must carry the
   derivation/import that makes it valid in the standing non-unit target.

A successful week is not "more specimens passed." It is one of:

- P1b reduced to a strictly smaller source-checked non-unit hitting theorem;
- P1a reduced to a strictly smaller endpoint/occurrence theorem;
- one of those theorems proved;
- a complete closure candidate assembled with its pending human-review items collected for final validation;
- G1b-2 advanced by a genuine labelled-return finiteness lemma;
- or a proposed bridge falsified by a retained exact countermodel, thereby
  shrinking the search space without weakening the hypothesis firewall.


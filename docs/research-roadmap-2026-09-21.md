# PSC research roadmap — 2026-09-21

**Status:** live completion roadmap for the current research frontier. This file is a planning/status surface, not a proof source. The authoritative claim taxonomy remains `docs/claim-status-and-source-map-2026-09-13.md`; theorem statements remain in `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`; machine dependencies remain generated from `scripts/make_ledger.py`.

**Standing target:** pure discrete spectrum for primitive irreducible Pisot substitutions in the repository's standing regime, **without** silently adding seed legality, unique decodability, finite injectivity, rational/integer independence, or unimodularity.

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

#### P1a next proof tasks

1. Write the exact ternary propagation lemma needed after fixing a Barge–Diamond good pair.
2. Express every surviving bad pair through the hub-star and endpoint-map normal forms.
3. Use recurrence of the first-/last-letter maps to show that a surviving bad pair forces a forbidden good pair, or isolate the exact new invariant still missing.
4. If a proposed argument uses Rauzy geometry, classify every imported step as unit-only or non-unit-safe before using it.

**Closure evidence:** a proof that eliminates every aligned bad SCC for all ternary PIP substitutions, with the reversed-substitution statement handled explicitly and no FI, legality, or unimodularity assumption.

### P1b — strict-zipper branch: issue #139

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

#### P1b non-unimodular theorem target

The desired theorem must be formulated in the full contracting representation needed by the non-unit case: Euclidean contracting embeddings together with the required finite-place/non-Archimedean factors. A purely Euclidean proof is acceptable only if it separately proves that the omitted finite-place coordinates are irrelevant.

The high-value target is a uniform statement of one of the following forms:

1. **recurrence/covering:** every purely periodic bad offset in the finite digit set must meet a prefix-difference Rauzy piece;
2. **separation:** a closed strict-zipper nonproductive SCC would violate a proven separation property of the full representation;
3. **finite return:** the prefix-difference dynamics has a uniform return mechanism forcing an offset-zero descendant.

The theorem must be uniform in `|S|`; another necessary-condition sieve without a completeness statement is not completion progress.

#### P1b next proof tasks

1. Define the strict-zipper offset and prefix-difference cylinder in the non-unit representation space, including finite-place coordinates.
2. State the smallest recurrence or coverage lemma that proves `AdelicPeriodicOffsetHitting` uniformly in the chosen closed SCC.
3. Test that lemma first against the known affine-pump and collar countermodels.
4. Only then build new Mojo instrumentation, preserving ordered child occurrences and exact arithmetic.

**Closure evidence:** a uniform hitting theorem eliminating every strict-zipper bad SCC, or an exact proof that the standard super-coincidence machinery does not close the residual obligation together with a strictly smaller named theorem gap.

### P1 assembly

Issue #84 closes when the aligned and strict branches are both excluded, or when a single stronger theorem excludes every bad closed SCC directly.

No proof of G1b-2, finite BPA, concentration, wedge productivity, or realization is required by the current shortest PDS theorem.

## 5. P2 — Level 2 / G1b-2 renewal finiteness

**Status: OPEN, stronger parallel program.**

The target remains:

```text
G1b-1 bounded discrepancy [PROVED]
=> G1b-2 renewal finiteness [OPEN]
=> finite BPA (G1).
```

Bounded discrepancy controls the difference walk but not the length or labelled memory of an irreducible balanced pair. The corpus already exhibits this separation: discrepancy is at most 14 while reachable balanced-pair length reaches at least 48,020.

The useful structural program is

```text
realizable labelled first-return word
=> level-scaled contracting/Rauzy address
=> finite local return types / uniform discreteness
=> G1b-2.
```

**Independence/unimodularity firewall:**

- UD is already derived and may not be assumed as an extra premise.
- A bounded difference alphabet does not imply finite BPA.
- Do not replace the full non-unit internal space by a Euclidean stable plane.
- Do not treat `pi_s(Z^A)` as a discrete lattice.
- Preserve labels and order; the unlabelled cumulative difference walk is not a state classifier.

**Closure evidence:** a uniform finite-return theorem for every realizable labelled first return in the standing PIP regime.

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
- ordered letter pairs decided by the coincidence automata: `40,986`, with every witness re-derived;
- unit/non-unit split on this corpus: 2,628 unimodular and 1,926 determinant-two specimens;
- proper-power collapse occurs only on the non-unit branch in this domain, but zero-shift-free pumps occur on both branches, including 2,598 of 2,628 unimodular specimens.

The exact cubic arithmetic audit reports zero disagreements against the independent oracle on its declared tests, including wide-magnitude Perron-sign checks.

### Generalization warning

The 4,554 corpus is not determinant-representative of the full non-unit problem. The broader image-length-at-most-four screen contains 135,990 specimens and determinant classes `-2,-1,+1,+2,+3`, whereas the declared 4,554 corpus contains only `-1,+1,+2`.

Therefore determinant-two success or failure must not be promoted to "the non-unimodular case."

### Role of computation going forward

Use computation to:

- falsify proposed universal lemmas quickly;
- retain minimal replayable countermodels;
- measure which extra ordered/address data separate good from bad recurrence;
- audit source-to-code theorem predicates;
- stress non-unit determinant classes outside the original corpus.

Do not use another deeper finite search as the closure condition for P1a, P1b, or G1b-2 unless a separate theorem proves the search complete.

## 9. Hypothesis and attribution firewall

Every roadmap item must fail review if it silently uses any of the following:

1. **Seed legality:** `ab` need not be a language factor.
2. **Independent tile-length independence:** derive rational/integer independence from irreducibility where used.
3. **Independent UD:** UD is already derived.
4. **FI / boundary injectivity / prefix-suffix permutation:** extra hypotheses unless explicitly stated as a restricted theorem.
5. **Unimodularity:** `|det M|=1` may define a restricted subtheorem, never the general completion theorem.
6. **Purely Euclidean non-unit geometry:** forbidden unless finite-place coordinates are proved irrelevant.
7. **Stable-lattice shortcut:** `pi_s(Z^A)` is not to be treated as a discrete lattice in the needed generality.
8. **Formal-to-real realization:** a graph cycle is not automatically a realized tiling object.
9. **Finite-search completeness:** no corpus/collar/depth threshold is universal without an independent theorem.
10. **Rank deficiency:** bad overlap SCCs are already known to be full rank.
11. **Residual spectral gap by naming:** Akiyama–Lee makes the residual spectral comparison load-bearing; `rho=beta` is the hard case.
12. **Strong-coincidence over-attribution:** do not turn the two-letter Barge–Diamond result into a ternary all-pairs theorem.
13. **Preprint promotion:** claimed general proofs remain non-load-bearing until their hypotheses and proof status are independently validated.

## 10. Retired or demoted attacks

Do not spend primary proof effort on:

- `UD => bounded total padding`;
- bounded discrepancy alone `=>` finite BPA;
- naive contraction of the zero-sum hyperplane;
- uniformly short cores in every long balanced state;
- unlabelled difference-walk classification;
- rank-deficient bad SCCs;
- generic Perron-growth contradiction;
- automatic `rho(residual)<beta`;
- affine-cycle pumping without symbolic/realization control;
- bounded collars as a completeness theorem;
- a unimodular-only argument presented as general PSC;
- another fixed-size SCC sieve without a path to uniformity.

Countermodels and failed routes remain part of the project evidence and should stay replayable.

## 11. Prioritized completion ledger

| Priority | Item | Status | Evidence needed to close | Immediate next deliverable |
| --- | --- | --- | --- | --- |
| **P0** | Status/provenance synchronization | ongoing | roadmap, proof ladder, claim map, manuscript, ledger and README agree on the same theorem boundary | land this roadmap and keep issue #84/#138/#139 wording synchronized |
| **P1a** | Aligned strong coincidence (#138) | **OPEN critical** | uniform elimination of every aligned bad SCC for ternary PIP, including reversal | propagation theorem from one good pair through hub-star/endpoint recurrence |
| **P1b** | Strict-zipper hitting (#139) | **OPEN critical; literature gate complete** | uniform non-unit-safe `AdelicPeriodicOffsetHitting` theorem | define the full-representation prefix-difference cylinder and a complete recurrence/coverage lemma |
| **P1** | Seedwise overlap productivity (#84) | **OPEN — only shortest-route premise** | P1a + P1b, or one stronger theorem excluding every bad SCC | assemble after branch theorems; do not replace with larger finite sieves |
| **P2** | G1b-2 renewal finiteness | **OPEN parallel** | uniform finite-return theorem for realizable labelled first returns | develop non-unit level-scaled address/return theory |
| **P3a** | Concentration, `K2=0` | **OPEN parallel** | uniform exclusion of strict zero-wedge closed carriers | use ordered/ancestral information absent from current span data |
| **P3b** | Wedge productivity, `K2!=0` | **OPEN parallel** | theorem converting the surviving recurrence/order constraints into coincidence | identify the missing invariant beyond full wedge span |
| **P4** | Realization / MEF bridge | **OPEN secondary** | theorem relating formal recurrence to global realization, or excluding realization | seek a uniform realization/collar completeness statement |
| **Support** | Exact computation and arithmetic | strong finite support | no universal closure by itself | adversarial non-unit screens and countermodel retention |

## 12. Highest-value task order

For the next research cycle:

1. **#139 literature baseline first.** Finish the exact transfer audit before inventing another strict-zipper invariant.
2. **#138 propagation theorem in parallel.** The aligned branch has a finite combinatorial normal form and may close independently of the geometric branch.
3. **State the non-unit strict-zipper hitting theorem precisely.** It must mention the full representation space and its conclusion must force an actual prefix-Parikh hit.
4. **Use the known pumps/collars as mandatory negative controls.**
5. **Keep G1b-2 active but secondary to #84.** It is a stronger structural theorem, not a hidden dependency of PDS.
6. **Do not expand fixed-size sieves unless they test a specific proposed uniform lemma.**

A successful week is not "more specimens passed." It is one of:

- P1a reduced to a strictly smaller named theorem;
- P1b reduced to a source-checked non-unit recurrence/hitting theorem;
- one of those theorems proved;
- or a proposed bridge falsified by a retained exact countermodel, thereby shrinking the search space without weakening the hypothesis firewall.

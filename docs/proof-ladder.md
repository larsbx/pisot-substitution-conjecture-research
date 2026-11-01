# Proof ladder

## October 22 reconciliation: accepted class D and scoped G1

PR #298 discharged class-D integration at accepted tree
`c325aa5345e1f49b2fb50b37565bd2902104aab7`. The older pending-runtime and
positive-`b` planning paragraphs below are historical, not live gates.
The [class-D G1 corollary](class-d-g1-corollary-2026-10-22.md) makes the
existing assembly explicit: accepted all-seed offset-zero hitting plus
Proposition 4 gives finite BPA on the determinant-two class-D normal form.
On the two full `b=0` branches, exact occurrence-compatible certificates
give `K_minus<=4` and `K_plus<=6`, including their finite prefixes, hence
all-level word-length bounds `2(3a+8)^6` and `2(3a+5)^8` respectively.

The absence of a uniform spectral contraction margin is compatible with
these uniform hitting-depth bounds. Neither fact settles the universal
problem. This is a scoped derived corollary, with independent human review
pending; universal #138/#139/#84, G1 and PSC remain open. Continue the
remaining A/C coverage from the live roadmap, without reopening class D.

`ClassDFiniteBPA` now records this specialization in the generated ledger,
depending on `ClassDBoundaryHitting` and `SwapOverlapFiniteness`. The Open
model reaches it while retaining `G1NotEstablished` and `PDSNotEstablished`.
This instantiates Proposition 4 on the discharged scoped premise; it does
not assume the open universal premise bundled into `G1HalfCoincidenceRoute`.

The scoped class-A/C boundary-hitting certificates are registered alongside it
(2026-10-26): `ClassABoundaryHittingLowGaps` (gaps `d <= 4`),
`ClassABoundaryHittingHighGaps` (gaps `d >= 5`, `n >= 5d`) and
`ClassCBoundaryHittingLowGaps` (gaps `d <= 5`, depending on the Theorem L″ lines
in `DetTwoBoundaryHittingLines`). None of them is a premise of
`UniversalBoundaryHitting`, and no G1 corollary is drawn for classes A or C. The
class-B top-layer label rays are registered as evidence only
(`ClassBTopLayerLabelRays`).

## October 27 class-B executable increment

The [class-B middle certificate](class-b-middle-certificate-2026-10-27.md)
adds unbounded-gap middle coverage at `l>=4`: plus `g>=16, 2<=r<=g-14`,
minus `g>=12, 6<=r<=g-6`. Strict core containment, complete forward closure
and selected-child descent of `abs(k)+b` (`b<=3`) are exact Mojo certificates
with independent rational Python verification. The sole minus `g=12` middle
residue uses an exact ray exception. The remaining finite gaps of #363 add
103 rays, giving 186 in total (plus gaps through 15, minus through 11),
with exact checks below their certified floors.

The old `ClassBTopLayerLabelRays` entry retains its historical evidence status;
no governed claim or universal premise is promoted here. Lean formalizes
integer segment realization, residue partitions and the generic rank
implication, not the table certificates. Low/high residue bands and `l<4`
for unbounded gaps remain open. Actual escaping children disprove reuse of
the middle table on the boundary bands. This is separate from class A.

## Primary ladder: two universal lemmas

The project now treats seedwise overlap productivity (#84) through the
manuscript's **Two-obstruction completion theorem**
(`thm:two-obstruction-completion`). The shortest honest ladder is:

```text
PIP
=> finite exact seed-patch overlap graph                         [PROVED]
=> closed recurrent obstruction normal form                     [PROVED]
=> A1′: residual fixed-letter hub edge cannot remain bad         [OPEN: #138]
 + BH: every cyclic strict zipper hits offset zero               [OPEN: #139]
=> every seed-reachable overlap is productive                    [PROVED assembly]
=> dense eventual coincidence                                   [PROVED]
=> pure discrete spectrum                                       [IMPORTED theorem]
```

The two open lines are the primary proof obligations. The aligned endpoint
normal form reduces #138 to one-sided A1′ (reversal is not an additional
premise of this completion theorem), while #139 is the
occurrence-compatible coverage theorem in the full non-unit representation.
If both close without an independent tile-length-independence, legality, FI
or unimodularity hypothesis, #84 closes and the PDS conclusion follows
immediately. G1b-2, SCC Producer/K2 and realization remain valuable parallel
theorems, but they are not prerequisites of this direct route.

**October 20 interface advance:** the
[exact length-window lemma](two-obstruction-moment-interface-2026-10-20.md)
shows that three scalar length observations determine a ternary PIP Parikh
defect. A same-position block need not stay aligned under inflation; the
recorded PIP control has drift `(0,-1,-3)`. An occurrence-address reader
independently checks supplied zero-defect paths and distinguishes boundary
hitting from equal-letter coincidence. These are proof interfaces and finite
controls, not existence or carrier-closure theorems; both universal lines
above remain open. Local execution provenance and the pinned replay boundary
are recorded in the linked note.

The separate class-D work is accepted at the exact scope recorded by PR #298
and the [assembly audit](class-d-assembly-audit-2026-10-21.md). Historical
failed and queued runs remain preserved in their evidence packets; the
later complete acceptance record supersedes their pending integration status.
No class-D result supplies either universal premise here.


The current shortest route to the Pisot Substitution Conjecture in the standing regime has **one open mathematical premise**: seedwise overlap productivity. The finite-BPA/G1 and closed-carrier programmes remain important stronger structural routes, but they are no longer prerequisites of the shortest PDS sufficiency theorem.

For detailed claim status use `docs/claim-status-and-source-map-2026-09-13.md`; for the live completion priorities use `docs/research-roadmap-2026-09-21.md`; for the latest merged weekly snapshot use `docs/completion-ledger-2026-10-26.md`; theorem statements and imported hypotheses are in `manuscripts/PSC_balanced_pair_state_2026-09-13.tex`.

## Scoped closure below the universal rung (through 2026-10-16)

These results establish PDS only on their stated domains; none fills the open
universal rung above.

- **Finite-domain theorem:** Theorem Ω and the completed box certificates give
  PDS on the union of 145,806 ternary PIP substitutions with images of length
  at most 4 or total image length at most 8. The route uses explicit imported
  overlap-coincidence and Meyer-property theorems and no longer depends on
  Proposition V(2) or Theorem B.
- **Computer-assisted family theorems, human review pending; project-accepted for progression:** Theorems L, L′
  and L″ cover 47 one-parameter determinant-two lines; Theorem W covers the
  declared class-D wedges, in particular all PIP members with `r >= q - 1`.
- **Imported family scope:** Sirvent–Solomyak transfers tiling-flow PDS to the
  symbolic action for PIP substitutions. With Barge's class theorem and the
  exact repository detector this yields symbolic PDS on the declared
  power/rotation/mirror class (1,248 standing-corpus witnesses), while the
  imported Brun-composite corollary covers its own structured family.
- **Provenance limit:** no accepted source on `main` proves boundary hitting,
  overlap productivity, formal productivity, G1 or PDS uniformly for every
  PIP substitution.

## Historical scoped rung: residual positive-b class D (2026-10-19)

**Superseded as a task by PR #298.** Retained below as the October 19–20
development record; use the October 22 reconciliation above for current status.

The exact parameter cover reduces every PIP class-D member below `r=q-1` to
two affine quadrants `a,b>=0`. Merged PR #277 now certifies both infinite
`b=0` boundary lines with exact occurrence-aware machinery. The remaining
class-D target is therefore exactly

```text
s = -1, a >= 0, b >= 1
s = +1, a >= 0, b >= 1.
```

The sealed `b=0` target spine is not a two-parameter proof: the recorded
rank-one matrix update changes a selected child by `(sum w)e_y` unless the
occurrence choice changes with `b`.

1. Validate and integrate the separate occurrence-labelled positive-`b`
   contributions, keeping their local native receipts and CI gates distinct.
2. Combine it with Corollary W1 and the merged `b=0` lines to cover all
   determinant-two class D.
3. Apply the depth note §7 for G1 on that class; with the required #138 input,
   assemble PDS on the corresponding scope.
4. Extend coverage to the remaining classes and then the standing universal
   target. Class-level closure alone does not establish general #139.

The [October 20 chamber validation](class-d-chamber-validation-2026-10-20.md)
records a complete **native local aggregate receipt** under the lock-matched
Mojo 1.1.0.dev2026090805 compiler/runtime: six wedge cores, all 73 returned
strip obligations (69 distinct lines), six explicit interfaces and 952
finite-prefix PIP checks. Every obligation finishes before the driver emits
`CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED`; the process returns exit0.
The earlier component receipts and interrupted duplicate aggregate are retained.
No additional chamber or carrier extension is needed after the exact reader
repairs and ordered interval sweep. The [evidence packet](../evidence/class-d-chamber-validation-2026-10-20/)
records source/runtime identities, raw logs, mapping reconciliation and replay.

The two inherited threshold pins are reconciled to PR #288's clipping change;
the complete pinned symbolic-line regression now passes. The reused
hash-verified manuscript repair and existing conditional completion record
also pass their validation gates, including all 16 TLA+ models. Both universal
premises of that completion criterion remain open.

Full Pixi provisioning remains blocked and dedicated CI remains queued.
No governed plus-family status is promoted. Separately, PR #290 at 3b16b54
now records a uniform seed-carrier proof, both formerly omitted a=0,1 strips,
and a native complete-minus-residual receipt; its assembly with the existing
wedge theorem covers the PIP minus branch. This plus session inspected that
receipt and its source/evidence hashes, without executing or importing the
minus proof. Both scoped contributions retain their full Pixi/CI integration
gates. Universal #139/#84 and general PSC remain separate and open.

Mechanically sufficient scoped results are project-accepted for progression;
independent human review remains final validation and is not being claimed.

## October 16 evidence boundary

The merged source audits narrow what can legitimately fill the next rung.
Nakaishi's printed general-proof route cannot be imported: its first-entry
identity omits an intersection term, its Theorem 3 radius does not match the
proof scale, and an exact source-address cancellation does not automatically
transport the prescribed forward integer offset. Likewise, projected
imbalance zero is not coincidence and projected paths can splice incompatible
occurrences. A positive path must be replayed with one compatible sequence of
ordered child occurrences.

The exact ternary non-unit calibration reinforces the correct quantifier: one
reachable vertex can have an indefinitely repeatable nonzero loop and still
have alternative legal children reaching zero and coincidence immediately.
The open object is therefore an entire child-closed nonproductive realized
component, not an individual recurrent path. The calibration family itself is
already PDS by the imported mirror-Barge route and supplies no new universal
closure.

# Stable base — incidence rank, UD, and bounded discrepancy

Established on `main`:

1. `det M_sigma != 0` gives full incidence rank / letter injectivity.
2. The defect theorem gives unique decodability of the image code `{sigma(a)}`.
3. UD propagates to powers because `det M_{sigma^r}=(det M_sigma)^r != 0`.
4. G1b-1 bounded discrepancy is repository-proved by the independent reconstruction merged in PR #69.

UD is therefore a theorem, not an independent standing hypothesis. Bounded discrepancy bounds the prefix-difference walk, not balanced-state length.

The old predecessor-contraction claim and the inference `UD => bounded total padding => finite BPA` are withdrawn permanently.

# Primary completion ladder — finite seed-patch overlaps, no G1

The current shortest honest chain is

```text
primitive irreducible Pisot
=> bounded discrepancy                                  [PROVED]
=> finite seed-patch overlap graph                      [PROVED]
=> one swap seed has only productive reachable overlaps [OPEN]
=> coincidence density one / dense good set             [PROVED equivalence]
=> pure discrete spectrum                               [IMPORTED theorem]
```

The two-letter periodic swap patch uses distinct tile types; `ab` need not be a legal factor of the substitution language.

## Finite seed-patch overlap graph

**Repository-proved.** Manuscript Theorem 4.22 / PR #72 shows that every exact overlap type reachable from a swap seed lies in an explicitly bounded integer-coordinate set derived from G1b-1. This graph is finite without assuming finite BPA, Meyer structure, or unimodularity.

## Overlap productivity — the current critical gate

**OPEN (Open Problem 5.35).** For every PIP substitution it is enough to prove existence of distinct letters `a != b` such that every overlap reachable from the seed overlaps of `(ab,ba)` is productive. (The manuscript states Open Problem 5.35 for every vertex of the overlap graph; this one-seed form is the weaker statement Theorem 5.38 needs.)

Do not transfer conclusions from the stronger all-vertex premise to this one-seed gate. Proposition 5.39(iii)'s two-sided strong-coincidence consequence, the every-vertex Corollary 5.41 hitting formulation, and the cited unimodular equivalence with PDS apply to all-vertex productivity. No one-seed-to-all-vertices implication is claimed. *Correction 2026-10-08:* through PDS one does hold (Theorem 5.38 forward, Corollary FP″ back, at the October 4 chain's review status); see Theorem SC of `docs/p1-seed-strength-2026-10-08.md`. The seed still matters for the proof, not for the truth.

The seed-relative growth accounting needed for this attack is now exact:
`docs/p1-overlap-seed-growth-bridge-2026-09-17.md` proves that the
multiple-edge update counts actual residual occurrences per inherited seed
period. The unresolved step is not the occurrence dictionary but the rigidity
claim excluding a full-growth, child-closed nonproductive realized component.

The ordered strict-zipper layer now has an exact finite affine-pump lemma:
every actual child occurrence satisfies `w'=Mw+q-p`, and a replayed cycle
satisfies the iterated cycle identity. This does not close the gate. A
productive non-unimodular graph already supplies a six-edge zero-shift-free
cycle, so the missing rung must use closed nonproductivity, occurrence context,
recognizability, and any required non-Archimedean internal factors.

Proving productivity for every seed or every vertex in the union graph is stronger than necessary for manuscript Theorem 5.38.

The current obstruction normal form combines PRs #76, #82 and #88. If the gate fails, we may pass to a finite child-closed irreducible nonproductive SCC `S` with

```text
PF(N_S) = beta,
N_S V_S = V_S M^T,
rank_Q(V_S) = |A|,
spec(M) subset spec(N_S).
```

Thus a bad set is algebraically **full rank**, not rank-deficient.

PR #88 further gives an exact dichotomy:

```text
bad S
=> contains an offset-zero state (i,j,0)
   and therefore exposes a non-eventually-coincident pair {i,j}
OR
=> contains no zero-shift state
   and every child factorization is a strict no-tie prefix-grid zipper.
```

The second branch preserves information erased by the child-count matrix: the ordered sequence of top/bottom subdivision boundary events. The next contradiction should use that order together with full rank and exact prefix-Parikh geometry.

The one-step context calibration shows that equal affine overlap states can
carry unequal paired prefix-suffix addresses. The radius-`m` collar in the
iterated periodic swap patch is now an exact finite object (Lemma 1 of
`docs/p1-overlap-collar-2026-09-16.md`): on the determinant-two graph the
separation radius is `1`, and the golden zero-shift-free pump lifts to a
collared cycle at every tested radius. Bounded-context equality therefore
cannot by itself exclude zero-shift-free recurrence; the missing rung must use
child closure and nonproductivity with the exact cycle identity, not loop
deletion from affine-state or bounded-context recurrence alone.

Generic spectral growth is not enough. A residual graph containing a genuine noncoincident real overlap may itself carry the full expansion spectral radius, so `PF(N_S)=beta` is the hard residual case rather than a contradiction.

## Coincidence density and PDS bridge

**Repository-proved:** Lemma 5.36 identifies seedwise overlap productivity with coincidence density one and density of the eventual-coincidence good set. The proof does not assume that the finite-stage good sets are nested; the corrected argument uses the finite subdivision-point difference between stages.

**Imported theorem:** Barge–Štimac–Williams supplies the dense-eventual-coincidence-to-PDS implication in the precise one-dimensional Pisot-family setting checked in manuscript Imported Theorem 5.37. Hence Theorem 5.38 has no G1 hypothesis.

## Endpoint-aligned boundary case

PR #82 proves:

- swapping tiling sides preserves productivity;
- offset-zero and right-aligned seed overlaps are productive exactly in the prefix/suffix strong-coincidence cases;
- an overlap reaches an offset-zero descendant at level `m` exactly when `M^m w` is a difference of proper-prefix Parikh vectors, equivalently when inflated subtiles have a common left endpoint;
- under strong coincidence, productivity reduces to this boundary-hitting statement.

PR #88 turns this into the aligned-versus-zipper case split above without assuming strong coincidence globally (manuscript Propositions 5.43–5.44). Manuscript Lemma 5.45 records the ordered cycle equation `(I - M^r) w_0 = sum_k M^{r-1-k} d_k`: every offset of a closed irreducible obstruction is determined by the ordered address of a cycle through it and has a purely periodic expansion in the increment set `F`, with no vanishing tail in the strict-zipper branch.

PR #87 adds the contracting lower bound (Proposition 5.42): a hit at level `m` forces `|varsigma(t)| <= C_varsigma sum_{s<=m} |varsigma(beta)|^{-s}` for every contracting embedding, decided exactly in `Q(beta)`; on the corpus this bound is at most 8 while the hitting depth reaches 17, leaving a gap of up to 14 inflations that this magnitude bound does not explain (the gap includes the slack of the bound; no further attribution is drawn).

# Stronger route A — Level 2 / finite BPA

The stronger Level-2 ladder remains

```text
primitive + Pisot spectrum
=> bounded discrepancy (G1b-1)       [PROVED]
=> renewal finiteness (G1b-2)         [OPEN]
=> finite BPA (G1).
```

## Overlap-depth route to G1

**Conditional theorem** (manuscript Proposition 5.46; `docs/bpa-termination-by-overlap-depth-2026-10-02.md`, Proposition 1; mechanism of Sirvent–Solomyak 2002, Theorem 5.6, per `docs/bpa-overlap-depth-literature-gate-2026-10-02.md`). G1 has a second sufficient premise on the overlap side:

```text
primitive irreducible Pisot
=> bounded discrepancy                                   [PROVED]
=> finite seed-patch overlap graph                       [PROVED]
=> every swap seed has only productive reachable overlaps [OPEN]
=> every reachable state has length <= 2 beta^D ell_max   [PROVED implication]
=> finite BPA (G1).
```

`D` is the largest first-coincidence depth of the overlap graph. Balanced cuts are simultaneous tile boundaries because the coordinates of `ell` are `Q`-independent, and every overlap at level `n - D` has a coincident descendant inside its `beta^D`-scaled region, so consecutive cuts are at most `2 beta^D ell_max` apart. No realization hypothesis is needed: every reachable state is a gap of a swap pair `(sigma^n(ab), sigma^n(ba))`. The premise is the all-seed form, stronger than the one-seed gate of Theorem 5.38, so this arrow does not shorten the PDS route; it makes G1 a consequence of the overlap programme rather than an independent obligation.


## Half-coincidence route to G1

**Conditional theorem** (manuscript Proposition 5.47; `docs/bpa-termination-by-overlap-depth-2026-10-02.md`, Proposition 4 and Corollary 5; half-coincidence form of Sirvent–Solomyak 2002, Theorem 5.6). The overlap-depth route needs less than productivity:

```text
finite seed-patch overlap graph                           [PROVED]
=> no reachable strict zipper from any swap seed           [OPEN, issue #139 form]
=> every reachable overlap has an offset-zero descendant   [equivalent, Corollary 5]
=> every reachable state has length <= 2 beta^K' ell_max   [PROVED implication]
=> finite BPA (G1).
```

A coincidence has offset zero, so `K' <= D` and this premise is implied by all-seed overlap productivity. The vertices with no offset-zero descendant form a closed nonproductive set with no offset-zero vertex, case (b) of manuscript Proposition 5.44(iii), and every reachable such set lies inside them. So finiteness needs only the strict-zipper branch of the obstruction problem; the strong-coincidence branch (P1a, issue #138) is needed for productivity and pure discrete spectrum, not for G1.

## PDS implies G1, so G1 is necessary

**Repository-proved** (manuscript Proposition `prop:PDS-implies-G1`; ledger `PDSImpliesRepoG1`, the Theorem S route of `docs/p1b-vertex-coincidence-box-2026-10-02.md` §5.1; internally/adversarially audited 2026-10-04, **project-accepted for progression; independent human validation outstanding**, `docs/side-notes-ledger.md` §7).

```text
pure discrete spectrum
=> no reachable strict zipper from any swap seed    [via imported coincidence rank]
=> finite BPA (G1)                                  [half-coincidence route above]
```

A reachable strict zipper yields, by Theorem B and Corollary B′ of `docs/p1b-strict-zipper-periodic-pair-2026-10-02.md`, a pair of `Phi^r`-fixed tilings with a common interior centre, an integral centre offset and no common vertex; Proposition F and Theorem R put them in one fibre of the maximal equicontinuous factor; sharing no tile they force coincidence rank at least two, which excludes PDS by Barge's coincidence-rank theorems. Those imports assume neither unimodularity nor irreducibility (`docs/coincidence-rank-imports-literature-gate-2026-10-04.md`).

This closes the direction the ladder lacked. Until now G1 was a hypothesis whose relation to the conjecture was unknown, so the boxed conditional was one sufficient route among possible others. G1 is now a **necessary** condition for PDS: any proof of PSC makes G1 true, and a counterexample to G1 would refute PSC. The realization step is not a formal-recurrence shortcut — it builds the two tilings from interior occurrences, whose patches are allowed for `sigma`, and takes integrality of the offset from the cycle equation rather than assuming it.

Together with the seedwise bridge below, the finiteness side of the programme is no longer an independent obligation: it is a consequence of the conjecture, and it is implied by either half of the obstruction problem.

## PDS implies seedwise termination (former Open Problem 4.24)

**Repository-proved** (manuscript Theorem `thm:seedwise`; ledger `PDSImpliesSeedwiseTermination` with the imported `StrongCoincidenceFromPDS`; same review status as above). PDS implies termination with coincidence from **every** seed `(ab, ba)`, legal factor or not. The repository's all-seed graph is therefore covered, not one convenient seed, and the seed-family question the ladder used to carry as open is answered. Dated notes that still call Open Problem 4.24 open are history, not status.
## G1b-2 — renewal finiteness

**OPEN; equivalent to G1 after G1b-1. Not required by Theorem 5.38.**

Prove that only finitely many reachable irreducible balanced pairs occur inside the established discrepancy bound. A bounded difference alphabet does not suffice because labelled first-return words can revisit the same nonzero difference vertices indefinitely.

The structural target is

```text
realizable labelled first-return words
=> level-scaled contracting/Rauzy address
=> finite-return / uniform-discreteness theorem
=> G1b-2.
```

The proof must remain non-unimodular-safe:

- no `|det M|=1` assumption;
- no purely Euclidean internal-space assumption where a profinite/non-Archimedean factor is required;
- no claim that `pi_s(Z^A)` is a lattice;
- preserve label/order data lost by cumulative difference walks.

### Retired Level-2 shortcuts

Do not use:

- UD implies bounded total padding;
- bounded discrepancy implies finite BPA;
- naive zero-sum-hyperplane contraction;
- every long state has a uniformly short core;
- two-letter renewal is trivial;
- unlabelled cumulative difference walk determines a balanced state.

# Stronger route B — SCC Producer under G1

Assume G1. Nonproductivity then reduces to a finite closed/sink recurrent noncoincident carrier.

The current spectral split is

```text
closed recurrent carrier
=> K2 == 0 or K2 != 0
=> [OPEN] concentration or [OPEN] wedge productivity
=> productivity
=> SCC Producer.
```

## Concentration / aux-B

**OPEN.** Equivalent in the current cubic wedge dichotomy to excluding strict components with `K2 == 0`.

The archived degree-three theorem applies only to its explicit seeds. The live degree-two carrier-span statement is independently repository-proved; no missing v16 source is required.

## Wedge productivity

**OPEN.** Equivalent to excluding strict components with `K2 != 0`. Full rational wedge span is a classification constraint, not a productivity theorem.

The exact 4,554-member corpus has fail-closed finite-domain certificates excluding both first-defect branches in their stated domains. Those certificates are not uniform theorems.

## Relation to the overlap route

A proof of general overlap productivity is stronger than needed to bypass G1. In its all-seed form it also implies G1 (the overlap-depth route above) and supplies productivity of all reachable BPA states. Therefore the overlap theorem can feed SCC Producer, but the finite-BPA carrier route is not required to prove Theorem 5.38.

# Supporting structural machinery

The following remain theoremically useful where their individual notes mark them theorem-grade:

- bad-overlap closed-SCC normal form and aligned/strict-zipper dichotomy (PR #88);
- sink-SCC reduction under G1;
- endpoint synchronization quotient and A/B eliminator;
- Barge–Diamond type-G eliminator and hub-star normal form;
- Parikh intertwiner `P_C N_C = (M_sigma) P_C`;
- orientation monodromy and signed child-count matrices;
- signed first-defect intertwiners;
- degree-3, degree-4 and generalized-Witt spectral sieves;
- ordered degree-2 mid-area factorization and integral filters;
- bounded-gap zero-return calculus;
- finite Pisot ancestry states and legal ancestry towers;
- derived recognizability and relative hierarchy-offset states.

The C4 chain

```text
C4 => C3-local => C2 => C1
```

remains a valid one-way sufficiency route. It is not the headline completion ladder.

# Realization / MEF route

The realization programme remains an open bridge / certificate route. Its audited interface has obligations G0–G6. Do not identify:

```text
formal producer-free recurrence
= global realization
= survival to a finite collar bound.
```

Finite collar death is evidence until an independent completeness theorem is available.

# Exact finite calibration

Across the exact 4,554 short-image ternary PIP corpus:

- G1b-1 cross-check: maximum reachable discrepancy `14`, with reachable state length at least `48,020`;
- every BPA build used by the finite certificates terminates below its fail-closed cap;
- seed-patch overlap graphs: `4,554 / 0 / 0` built/capped/failed;
- total overlap vertices: `1,118,850`;
- largest overlap graph: `2,640`;
- specimens containing a nonproductive overlap: `0`;
- maximum first-coincidence depth: `18`;
- maximum first left-aligned depth: `17`;
- maximum prefix and suffix strong-coincidence depths: `15`;
- all specimens satisfy the tested two-sided strong-coincidence condition;
- the degree-two and degree-three finite carrier certificates have zero survivors in their stated domains.

These are exact finite-domain results/evidence according to their individual completeness contracts. They do not prove the general conjecture.

# Hypothesis firewall

Every proposed completion proof must preserve:

1. **Swap-patch legality is not assumed.** The two-letter periodic seed in Theorem 5.38 need not be a legal substitution-language factor.
2. **Tile-length independence is derived.** Do not add rational/integer independence as a separate PSC hypothesis when irreducibility supplies it.
3. **UD is derived.** Do not make unique decodability a standing assumption.
4. **FI/boundary injectivity is extra.** Do not silently restrict to permutation/injective boundary maps.
5. **No unimodularity leak.** Unit-only converse theorems or Euclidean-only Rauzy constructions remain restricted unless separately generalized.
6. **No false stable lattice.** `pi_s(Z^A)` is generally not a discrete lattice.
7. **No realization shortcut.** Formal recurrence does not imply global realization.
8. **No computational self-certification.** Finite corpus/collar bounds require an independent completeness theorem before universal use.

# Completion order

1. **P0 — synchronization.** Keep manuscript, claim/source map, conjecture ledger, proof ladder, README, roadmap, issue statements and TLA dependency comments aligned.
2. **P1a — aligned branch (#138).** Prove the ternary two-sided strong-coincidence statement needed to eliminate every aligned bad SCC, or reduce it to a strictly smaller named theorem. Keep the Barge–Diamond two-letter/general-existence scopes distinct.
3. **P1b — strict-zipper branch (#139).** Prove an occurrence-compatible matched-target replay/lifting theorem and then a uniform good-branch or boundary-hitting theorem for every realized child-closed candidate. In class D, merged PR #277 already covers both `b=0` boundary lines; the exact residual is `s=±1, a>=0, b>=1`. Do not infer this from a projected path, one recurrent branch, or literal transport of the boundary spine.
4. **P1 — overlap productivity (#84).** Assemble P1a and P1b, or replace them with one stronger theorem excluding every bad closed irreducible SCC. This remains the only open premise on the current shortest PDS route.
5. **P2 — G1b-2.** Continue as a stronger theorem on BPA finiteness, with the non-unimodular and label/order firewalls intact. G1 now has three sufficient premises — G1b-2, all-seed overlap productivity (overlap-depth route), or all-seed strict-zipper exclusion alone (half-coincidence route) — and is in any case a necessary consequence of PDS, so G1b-2 is the least load-bearing of the three.
6. **P3 — concentration and wedge productivity.** Continue as the alternative finite-BPA/SCC route only when new invariants add information beyond child counts and full wedge span.
7. **P4 — realization bridge.** Discharge G0–G6 only if pursuing the coincidence-rank/collar certification route.

No additional fixed-size SCC sieve, collar depth, coincidence-depth census, or determinant-restricted argument should displace P1a/P1b unless it supplies a credible uniform theorem feeding #84.

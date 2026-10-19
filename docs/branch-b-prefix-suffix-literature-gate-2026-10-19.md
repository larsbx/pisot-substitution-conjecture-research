# Literature gate: prefix/suffix endpoints, balanced-pair SCCs, and Branch-B injection — 2026-10-19

**Status:** literature synthesis / hypothesis firewall / side-route research. **No theorem or claim-status promotion.** This note records findings from the project's September 2026 deep-literature investigation, reconciled with the repository's October 19, 2026 architecture. It is not a fresh independently exhaustive bibliographic search through October 19. No computations reported in earlier conversational sweeps were rerun for this note.

**Routing:** the live proof obligations remain #138 (aligned A1′), #139 (strict-zipper BH), and their assembly under #84. The finite balanced-pair/SCC Producer route is a *stronger parallel route*, not an assumed prerequisite. See [the CK-v3 status note](ck-v3-side-route-status-2026-10-12.md), [the live roadmap](research-roadmap-2026-09-21.md), and [the current proof architecture](current-proof-architecture-2026-09-14.md).

## 1. Exact research question

For a nonerasing substitution \(\sigma:\mathcal A\to\mathcal A^+\) define the endpoint maps
\[
  p(a)=\sigma_+(a)=\operatorname{first}(\sigma(a)),\qquad
  q(a)=\sigma_-(a)=\operatorname{last}(\sigma(a)).
\]
Here the standing *general* problem is primitive irreducible Pisot (PIP), **not** secretly unimodular, legal-swap-only, boundary-injective, or finite-BPA.

A finite recurrent noncoincident balanced-pair SCC \(C\) can carry an orientation sign on each occurrence of a noncoincident child, using the project's **chosen and explicitly order-dependent** sign convention. Its no-cancellation regime \(Q_C=0\) yields a well-defined signing of its directed support (with multiplicities retained for signed transfers). For an irreducible support digraph with period \(h\), period-wrap cochain \(\lambda_C\), and sign bit \(b_C\), the correctly stated finite Perron-compatibility test is
\[
  \exists r\in\mathbb F_2,\ x:V(C)\to\mathbb F_2:
  b_C(e)=x(s(e))+x(t(e))+r\lambda_C(e).
\]
In project terminology a closed recurrent no-cancellation SCC satisfying this test is **Branch B**. This is graph theory on a *defined* signing, not a published Pisot theorem, and the classification depends on the chosen orientation convention.

**Open Boundary-Injection Exclusion conjecture (Branch B only):**
\[
  p,q\text{ injective}\quad\Longrightarrow\quad
  \text{there is no closed recurrent Branch-B SCC}.
  \tag{BI}
\]
Because the alphabet is finite, injective endpoint maps are permutations. BI does **not** claim that a substitution with two injective endpoints has no recurrent noncoincident SCC or no interior coincidences. The statement is a proposed obstruction to a *specific signed subclass*.

The more general finite-BPA side target is **CK-v3 / SCC Producer**: each *closed* recurrent noncoincident SCC contains a state whose substitution has a coincidence sibling. This is open. Earlier exclusions of all recurrent noncoincident cycles and per-state immediate productivity are false and must not be revived; see [CK-v3 status](ck-v3-side-route-status-2026-10-12.md).

## 2. Closest literature and exact transfer boundaries

| Source | Hypotheses and actual result | Useful to this program | Does **not** establish |
| --- | --- | --- | --- |
| Barge–Diamond (2002), *Coincidence for substitutions of Pisot type* | Strong coincidence in the two-letter setting, with partial higher-alphabet consequences. Matching abelianized prefix plus matching next letter is the key local form. | The correspondence between a Parikh zero-return followed by a matching letter and a coincidence witness. | No-recurrent-noncoincident-cycle, or the relative CK-v3 assertion for *every* closed SCC. |
| Sirvent–Solomyak (2002); Hollander–Solomyak (2003) | Balanced-pair/overlap techniques and the two-symbol Pisot pure-discrete theorem. | Foundational BPA seed/irreducible-factor machinery; the two-letter benchmark. | A higher-alphabet SCC Producer theorem. |
| Akiyama–Barge–Berthé–Lee–Siegel (2015), *On the Pisot substitution conjecture*, Thm. 5.3 | BPA termination with coincidence is tied to PDS in the irreducible Pisot regime; the exact quantifiers on chosen \((ij,ji)\) seeds must be preserved. | Literature criterion for this project's seed-vs-all-seeds bridge; see [BPA literature bridge](bpa-literature-bridge.md). | The missing general termination step from mere finite recurrence. |
| Barge–Kwapisz (2006), *Geometric theory of unimodular Pisot substitutions* | **Unimodular** strand/geometric-realization framework and geometric coincidence criteria. | A geometric dictionary for a putative no-coincidence strand subsystem. | Removal of unimodularity; automatic coincidence in a restricted recurrent SCC. Do not cite §§14–17 or Thm. 16.3 as an unconditional cycle-killer. |
| Barge–Štimac–Williams (2013), *Pure discrete spectrum in substitution tiling spaces* | Uses specified coincidence/BPA hypotheses to obtain pure discreteness through its proximality/regional-proximality bridge. | The appropriately scoped downstream bridge; existing import audits are authoritative. | Proof that arbitrary BPA instances terminate; no permission to repair any older BK proof gap by citation alone. |
| Canterini–Siegel (2001), *Automate des préfixes-suffixes associé à une substitution primitive* | Full factorization paths \(\sigma(a)=u\,b\,v\), an adic coding and geometric descriptions. | Strong candidate *richer* state space for endpoint/ancestor contexts. | The prefix-suffix automaton is **not** just the pair of endpoint functions \(p,q\); coding does not yield BI. |
| Mossé (1992/1996); Solomyak (1998) | Recognizability/unique composition under their aperiodicity and tiling hypotheses. | Unique hierarchical ancestry when the relevant local/collared hypotheses are satisfied. | Agreement of two sigma-cut sets, first/last-letter synchronization, or a shrinking SCC descent. |
| Akiyama–Lee (2011), Thm. 4.1 | Under the stated tiling/Meyer/representability assumptions, a complete overlap-coincidence graph criterion including residual growth. | A graph-theoretic analogue of a Perron-critical noncoincident obstruction. | A theorem forcing that obstruction to disappear, or forcing a particular periodic address to hit an aligned prefix-difference set. |
| Barge (2016), *Pure discrete spectrum for a class of one-dimensional substitution tiling systems*, Thm. 3.13 | Primitive nonperiodic Pisot, **injective on initial letters and constant on final letters** implies PDS (with its corresponding reversed-word mirror). No unit-determinant shortcut is needed for this imported result. | **Closest proven endpoint-sensitive theorem**, using stable-equivalence/quotient and eventual-coincidence ideas descending from BD. | BI: both endpoints injective is very different from one endpoint constant. Nor does it prove Branch-B SCC-Diagonal. |
| Barge (2018), *The Pisot conjecture for beta-substitutions* | A special \(\beta\)-substitution class. | Class-specific quotient and geometric strategy, including non-unit phenomena. | General PIP or a generic Branch-B endpoint criterion. |
| Barge–Kellendonk (2013), *Proximality and pure point spectrum for tiling dynamical systems* | Proximality/coincidence-rank/fiber criteria under explicit hypotheses. | Possible fiber-theoretic replacement for a direct strand pigeonhole. | A boundary-sign identity or a proof that every recurrent SCC produces coincidence. |
| Gohlke–Mitchell–Rust–Samuel (2026), *Rauzy fractals of random substitutions* | Contemporary geometric research continuing to treat the deterministic general PSC as an open problem. | Current-status anchor and same-incidence/different-order motivation. | Acceptance of a general PSC proof. |

**Additional caution.** Nakaishi's 2024 arXiv manuscript, *Pisot Substitution Conjecture and Rauzy Fractals*, claims to resolve a version of the conjecture. This is a **preprint claim**; the subsequent 2026 peer-reviewed literature still presents the general PSC as open. Do not silently promote the preprint to an established closure; its exact assumptions and proof should be audited separately if used.

**Existing repository work already handles adjacent prior art.** In particular [the strict-zipper literature gate](p1b-strict-zipper-literature-gate-2026-09-21.md), [the Barge-class power/rotation stop](p1b-class-d-barge-power-rotation-stop-2026-10-16.md), and [the 2026-10-19 proximality note for A1′](p1a-a1-proximality-2026-10-19.md) have sharper, currently load-bearing scope rules for the *primary* route. This file supplements rather than replaces them.

## 3. What endpoint permutations prove, and what they do not

If both \(p,q\) are injective, they are permutations of \(\mathcal A\). Consequently \(P=p\times p\) and \(Q=q\times q\) permute the off-diagonal set
\[
  \mathcal A^2\setminus\Delta,\qquad \Delta=\{(a,a):a\in\mathcal A\}.
\]
For any \(a\ne b\) and any \(n\ge0\), \(p^n(a)\ne p^n(b)\), and likewise \(q^n(a)\ne q^n(b)\). This is an exact elementary lemma requiring **neither** Pisot nor unimodularity.

However, a child occurrence in an inflated balanced pair can begin/end at an **internal** Parikh zero-return boundary. Its endpoint pair is not generally the image under \(P\) or \(Q\) of the *external* endpoints of its parent. Internal letters, their order, and the full zero-return cutting pattern matter. Therefore:

- No collision of **inherited outer endpoints** does not mean no **newborn internal** coincidence.
- Global recognizability does not make the two tracks' sigma-cut positions coincide.
- An SCC with a Perron-compatible orientation signing need not have each state immediately productive.
- No theorem can infer a sign cocycle on arbitrary child edges using only \(p,q\) without a proved **edge/context factorization**.

The project's [Boundary Synchronization Lemma](boundary-synchronization.md) is a safe one-way implication: an *actual* zero-return boundary right pair synchronizing under \(p\), or left pair synchronizing under \(q\), yields a coincidence sibling after some inflation. It is not the converse and does not force such a boundary to exist.

## 4. Two genuinely separate conjectural bridges

**Bridge I — Boundary-Injection Exclusion (BI).** In the bi-injective regime \(p,q\in\mathrm{Sym}(\mathcal A)\), prove that no **closed recurrent** no-cancellation SCC can have a Perron-compatible orientation signing. This is empirically suggested but remains unproved and sign-convention-sensitive.

**Bridge II — Collision Realization (CR).** Suppose a Branch-B SCC exists and \(p\) or \(q\) has a collision. Show that *that same SCC* realizes a colliding pair at a matching endpoint:
\[
 \exists (u,v)\in C:\ 
 p(u_1)=p(v_1)
 \quad\text{or}\quad q(u_{|u|})=q(v_{|v|}).
 \tag{CR}
\]
Even proving BI does **not** prove CR. Non-injectivity of \(\sigma\)'s endpoint map may occur on letters that never form relevant endpoints in \(C\).

Under CR, the relevant state produces a single-tile boundary coincidence, hence CK-v3 for that *closed strongly connected* component (every state reaches the producer). The chain is only
\[
 \text{BI + CR}\Longrightarrow\text{SCC-Diagonal}\Longrightarrow\text{CK-v3 for Branch B},
\]
not \(\text{BI}\Longrightarrow\text{CK-v3}\) alone.

**Empirical context, not independently replayed evidence:** prior conversation-derived audits reported no Branch-B counterexample to SCC-Diagonal in a small/random/Perturbed ternary set, and no Branch-B SCC in a bi-injective-boundary sample (1,885 ternary PIP specimens and 70 four-letter specimens). Those figures belong to the original experimental logs, **not** new certified receipts in this PR. Selection bias, BPA state caps, seed distributions, and the dependence on lexicographic signing must travel with any quotation. The per-state Branch-B immediate-productivity proposal was falsified (trial 8381), and cycle exclusion was falsified by a recurrent noncoincident reversed-Tribonacci component.

**Nomenclature control:** the project's recurrent-cycle specimen \(1\mapsto21,\ 2\mapsto31,\ 3\mapsto1\) is called **reversed Tribonacci** here. Sirvent's published paper titled *flipped Tribonacci* studies \(1\mapsto12,\ 2\mapsto31,\ 3\mapsto1\). Cite the explicit substitution whenever using either name.

## 5. Candidate literature-grounded research routes (ordered)

### A. Test endpoint/context factorization *before* endpoint holonomy

Define the signed multi-edge occurrence graph with **actual child occurrence identities**, not collapsed types alone. Ask whether a finite map to an endpoint/context graph carries the project sign \(b_C\), modulo vertex gauge and period wrap:
\[
 [b_C]=\pi^*[\eta]+r[\lambda_C].
 \tag{EF?}
\]
First try the four **external** endpoint letters; if falsified, use the first Parikh-return neighborhood and then full Canterini–Siegel-style ancestor context. Counterexamples must preserve ordered occurrences and the exact sign convention. A fitted cocycle with one bespoke feature per edge is not a proof of factorization.

Suggested controls: (a) productive bi-injective PIP Branch A/C specimens; (b) known Branch-B specimens with noninjective ends; (c) primitive non-Pisot bi-injective substitutions; (d) reversed-Tribonacci persistence. A failed factorization is a stop/go for this proposed approach, not a disproof of BI.

### B. Try Barge's endpoint-sensitive *quotient* method

Barge's 2016 theorem is more substantive than the bare statement “prefix/suffix matter”: its proof turns special endpoint structure and stable-equivalence into a quotient/contradiction using a BD-style coincidence argument. A potentially useful **new** question is whether a closed Branch-B SCC defines a quotient/fiber relation that preserves both endpoint permutations, and whether its recurrence can contradict a suitable stable-relation invariant. Neither assertion is in Barge's theorem; they require fresh proof. Reversal gives the symmetric initial-constant/final-injective case but not the desired bi-injective case.

### C. Relative BD/BK strand subsystem for CK-v3 generally

Translate a hypothetical *closed nonproductive* balanced-pair SCC into a finite forward-invariant labelled two-strand family with no eventual coincidence. BD supplies the coincidence model; BK supplies the strand realization **in its stated unimodular scope**. The hard open step is a **relative** coincidence theorem excluding that particular invariant family, not merely establishing one good pair somewhere in the system. In the non-unit regime, do not replace the required adelic/internal coordinates by an unjustified real stable lattice; see [the #139 transfer matrix](p1b-strict-zipper-literature-gate-2026-09-21.md).

This third route is more closely related to the project's primary #138/#139 overlap and proximality work, but **CK-v3 is not being promoted to the shortest proof dependency**.

## 6. Research gate and acceptance criteria

This PR contributes **literature classification**, not a new finite algorithm. No Mojo kernel, Python oracle, finite census, proof dependency or manuscript theorem is changed.

For a subsequent theorem-facing PR to assert BI or CR, require:

1. Exact definitions of the balanced-pair states, canonical side-swapping, sign convention, and period-wrap cochain.
2. An occurrence-preserving source-to-child map with a proof of any claimed endpoint/context factorization.
3. A deterministic exact replay outside the small ternary sample (including non-Pisot controls and cap/refusal reporting); new algorithms should be **Mojo-first** under [AGENTS](../AGENTS.md).
4. A proof of the universal quantifier (or an explicit finite/conditional scope), not a fitted cohomology identity.
5. Separate proof of CR; no “global endpoint collision therefore SCC endpoint coincidence” shortcut.
6. An audited bridge from any SCC statement to the actual seedwise overlap/PSC goal, preserving the repository's primary-route distinctions and all non-unit hypotheses.

**Research verdict:** no published theorem located in the survey identical to BI, Branch-B Perron-compatible signing, or CK-v3. The closest proven endpoint-specific theorem is Barge 2016 (initial-injective/final-constant), not bi-injective exclusion. The conjecture is credible as a **side-route** but remains open; the strongest next experiment is the *endpoint-sign factorization gate*, and the most established conceptual alternative is Barge-style stable-equivalence or BD/BK-style relative coincidence.

## 7. Stable source index

Primary sources (journal or author preprint identifiers):

- Barge–Diamond (2002), *Coincidence for substitutions of Pisot type*, [DOI 10.24033/bsmf.2433](https://doi.org/10.24033/bsmf.2433).
- Sirvent–Solomyak (2002), *Pure discrete spectrum for one-dimensional substitution systems of Pisot type*, [DOI 10.4153/CMB-2002-062-3](https://doi.org/10.4153/CMB-2002-062-3).
- Hollander–Solomyak (2003), *Two-symbol Pisot substitutions have pure discrete spectrum*, [DOI 10.1017/S0143385702001384](https://doi.org/10.1017/S0143385702001384).
- Canterini–Siegel (2001), *Automate des préfixes-suffixes associé à une substitution primitive*, [DOI 10.5802/jtnb.327](https://doi.org/10.5802/jtnb.327).
- Barge–Kwapisz (2006), *Geometric theory of unimodular Pisot substitutions*, [DOI 10.1353/ajm.2006.0037](https://doi.org/10.1353/ajm.2006.0037).
- Akiyama, Barge, Berthé, Lee, Siegel (2015), *On the Pisot substitution conjecture*, in *Mathematics of Aperiodic Order*, Progress in Mathematics 309, pp. 33–72, [DOI 10.1007/978-3-0348-0903-0_2](https://doi.org/10.1007/978-3-0348-0903-0_2).
- Barge–Štimac–Williams (2013), *Pure discrete spectrum in substitution tiling spaces*, [DOI 10.3934/dcds.2013.33.579](https://doi.org/10.3934/dcds.2013.33.579).
- Akiyama–Lee (2011), *Algorithm for determining pure pointedness of self-affine tilings*, [DOI 10.1016/j.aim.2010.07.019](https://doi.org/10.1016/j.aim.2010.07.019).
- Barge–Kellendonk (2013), *Proximality and pure point spectrum for tiling dynamical systems*, [arXiv 1108.4065](https://arxiv.org/abs/1108.4065).
- Barge (2016), *Pure discrete spectrum for a class of one-dimensional substitution tiling systems*, Thm. 3.13, [DOI 10.3934/dcds.2016.36.1159](https://doi.org/10.3934/dcds.2016.36.1159), [arXiv 1403.7826](https://arxiv.org/abs/1403.7826).
- Barge, *The Pisot conjecture for beta-substitutions*, [DOI 10.1017/etds.2016.44](https://doi.org/10.1017/etds.2016.44).
- Mossé (1996), recognizability, [DOI 10.24033/bsmf.2283](https://doi.org/10.24033/bsmf.2283); Solomyak (1998), unique composition, [DOI 10.1007/PL00009386](https://doi.org/10.1007/PL00009386).
- Sellami–Sirvent (2016), *Symmetric intersections of Rauzy fractals*, [DOI 10.2989/16073606.2015.1073189](https://doi.org/10.2989/16073606.2015.1073189).
- Gohlke–Mitchell–Rust–Samuel (2026), *Rauzy fractals of random substitutions*, [DOI 10.1016/j.aim.2025.110713](https://doi.org/10.1016/j.aim.2025.110713).
- Nakaishi (2024), *Pisot Substitution Conjecture and Rauzy Fractals*, **unadopted preprint claim**, [arXiv 2401.07771](https://arxiv.org/abs/2401.07771).

**Source provenance:** literature mapping distilled from the requested Deep Research investigation and the cited repository literature gates. No local experimental result was certified anew in this change. This source map is navigational, not a machine-verified theorem import.

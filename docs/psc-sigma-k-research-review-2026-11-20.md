# Spectral and coincidence results for the PSC sigma k proofs

Research assessment through 20 November 2026

**Status:** Literature review and formalization roadmap. Published theorems,
preprint claims, repository proofs, and proposed transfers retain their separate
scopes. This document adds no governed claim promotion or new Lean proof.

## Publication addendum on 21 November 2026

Sections 1–12 retain the literature cutoff of 20 November 2026 and the original
repository baseline `4f325038d4268bacbccd6e835ff7dc362d96c4bc`. Before publication,
repository status was rechecked at main
`8bbc05b898b48b3ad97fcab0534a128998ec9677`. The following internal advances
supersede the earlier status descriptions in Sections 5, 10 and 11. They do not
change the external-literature findings or complete the family's formal
spectral implication. The family bridge, arithmetic and hull sources did not
change between those revisions.

**Marker decision.** PR #631 has merged, including the executable finite marker
product. PR #635 proves one-orientation literal reachability and certificate
correctness in Lean under an exact Parikh-acceptance contract and three-step
nilpotence of the mod-two letter rows. The Perron reserve, packed executable
keys, resource refusals, two-sided geometric identification, and uniform
existence of a violating cut retain separate obligations. The earlier
description of the canonical product as unfinished is therefore historical.
See the [updated marker note](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bbc05b898b48b3ad97fcab0534a128998ec9677/docs/c4-marker-reachability-2026-11-20.md).

**Stack review and graph spectrum.** PR #634 records a review of the stack
argument and derives the trivial-stack and twin-endpoint reductions. PR #637
adds an independent written review of the graph-spectrum bridge and Lean
theorems factoring the edge characteristic polynomial through the cycle space
and boundary image, with finite-vertex eigenvalues restricted to zero and roots
of unity. Compatible graph construction, identification with hull cohomology,
and assembly of the graded word argument remain written deductions. The
earlier pending-review description must be read at its original cutoff.
These are recorded written reviews; independent human review is not asserted.
Under the repository's progression policy, pending human review alone does not
block use at an established scope; missing hypotheses and formal bridges
remain actual obligations. See the [graph-spectrum review and its evidence table](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bbc05b898b48b3ad97fcab0534a128998ec9677/docs/c4-graph-spectrum-review-2026-11-21.md).

**Remaining global rank-two case.** PR #636 supplies a written reduction
without assuming a strict system. Its fixed-tiling count and twin parity
argument, together with the stated cohomological imports, leave an
eventual-range graph $K_{2,2}$, two non-injective endpoint maps, and
$\chi_M\equiv t^3\pmod 2$. This is a residual classification, not an exclusion:
twins branching on the collapsed pair remain unresolved. The corpus replay
does not compute coincidence rank. See the [rank-two residue note](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bbc05b898b48b3ad97fcab0534a128998ec9677/docs/c4-nonunit-rank-two-residue-2026-11-21.md).
PR #636's source head is `629d3c60f71817b76d479deaa6b802dc0c25a4ff`; its merge
commit is `bf31dfa49687748de5da998cc7c4cfbf00fa113f`.

**Property (F).** The merged FC2 follow-up #608 formalizes an integer-rank
bound of two under a named Barge–Diamond coincident-pair hypothesis. Its
composition with the reviewed nonunit strict-system argument remains a written
geometric deduction. Unit determinant, higher ranks outside that composition,
finite-carrier extraction from arbitrary failure, and universal C4 remain
open. See the [FC2 update](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/8bbc05b898b48b3ad97fcab0534a128998ec9677/docs/c4-fc2-orientation-2026-11-17.md)
and the graph-spectrum review's final scope section.

## 1 Assessment and scope

The most useful next step for the family σₖ is to complete its formal spectral bridge. At the inspected repository revision, the finite balanced-pair obligation for every k ≥ 2 has already been proved in Lean, and the family note applies the published Barge–Štimac–Williams criterion to conclude pure discrete spectrum for the associated tiling action. The current Lean endpoint establishes the criterion’s arithmetic and full-factor hypotheses; its conclusion is not yet a spectral assertion about an actual dynamical system. The broader universal coincidence programme remains a separate problem. [1–3]

There is a material external revision in the focused review period of 14–20 November 2026. Creutz and Pavlov posted version 3 of their low-complexity spectral paper on 15 November. It corrects the description of the maximal equicontinuous factor and repairs a balancedness argument. Its principal spectral threshold was already present in the 2023 version. The original σₖ coding cannot satisfy that threshold: the family’s rationally independent letter frequencies imply factor complexity at least 2n + 1. This exclusion is derived in Section 4 and prevents an attractive but inapplicable shortcut. [6–8]

No newly verified external result found in this review directly removes the family’s remaining formal spectral boundary, proves universal BH or residual A1′, or completes the general C4 extraction argument. This is a bounded finding about the reviewed sources, not a claim that the entire subject was inactive. The useful recent developments concern effective arithmetic automata, recognizability, eigenvalues, and distinctions among kinds of finite fibres. Each has a specific role; none can silently replace coincidence productivity or a proof of spectral completeness.

The review covers consequential publications and preprints from 2024 through 20 November 2026, with the seven-day window checked separately. Older results are included when they supply the actual implication needed by the family. Publication dates, first submissions, and revisions are distinguished. A recent crawl date, a journal issue date, or a date generated inside an HTML rendering is not treated as a new theorem. Statements about the project are frozen to main revision 4f325038d4268bacbccd6e835ff7dc362d96c4bc, with separate branch references where necessary. [1,4,5]

The assessment distinguishes published theorems, preprint claims, repository proofs, and proposed transfers. Source inspection was performed for this review; no new Lean compilation or independent replay of archived acceptance artifacts was performed. Historical acceptance remains attached to its recorded source revision. Mathematical deductions made here are identified explicitly and are not described as new Lean results.

## 2 The family result and the exact remaining boundary

The substitution under consideration is

$$
\sigma_k(0)=1,\qquad \sigma_k(1)=0\,1^k\,2,\qquad \sigma_k(2)=001.
$$

The principal formal family theorem has domain k ∈ ℕ with k ≥ 2. The repository’s external mathematical conclusion extends to k ≥ 1 because the first member is covered by a separate published small-trace result. This extension does not enlarge the domain of the combined Lean endpoint. [1,18]

### The arithmetic constrains which literature applies

With source letters indexing columns, the incidence matrix and characteristic polynomial are

$$
M_k=\begin{pmatrix}0&1&2\\1&k&1\\0&1&0\end{pmatrix},\qquad M_k^2=\begin{pmatrix}1&k+2&1\\k&k^2+2&k+2\\1&k&1\end{pmatrix}.
$$

$$
\det M_k=2,\qquad f_k(X)=X^3-kX^2-2X-2.
$$

The square of Mₖ is strictly positive for k ≥ 1. The only possible rational roots of the monic cubic are ±1 and ±2; its values there are −k−3, −k−1, 2−4k, and −4k−6, respectively. Thus fₖ is irreducible over ℚ for integer k ≥ 1. Its discriminant is −8k³ + 4k² − 72k − 76 < 0. The unique real root βₖ exceeds 2, and the conjugate pair has squared modulus 2/βₖ < 1. For k ≥ 2 one also has k < βₖ < k+1. These elementary calculations agree with the family arithmetic already present in Lean. [1,2]

Every member is therefore primitive, irreducible Pisot, and non-unimodular. The last property matters throughout the review. A result assuming determinant ±1 or a Pisot unit cannot be applied by omitting that hypothesis. Inverse limits or the appropriate finite-place coordinates must be retained whenever a construction depends on invertibility or on a nonunit representation space.

### The finite coincidence assertion is already universal in the parameter

The exact declaration Psc.ParameterFamilyBridge.spectral_criterion_inputs takes only k and the proof of 2 ≤ k. It provides primitive incidence, an irreducible characteristic polynomial, an irrational expanding root, a positive length eigenvector, contraction of the other roots, and the complete balanced-pair factor condition for the literal seed (01,10). Its factor clause quantifies over every irreducible factor of every actual substituted iterate. The set of such factors is finite, and every member has a later iterate containing a singleton diagonal coincidence. [2]

This is the correct strength for the paper-level spectral application. It is stronger than a finite sample, a list of promising paths, or strong coincidence alone. It does not say that every possible choice of child eventually reaches a coincidence. A state can have both a recurrent noncoincident path and another path that reaches a coincidence. The family’s k = 2 control also prevents promotion of eventual productivity to the stronger immediate-exit property, which begins at k ≥ 3. [1]

The family work is on main through the integration associated with PR #574. Older PRs #570, #572, and #573 are predecessor records rather than the current location of unfinished family coincidence work. The appropriate baseline is the actual theorem and current source, with earlier test receipts retained under their original revisions. [4]

### The published implication remains the shortest route

Barge, Štimac, and Williams, Corollary 2 of Pure discrete spectrum in substitution tiling spaces, gives a sufficient condition for pure discrete spectrum of the tiling ℝ-action: an irreducible Pisot substitution with a distinct-letter seed (ab,ba) whose balanced-pair algorithm terminates with coincidence. The paper’s full-factor definition requires both finiteness and productivity of every encountered irreducible pair. It imposes no unimodularity condition. Theorem 3.2 gives the more general version using two words of rationally independent Perron lengths. [3]

The repository has aligned its endpoint with this definition. What remains is to connect that endpoint to a formal construction of the family hull and to a formal proof of the spectral implication. A theorem concluding an arithmetic conjunction is valuable evidence, but is not definitionally interchangeable with a theorem that eigenfunctions span the L² space of the tiling action.

| Obligation | Current evidence | Consequence for the next step |
| --- | --- | --- |
| Literal family arithmetic | Lean endpoint for all k ≥ 2 | Reuse the exact matrix and words |
| Finitely many full-iterate balanced factors | Lean endpoint for all k ≥ 2 | No new family carrier discovery needed |
| A coincidence descendant for every factor | Lean endpoint for all k ≥ 2 | Retain existential paths and full coverage |
| Primitive nonperiodic FLC hull | Standing argument in mathematical prose | Instantiate and prove the actual hull hypotheses |
| Balanced pairs imply pure discrete spectrum | Published external theorem | Formalize the implication or label the external boundary |
| General BH and finite strict-carrier extraction | Separate open obligations | Do not make family closure depend on universal closure |

## 3 Recent work ranked by relevance

The following register separates publication status from usefulness. “Applicable” means the stated hypotheses are compatible with σₖ; it does not mean that a theorem has already been imported or its implementation certified.

| Work | Verified status and date | Role for σₖ |
| --- | --- | --- |
| Carton and collaborators on recurrence automata | Refereed WORDS proceedings, 30 June 2025 | Effective arithmetic and address automata |
| Couvreur and collaborators on abelian complexity | Preprint v2, 22 April 2025 | Exact Parikh predicates and certificate construction |
| Berthé, Cecchi Bernales and Yassawi on eigenvalues | Journal of Modern Dynamics, 21 March 2025 | Construct continuous eigenfunctions under explicit hypotheses |
| García-Ramos and León-Torres on coincidence rank | Nonlinearity, 23 June 2025 | Reformulate rank bounds through equicontinuity |
| Haupt on stability and fibre degree | Journal article, 8 November 2025 | Distinguish residual from almost-everywhere fibre bounds |
| Gohlke and collaborators on random Rauzy fractals | Advances in Mathematics, February 2026 | New geometric method; unit hypothesis blocks direct transfer |
| Walton on recognizability | Preprint v2, 28 May 2026 | Replace inflation bijectivity once hull hypotheses are proved |
| Mercat on morphic eigenvalues | Preprint v1, 21 April 2024 | Independent algebraic eigenvalue computation |
| Creutz and Pavlov on low complexity | Preprint v3, 15 November 2026 | Material correction; original σₖ fails the complexity hypothesis |
| Nakaishi on PSC | Preprint v1, 15 January 2024 | Claimed closure with an unresolved source-audit objection |

The dates above are publication or version dates, not discovery dates. In particular, the random Rauzy paper first appeared in 2024 and its relevant revised preprint appeared in November 2025; its 2026 journal issue is a publication milestone. The recurrence-automata work is a peer-reviewed conference paper even though its arXiv page does not supply a journal reference. [6,9–18]

## 4 The November revision and an exact exclusion for sigma k

Creutz and Pavlov prove that an infinite minimal subshift with limsup p(n)/n < 3/2 is measurably isomorphic to its maximal equicontinuous factor, hence has discrete spectrum. Version 3, dated 15 November 2026, allows the factor to be a twisted product of an odometer and a connected one-dimensional compact group. The older version asserted a direct product. The new Corollary B provides an additional rational-eigenvalue condition under which splitting follows. [6,7]

The revised balancedness proof also explicitly replaces an invocation whose hypotheses were too restrictive with a prefix–suffix argument. Balancedness and the orbit-equivalence classification were already in version 2; their appearance in the new abstract does not make them new November theorems. No peer-reviewed publication of the revised paper was verified. [6,7]

The following calculation is a deduction for this review. Let β be the Perron root of fₖ. A right Perron vector is r = (β+2, β², β), since Mₖr = βr follows directly from β³ = kβ² + 2β + 2. Its normalized coordinates are the letter frequencies of the primitive substitution. If a, b, c ∈ ℚ satisfy a(β+2) + bβ² + cβ = 0, then

$$
b\beta^2+(a+c)\beta+2a=0.
$$

Irreducibility of the cubic forces a = b = c = 0. Normalization preserves rational independence. Tijdeman’s published complexity bound says that q rationally independent letter frequencies force p(n) > (q−1)n for every n. Therefore

$$
p_{\sigma_k}(n)\ge 2n+1.
$$

The recent threshold cannot apply to the original family coding. This is a proof of inapplicability, rather than a failure to locate a sufficiently efficient complexity estimate. It also avoids conflating bounded abelian complexity with small factor complexity: counting Parikh classes forgets order, whereas p(n) counts distinct words. [8]

For a finite-radius topological conjugacy, the languages in each direction are related by a bounded increase in window length, so the asymptotic linear-complexity obstruction persists. An induced return system would require a separate argument connecting its measure and dynamics to the original system. It should not be proposed merely as a way to bypass the failed hypothesis.

The useful lesson for the existing solenoid work is narrower. A group extension must be constructed with its actual cocycle or inverse-limit data; a convenient direct-product description needs proof. The revision does not itself describe the σₖ factor, and the family’s spectrum should continue to rest on its established coincidence criterion.

## 5 Effective automata and the coincidence programme

### A published arithmetic construction

Carton, Couvreur, Delacourt, and Ollinger introduce linear recurrence sequence automata. Under a recurrence polynomial that is Pisot up to an initial zero-root part, the relevant languages are regular. Theorem 0.1 gives synchronized addition in the abstract numeration system associated with a Pisot substitution; Theorem 3.2 supplies the underlying regularity result. Their WORDS 2025 paper includes a practical Walnut implementation. [9]

For σₖ, the irreducible cubic and its contraction are available as exact data. This makes the result a plausible foundation for checking arithmetic of substitution addresses without relying on floating-point equality. The original substitution is not prolongable on a letter: its first-letter map has a two-cycle. A construction based on a one-sided fixed point should explicitly choose a suitable power, such as σₖ², and prove the correspondence back to the original language and address conventions.

A productive formalization would separate the mathematically specified automaton from its generator. The generator can discover states; a small Lean checker can verify that a returned finite carrier contains the initial configurations, implements every literal transition, respects the value map, and accepts precisely the target arithmetic relation. The claim then depends on the checker’s soundness theorem and the checked certificate. A successful Walnut or Mojo run alone would remain a computational result with its own trust assumptions.

The quantifiers matter. An algorithm for each fixed k does not supply one finite automaton handling all unbounded k. To make a uniform family theorem, the proof must establish a parameterized invariant or a symbolic family of certificates. This is already the pattern used by the σₖ carrier theorem and should be preserved in follow-up work.

### Parikh predicates and their additional hypotheses

Couvreur, Delacourt, Ollinger, Popoli, Shallit, and Stipulanti develop effective constructions for generalized abelian complexity. Their 2025 preprint relates prefix Parikh vectors to synchronized sequences and constructs automata using Walnut. The stronger statements about higher block counts have additional hypotheses: Section 4.2 requires the induced length-two block substitution to be ultimately Pisot for the broad boundedness and automaticity conclusions. The displayed examples do not justify dropping that check for a new substitution. [10]

For the project, the highest-value transfer is exact evaluation of prefix and interval counts. Such predicates could help certify the all-level marker decision developed on PR #631. That branch already distinguishes checked register identities from the written finite-decision argument and the unfinished canonical product implementation. The published arithmetic theorem can inform a proof of the state semantics; it cannot establish that a desired marker violation is present for every surviving strict presentation. [5,9,10]

Three logically separate results should remain visible. First, a recognizer decides a predicate on all encoded inputs. Second, the predicate is connected to the actual ordered words or realized overlaps. Third, a theorem proves that every object in the target class has an accepted witness. The first two do not imply the third. Likewise, constructing a finite graph does not prove that every relevant state reaches its coincidence basin.

For general BH, the useful obligation is full occurrence-preserving closure. A certificate must cover every realized initial overlap and every outgoing child, then provide an actual composable route to zero integral displacement from every required state. A selected noncoincident cycle is not an obstruction if another child escapes. Conversely, observing many good exits does not rule out an unexamined child-closed nonproductive component. These requirements describe the semantic content to preserve when applying automata methods; they are not new consequences of the literature.

## 6 Recognizability and the two different fibre problems

Walton’s revised preprint proves unique composition modulo translation for compact Hausdorff expansive substitutional pattern spaces. Theorem 5.2 does not require minimality. Proposition 5.3 expresses the size of a substitution preimage in terms of a period-group index; nonperiodic patterns have unique preimages. This extends classical recognizability beyond the primitive setting. The latest verified version is 28 May 2026, and the work is still identified as a preprint. [11]

This is relevant to the imported assumption that inflation on the legal hull is bijective. Before using it, the Lean object must be shown to satisfy the paper’s topology, compactness, finite-local-complexity and substitutional-space definitions, with an expansive dilation and the required nonperiodicity. Surjectivity belongs in that construction as well. In the primitive one-dimensional family, a formalization of the older Solomyak unique-composition theorem may require less infrastructure than Walton’s broader framework. [11,19]

Inflation fibres and realization fibres must be separate interfaces. The first concerns preimages under the map taking a tiling to its substituted tiling. The second concerns all tilings mapping to one point of an equicontinuous factor. Unique desubstitution does not imply a one-point realization fibre. Walton’s theorem cannot be used to fill the BBK finite-fibre field merely because both statements contain the word “fibres.”

The current repository has already improved two older gaps. It derives its stable contraction estimate from characteristic-polynomial hypotheses, and it proves continuity of translation and forward inflation for an ordinary local hull topology. The construction of the realization map remains more demanding: its continuity must follow from its dependence on desubstitution histories. The identification of that map with the BBK realization, used to invoke BBK’s finite-fibre theorem, is still a written argument. [20–22]

One plausible proof decomposition is to establish local control of finitely many desubstitution levels, estimate the tail using the uniform contraction already proved, and combine those estimates in the ordinary hull topology. This is a proposed route, not a claim that recognizability alone provides the necessary continuity estimate. Compactness of the target solenoid must also be kept distinct from compactness of the source hull.

For σₖ specifically, the immediate implementation task is to assemble the known positive length vector and literal substitution into the existing LengthSubst structure, then obtain PisotData through the general theorem. A finite census of short substitutions does not instantiate the unbounded family: the image 0 1ᵏ 2 grows with k. The family theorem provides the needed symbolic arithmetic directly. [1,20]

## 7 Eigenvalue results and what they can certify

Berthé, Cecchi Bernales, and Yassawi’s peer-reviewed 2025 paper develops coboundary criteria for finitary recognizable S-adic systems. Its Theorem 4.7 supplies continuous eigenvalues from a weak coboundary and summable convergence, under straightness, recognizability, recurrence of the substitutions, and aperiodicity. This is a theorem about constructing eigenfunctions under specified dynamical hypotheses. Its constant-length specializations should not be applied to the unequal-length images of σₖ. [12]

Mercat’s 2024 preprint gives an algebraic algorithm for eigenvalues of morphic subshifts. Theorem 5.1 assumes a primitive aperiodic substitution and a recognizable word morphism. It uses coboundaries, generalized eigenspaces, and the rational module of vectors that become integral under powers of the incidence matrix. The general algorithm is not restricted to unimodular substitutions, so the identity-morphism instance is a plausible independent check for the family. The separately stated unimodular weak-mixing criterion has a narrower scope. [13]

For a formalization, these papers suggest a useful intermediate target: construct explicit eigenfunctions and verify their eigenvalue equations against the actual action. The contraction estimate may provide the summability input, but the coboundary and recognizability conditions must still be proved. A certified eigenvalue computation would also test whether a proposed factor has the correct arithmetic.

The remaining spectral question is completeness. Pure discrete spectrum requires that the closed span of eigenfunctions is the whole L² space. Knowing every eigenvalue, or even constructing many eigenfunctions, does not by itself rule out a continuous spectral component. This is why the existing balanced-pair implication remains central. The report uses “spectrum” in this dynamical sense; results about spectra of Schrödinger operators associated with substitutions address a different object.

For the final theorem, the translation action, its invariant probability measure, the Koopman representation, and the meaning of pure discreteness should be explicit. The tiling ℝ-action and the symbolic ℤ-shift should receive separate statements. A transfer theorem between them can then be invoked or formalized with its hypotheses visible. Variable tile lengths make that transfer a genuine step rather than a change of notation. [3,18]

## 8 Coincidence rank and almost everywhere injectivity

García-Ramos and León-Torres’ Nonlinearity paper gives a dynamical characterization of finite coincidence rank. In the precise indexing of Corollary 5.6 in arXiv v2, a minimal continuous action of a σ-compact abelian group is cover m-equicontinuous exactly when its coincidence rank is less than m. Consequently cover 2-equicontinuity would exclude coincidence rank two; cover 3-equicontinuity would only yield a bound of two. The introduction uses different shorthand, so a formal import should follow the definitions and numbered body result. [14]

This offers an alternative statement to target after the ordinary hull and its equicontinuous factor have been constructed. It does not provide the required cover-equicontinuity estimate. It also does not identify a candidate factor map as maximal, or extract an inflation-periodic partner from an arbitrary fibre. Translating a difficult rank statement into an equivalent dynamical property is useful only if the new property can be proved from the project’s combinatorics.

Haupt’s published 2025 work distinguishes two other fibre assertions. Frequent (m+1)-stability characterizes an almost m-to-one extension of the maximal equicontinuous factor, where “almost” is topological and residual. Diam-mean (m+1)-equicontinuity characterizes an almost-surely m-to-one extension, measured on the factor. Its acting-group assumptions include ℝ as well as ℤ. [15]

For the Lean design, this supports separate definitions for a bound on every fibre, a bound on a residual set of fibres, a bound almost everywhere, and a bound on the number of mutually nonproximal points in a fibre. None of these should be represented by a shared unqualified “finite rank” field. A published theorem can relate the fields under the right hypotheses, but cannot erase the distinction. Almost-everywhere injectivity of the appropriate measured factor is directly relevant to spectral completeness; a finite upper bound larger than one is not enough.

These results are best treated as reusable interfaces, rather than as immediate replacements for the existing single-seed proof. They may become more useful for C4, where the project already reasons about rank-two fibres and strict joinings. Their applicability must still be established for the same topology and map used by that argument.

## 9 Rauzy geometry and claims of universal closure

### A published criterion requiring unimodularity

Gohlke, Mitchell, Rust, and Samuel develop Rauzy fractals and natural measures for random substitutions. The paper is published in Advances in Mathematics 485 (2026), after online publication in November 2025. Corollary 6.5 gives a spectral criterion for recurrent sequences from a compatible collection of unimodular irreducible Pisot substitutions: an enveloping random Rauzy fractal of volume below twice a lattice fundamental-domain volume forces pure discrete spectrum. [16]

That hypothesis fails directly for σₖ because det Mₖ = 2. Also, changing k changes the incidence matrix, so the collection of all σₖ cannot simply be declared compatible. A nonunit version would need its own representation space, measure normalization, covering-multiplicity argument, and a checked bridge back to the deterministic systems. Those are new obligations. The method may motivate research on a fixed matrix and its reordered substitutions, but it is a longer route to family closure than the balanced-pair theorem already available.

This also illustrates a general reading rule. A multicovering theorem does not determine that the covering degree is one. A natural measure or a factor map does not automatically prove that the factor is measurably complete. The decisive quantity must be shown to have the value needed by the spectral criterion.

### The Nakaishi claim requires a source repair

Nakaishi’s Pisot Substitution Conjecture and Rauzy Fractals claims a universal irreducible Pisot spectral conclusion through prefix–suffix dynamics and Rauzy geometry. The verified arXiv history still contains only v1 of 15 January 2024, with no verified journal publication. An internal date appearing in the HTML is not evidence of a new 2026 revision. [17]

The project’s targeted audit identifies a specific difficulty in Proposition 5: a second-coordinate first return is equated with a first simultaneous return. With the audit’s event notation, inclusion–exclusion gives

$$
m(H_j)=s_j-m(E_0)+m(E_0\cap H_j).
$$

The printed argument drops the intersection term. Under the stated recurrence setup, that term tends to the positive mass subtracted in the proposed contradiction, so the contradiction disappears. The audit also records separate support and shrinking-scale transfer obligations. This is an internal mathematical objection to a specific proof step, not a published erratum, a counterexample to PSC, or a report of a community verdict. [23]

The appropriate disposition is to keep the universal conclusion outside the imported theorem set until the stopping-time and geometric transfers are repaired and independently checked. Generic mixing, recurrence, or proximity must not be promoted to an exact occurrence-labelled coincidence witness. The exact requirement is a compatible prefix-difference identity at a finite inflation level, with the original ordering and nonunit coordinates retained.

## 10 A material internal advance in the broader C4 programme

The inspected main includes PR #633, which claims a written exclusion of the nonunit ternary coincidence-rank-two strict residue, including even determinant. Its argument uses proper return and stack graphs, restrictions on their edge spectra, and ordered-product labels. Nonunit field norms separate tensor-degree eigenvalues from the allowed edge eigenvalues, allowing unique Sylvester corrections. Equality of lifted labels on common stack intervals then forces the original words to agree. [24]

The status is an unpublished repository proof with partial Lean support and independent review pending. Checked components include norm comparison, unique correction under explicit algebraic hypotheses, path transfer, and equality from common-interval premises. The geometric graph construction, the cohomology-spectrum application, the identification of the Galois norms, and assembly through all tensor degrees remain written mathematics. A merged PR does not by itself complete those proof obligations. [24]

This changes the appropriate description of the even-determinant case. It is no longer accurate to say that there has been no substantive attempt or advance. It is equally premature to describe the full obstruction as a completed Lean theorem. The decisive review should follow the actual chain from original letter cuts to the stack graph and check that every map commutes on literal paths, not only after abelianization.

The family already has a shorter spectral route, so it need not wait for this broader argument. Conversely, the family’s success does not verify all of the new graph hypotheses. General finite strict-carrier extraction and higher-rank cases remain outside the new claim. The recent external rank characterizations could supply alternative interfaces, but do not establish the graph construction or the graded lift.

## 11 Recommended next proof obligations

### Complete the family endpoint first

The next deliverable should instantiate the actual σₖ legal hull from its already proved words, positive lengths, and expansion. The construction should reuse the general spectral-to-contraction theorem rather than introduce another independent contraction assumption. Prove nonperiodicity, compactness and Hausdorffness of the ordinary hull, finite local complexity, and the action laws on this object. Where a route needs recognizability, establish it for this hull with a clearly identified theorem. [1,20,21]

Next, define the full-factor condition once and connect it by a literal theorem to spectral_criterion_inputs. The final sufficient criterion should consume those proved fields and conclude pure discreteness for the defined measured action. If the spectral theorem remains external, the document should retain the exact sentence “family criterion inputs proved in Lean; spectral conclusion obtained by a published theorem.” An assumption whose name contains “spectral” is not a substitute for the theorem’s proof.

The end-to-end result should quantify over every k ≥ 2 and contain no caller-supplied finiteness, coincidence, or desired spectral premise. Keep k = 1 as a separately sourced corollary until it receives its own formal instance. A symbolic-shift theorem should follow through a separately checked transfer, rather than through an implicit identification with the tiling action.

### Finish the realization route where it is independently needed

For the broader C4 development, continue from the existing ordinary topology and contraction results. The next precise interfaces are continuity of the constructed realization, recognizability of the source inflation, and equality with the BBK realization used by the finite-fibre input. Each interface should refer to the exact map, not merely to another map into an isomorphic-looking solenoid. The nonunit inverse limit should remain intact. [20–22]

For #633, independent mathematical review should precede any promotion of the full rank-two conclusion. Check finite refinement at original cuts, forward invariance, edge-spectrum transfer, and uniqueness at each degree. Verify existence and exact path-pullback compatibility at each required finite degree. If the formalization constructs a single inverse-limit graded object, also prove compatibility of its truncations. The existing finite algebra provides useful components without settling these global questions. [24]

### Use automata for a specified remaining predicate

The most concrete algorithmic extension is a checked recognizer for the marker or prefix-difference predicate already required by the project. Specify its input language, parameter domain, exact value map, transition semantics, and completeness before generating a large state set. Verify the resulting certificate against the original words and their occurrence labels. Only then ask whether a uniform forcing theorem guarantees a violating or coincident witness in every remaining presentation. [5,9,10]

Broad new scans should be justified by the obligation they resolve. For the family, more sampled k values add little once the universal endpoint is proved. For the general problem, a larger finite census still does not replace all-parameter carrier extraction or the assertion that every required source has an original-occurrence path to zero. The best next certificate is one whose conclusion removes a named premise from the target theorem.

## 12 Reporting when no material developments appear

For the focused 14–20 November 2026 window, the defensible finding is: a substantive correction and proof revision appeared in low-complexity symbolic dynamics, but no newly verified external result found in this review supplies the missing σₖ Lean spectral bridge or closes the universal coincidence programme. The revised low-complexity theorem is inapplicable to the original σₖ coding. Internal family integration and the nonunit C4 word-rigidity argument are reported separately from external publications.

For a future review with no qualifying changes, the appropriate wording is: “No material new or substantively revised result was identified in the checked sources during this review period. The existing proof obligations and recommended next step are unchanged.” A paper qualifies as material here if it removes a required hypothesis, supplies a usable bound or construction, corrects a relied-upon proof, or changes the validity of a proposed transfer. A new venue listing, related application, or additional numerical example is recorded only when it changes the assessment.

## References

[1] PSC repository. Spectral closure for the literal C4 parameter family. Source frozen at main 4f325038d4268bacbccd6e835ff7dc362d96c4bc. Includes the family statement, standing hypotheses, controls, and formal boundary. [Pinned research note](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/4f325038d4268bacbccd6e835ff7dc362d96c4bc/docs/c4-family-spectral-closure-2026-11-14.md).

[2] PSC repository. C4ParameterFamilyBridge.lean, especially full_factor_termination and spectral_criterion_inputs. Same frozen main revision. [Literal Lean source](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/4f325038d4268bacbccd6e835ff7dc362d96c4bc/proof/PscVerif/PscVerif/C4ParameterFamilyBridge.lean).

[3] M. Barge, S. Štimac, and R. F. Williams. Pure discrete spectrum in substitution tiling spaces. Discrete and Continuous Dynamical Systems 33(2) (2013), 579–597. Peer reviewed; online September 2012. Theorem 3.2 and Corollary 2. [Publisher](https://doi.org/10.3934/dcds.2013.33.579) · [Author full text](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf).

[4] PSC repository. PR #574, Prove BH finite reachability and simultaneous A1′ tail coincidences. Merged integration 7008992265b08ba1db6bd485085b2ab1d9b97249. The family stack is included; acceptance statements retain their source identities. [Pull request](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/574).

[5] PSC repository. PR #631, Derive and decide the original-word C4 marker law. Inspected open head a0cc36e236b591e7be0020ed96bc7dc33a0459d0. Register lemmas are distinguished from the written decision argument and unfinished implementation. [Pinned decision note](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/a0cc36e236b591e7be0020ed96bc7dc33a0459d0/docs/c4-marker-reachability-2026-11-20.md).

[6] D. Creutz and R. Pavlov. On minimal subshifts of linear word complexity with slope less than 3/2. arXiv:2308.14901v3, 15 November 2026; first submitted 28 August 2023. Preprint; journal publication not verified. Theorem A, Corollary B, Theorem 4.19, and Theorem 7.2. [Version history](https://arxiv.org/abs/2308.14901) · [Version 3](https://arxiv.org/html/2308.14901v3).

[7] D. Creutz and R. Pavlov. Same title, arXiv:2308.14901v2, 7 December 2023. Comparison baseline for the product decomposition and existing balancedness/orbit-equivalence results. [Version 2](https://arxiv.org/html/2308.14901v2).

[8] R. Tijdeman. On the minimal complexity of infinite words. Indagationes Mathematicae 10(1) (1999), 123–129. Peer-reviewed background theorem on rationally independent letter densities. [Publisher and DOI](https://doi.org/10.1016/S0019-3577(99)80010-X).

[9] O. Carton, J.-M. Couvreur, M. Delacourt, and N. Ollinger. Linear Recurrence Sequence Automata and the Addition of Abstract Numeration Systems. WORDS 2025, Lecture Notes in Computer Science 15729, 70–82. Refereed conference paper, online 30 June 2025. arXiv v3 dated 2 May 2025. [Publisher](https://doi.org/10.1007/978-3-031-97548-6_7) · [Full text](https://arxiv.org/html/2406.09868v3).

[10] J.-M. Couvreur, M. Delacourt, N. Ollinger, P. Popoli, J. Shallit, and M. Stipulanti. Effective Computation of Generalized Abelian Complexity for Pisot Type Substitutive Sequences. arXiv:2504.13584v2, 22 April 2025. Preprint; journal publication not verified. See Section 4 and Theorems 39–40. [Version history](https://arxiv.org/abs/2504.13584) · [Full text](https://arxiv.org/html/2504.13584v2).

[11] J. J. Walton. Recognisability for generalised hierarchical pattern spaces of finite local complexity. arXiv:2509.21001v2, 28 May 2026; first submitted 25 September 2025. Preprint. Theorem 5.2 and Proposition 5.3. [Version history](https://arxiv.org/abs/2509.21001) · [Full text](https://arxiv.org/html/2509.21001v2).

[12] V. Berthé, P. Cecchi Bernales, and R. Yassawi. Coboundaries and eigenvalues of finitary S-adic systems. Journal of Modern Dynamics 21 (2025), 271–325. Peer reviewed; online 21 March 2025. Theorem 4.7 in arXiv v3. [Publisher](https://doi.org/10.3934/jmd.2025004) · [Full text](https://arxiv.org/html/2202.07270v3).

[13] P. Mercat. Coboundaries and eigenvalues of morphic subshifts. arXiv:2404.13656v1, 21 April 2024. Preprint; journal publication not verified. Theorem 5.1 and Section 5.2. [Version history](https://arxiv.org/abs/2404.13656) · [Full text](https://arxiv.org/html/2404.13656v1).

[14] F. García-Ramos and I. León-Torres. Coincidence rank and multivariate equicontinuity. Nonlinearity 38 (2025), 075024. Peer reviewed; published 23 June 2025. Exact indexing here follows Corollary 5.6 of arXiv v2, 27 July 2025. [Publisher](https://doi.org/10.1088/1361-6544/ade190) · [Full text](https://arxiv.org/html/2411.03529v2).

[15] L. J. F. Haupt. Multivariate Frequent Stability and Diam-Mean Equicontinuity. Journal of Dynamics and Differential Equations, online 8 November 2025. Peer reviewed. Theorems A and B, or 4.5 and 5.6. [Publisher full text](https://doi.org/10.1007/s10884-025-10465-z).

[16] P. Gohlke, A. Mitchell, D. Rust, and T. Samuel. Rauzy fractals of random substitutions. Advances in Mathematics 485 (February 2026), 110713. Peer reviewed; online 26 November 2025; arXiv v2 dated 19 November 2025. Corollary 6.5. [Publisher](https://doi.org/10.1016/j.aim.2025.110713) · [Version history](https://arxiv.org/abs/2401.06732) · [Full text](https://arxiv.org/html/2401.06732v2).

[17] K. Nakaishi. Pisot Substitution Conjecture and Rauzy Fractals. arXiv:2401.07771v1, 15 January 2024. Preprint claim; no later version or journal publication verified. Proposition 5 is the step discussed in the source audit. [Version history](https://arxiv.org/abs/2401.07771) · [Full text](https://arxiv.org/html/2401.07771v1).

[18] S. Akiyama, F. Gähler, and J.-Y. Lee. Determining pure discrete spectrum for some self-affine tilings. Discrete Mathematics and Theoretical Computer Science 16(3) (2014), 305–316. Peer reviewed. Proposition 2.2 covers the irreducible cubic trace-at-most-two cases; the introduction distinguishes the symbolic and tiling spectra. [Published full text](https://dmtcs.episciences.org/en/articles/2089/download).

[19] B. Solomyak. Nonperiodicity implies unique composition for self-similar translationally finite tilings. Discrete and Computational Geometry 20 (1998), 265–279. Peer-reviewed background recognizability result. [Publisher and DOI](https://doi.org/10.1007/PL00009386).

[20] PSC repository. The Pisot contraction derived and Tribonacci as a PIP3 instance. Same frozen main revision, including the update linking the certified census. [Pinned source](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/4f325038d4268bacbccd6e835ff7dc362d96c4bc/docs/c4-pisot-contraction-2026-11-19.md).

[21] PSC repository. Geometric realization on the legal tiling hull. Same frozen main revision. Includes the updates on the ordinary hull topology and the remaining realization-continuity and BBK correspondence gaps. [Pinned source](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/4f325038d4268bacbccd6e835ff7dc362d96c4bc/docs/c4-geometric-realization-2026-11-19.md).

[22] V. Baker, M. Barge, and J. Kwapisz. Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces with an application to β-shifts. Annales de l’Institut Fourier 56(7) (2006), 2213–2248. Peer reviewed. Theorem 4.2 is the project’s external finite-fibre input. [Publisher and DOI](https://doi.org/10.5802/aif.2238).

[23] PSC repository. Nakaishi 2024 PSC claim first-entry audit and transfer boundary. Same frozen main revision; audit targets arXiv v1 and retains its internal-review status. [Pinned audit](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/4f325038d4268bacbccd6e835ff7dc362d96c4bc/docs/nakaishi-2024-first-entry-audit-2026-10-13.md).

[24] PSC repository. Word rigidity of the nonunit C4 stack quotient. PR #633, source 99878cd524b2a2c7f8796ccc9d3d32f1a2869e5c; merged at the frozen main revision. Unpublished written proof with partial Lean support and independent review pending. [Pinned proof note](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/4f325038d4268bacbccd6e835ff7dc362d96c4bc/docs/c4-nonunit-stack-word-rigidity-2026-11-20.md) · [Pull request](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/633).

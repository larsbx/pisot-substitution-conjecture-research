# Literature gate: bounded finite-cylinder overlap verifier

Date: 2026-11-04. Scope: a finite experimental verifier following Corollary M3 and equation (11) of [the compact M-adic counting note](c4-nonunit-madic-counting-bridge-2026-11-04.md), as present at revision `6ee339c670e711eddc4bfbe43e8b0b9dbc2876ce`. This gate does not repeat PR #494's completed occupancy replay.

## Stop/go decision

**Proceed with a bounded diagnostic and certificate checker.** Restrict the initial experiment to the two productive non-unit substitutions `1/021/001` and `1/012/001`, their common incidence matrix, and complete occurrence inventories at even depths `q = 2, 4, 6`, after checking the chosen period-two fixed-point witness. The admissible conclusions are exact finite residue separation, certified finite Euclidean outer-volume upper bounds, and a reproducible obstruction when the hypotheses needed for equation (11) are absent. Do not claim a genuine strict-component contradiction merely because a number supplied as a lower density exceeds an upper bound.

The literature supports the geometric and counting architecture, but it does not supply an actual fully strict noncoincident component for these controls or the pair-specific strict-cut density needed to finish equation (11). The companion note's compact-group construction remains a written proof dependency; executing this verifier does not formally verify it.

## Primary sources inspected

Three closely targeted primary sources suffice for this implementation gate. Their conclusions have different ambient spaces and hypotheses.

| Primary source and exact location | Relevant statement and hypothesis boundary | Consequence for this task |
| --- | --- | --- |
| Robert V. Moody, *Uniform Distribution in Model Sets* (2002), Proposition 1 and Theorem 1, pp. 125–126. [DOI](https://doi.org/10.4153/CMB-2002-015-3); [primary PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/2304DD08EC0AD970DEF94D7C180C4752/S0008439500015630a.pdf/div-class-title-uniform-distribution-in-model-sets-div.pdf). | In a cut-and-project setting, relatively compact measurable windows have the asserted density for almost every torus parameter; a Haar-null boundary upgrades this to every parameter. The averaging sets satisfy the paper's van Hove and bounded-difference-volume conditions. The Haar normalization is fixed at the start. | Finite boxes times clopen residue cylinders are appropriate regular outer windows. The almost-everywhere clause alone cannot justify the fixed phase of an irregular target. Preserve the lattice covolume when translating the normalization. This theorem gives an asymptotic density, without a usable finite convergence rate for the experiment. |
| Milton Minervino and Jörg M. Thuswaldner, *The Geometry of Non-unit Pisot Substitutions*, arXiv:1402.2002, Lemma 3.1, Proposition 6.3, Theorem 8.3, and Theorem 9.9. [Abstract](https://arxiv.org/abs/1402.2002); [primary PDF](https://arxiv.org/pdf/1402.2002). | The non-unit representation space includes the required finite completions as well as contracting Archimedean coordinates. Lemma 3.1 gives the representation-space Haar scaling. Theorem 8.3 supplies the prefix-graph set equations and regularity of subtiles for irreducible Pisot substitutions. Theorem 9.9 requires both geometric property (F) and strong coincidence for the stated tiling conclusion. | Retain every prefix occurrence and all residue information. Neither full-space regularity nor full-space measure disjointness automatically transfers to a Euclidean projection or to a differently constructed compact M-adic space. A separate identification would be needed. Here use the companion note's compact construction and direct certified containment instead. |
| Shigeki Akiyama and Jeong-Yup Lee, *Algorithm for determining pure pointedness of self-affine tilings*, arXiv:1003.2898, Theorem 3.4, equation (4.2), and Theorem 4.1. [Abstract](https://arxiv.org/abs/1003.2898); [primary PDF](https://arxiv.org/pdf/1003.2898). | Theorem 4.1 compares the spectral radii of the coincidence-reaching and residual portions of the potential-overlap graph for a self-affine tiling whose return vectors form a Meyer set. The construction retains the relevant digit pairs and edge multiplicities; potential overlap is distinguished from actual positive-volume overlap. | This is a completeness model for a finite verifier. Its result does not apply to an arbitrary finite graph presented as a strict balanced-pair component. The actual tiling, Meyer, graph-completeness, and coincidence-reachability hypotheses must be supplied before that theorem is invoked. |

These sources establish no novelty claim for graph-directed cylinders, geometric tail estimates, regular-window counting, or finite overlap graphs. The proposed contribution is a small reproducible specialization with explicit rejection of invalid evidence.

## Terminology and transfer map

| Object used by the verifier | Role | What must not be inferred |
| --- | --- | --- |
| Exact class in `Z^3 / M^q Z^3` | Finite coordinate of the compact inverse limit `H_M` | A class is not a Euclidean position, and different representatives must refine consistently. |
| Prefix occurrence `(parent, position, child, prefix)` | One term of the full inflation set equation | Repeated child letters cannot be collapsed to one term per parent or child type. |
| Euclidean slice `K_r^(q)` | Projection of the portion of the compact lifted set in one residue cylinder | Projection can destroy disjointness. Full-space zero measure does not imply Euclidean zero measure. |
| Box enclosure `B[c,r]` | Certified superset of the entire slice | A plotted sample or observed extremum is not an outer enclosure. |
| Actual strict-cut frequency `delta_e` | Lower density for the represented pair, per unit physical length | State frequency, letter frequency, a transient occurrence, or an arbitrary positive rational is not this claim. |
| Covolume `kappa` | Converts physical lattice density to the chosen internal Haar measure | Changing stable coordinates changes Euclidean volume and therefore the matching covolume. |

## Assumptions and hypotheses

Use the companion note's column-incidence convention and its compact lift. The substitution must be primitive and irreducible Pisot, with nonsingular incidence matrix `M`, Perron root `beta`, determinant magnitude `D`, a positive physical left eigenvector, and a checked fixed-point phase. Haar measure on `H_M` has total mass one, so every depth-`q` cylinder has mass `D^(-q)`. Euclidean area and lattice covolume must be computed in the same stable coordinates.

For these common-incidence fixtures, `beta` is the real root greater than two of `x^3-x^2-2x-2`, and `D=2`. These are inputs to be checked algebraically, not inferred from decimal eigenvalues. The period-two phase must be verified before using the even-depth cylinder formula.

A contradiction certificate has additional hypotheses: a real finite nonempty balanced-pair system, balance and irreducibility of its states, noncoincidence of its states, complete inflation and factorization closure, strict cuts, and a justified positive lower physical cut density for the exact represented pair. A frequency from a different component or normalization does not suffice. These extra hypotheses are absent from an ordinary productive control fixture.

## Derivation and reduction

### Exact residue disjointness is already conclusive

At a permissible depth, the companion note's full occurrence formula places each lifted letter set inside the union of the residue cylinders represented by its prefix occurrences. If two letters have disjoint exact residue supports, their lifted sets cannot meet: a point in their intersection would have a single depth-`q` residue belonging to both supports. This proves **emptiness of that lifted intersection**, conditional on the checked full inventory and the note's set identity. It is stronger than merely proving a zero volume upper bound. It does not require a lower-density input.

This argument fails if any occurrence is omitted or if the residue map is wrong. The verifier should regenerate the inventory independently from the substitution words, compare occurrence identities including positions, and check quotient membership and reduction from depth `q` to `q-2` exactly along the implemented even levels. Exhaustive support comparison is bounded and does not reproduce the earlier occupancy calculation.

### Certified Euclidean bounds for remaining pairs

For every shared residue, build a superset of the full Euclidean slice from the union of all corresponding translated contracted parent enclosures. Compute the area of the intersection of these outer unions exactly, or use a stated upper estimate that remains valid when boxes overlap. Then

`U_q = D^(-q) * sum_r area(B[c,r] intersection B[c_prime,r])`

is an upper bound for the represented lifted overlap. Exact box-union arithmetic is preferable when a crude sum obscures separation. No claim of pairwise disjointness between outer boxes is needed.

For the proposed coordinates, put `W x = (x0-a*x1, x2-b*x1)`, with `a=(beta+2)/beta^2`, `b=1/beta`, and `J=[e0 e2]`. Since `W J=I` and the kernel of `W` is the invariant Perron line, `B=W M J` satisfies `W M=B W`, hence `B^m=W M^m J`. Certifying `||B^m||_infinity < 1` by rational algebraic interval bounds gives a block contraction. Together with a bound covering **every block prefix digit**, a geometric series bounds the entire infinite tail. This supplies a genuine enclosure, unlike a finite point cloud. The implementation must check both the contraction margin and the digit bound; uncertainty in an interval comparison is a refusal, not permission to round favorably.

### The density comparison is conditional on independent evidence

Equation (11) can be checked numerically only after establishing that the claimed lower density belongs to the actual represented strict pair and uses physical-length units. The final comparison is `U_q < kappa * delta_lower`, with strict rational separation after enclosing every algebraic factor. If a symbolic frequency is per substitution state or per letter, its physical normalization must be derived explicitly. Do not divide by the average tile length twice.

A successful comparison of two supplied numbers certifies only that inequality. It does not establish the provenance of `delta_lower`, the existence of a strict component, or a contradiction in a substitution system. The proof record must distinguish those obligations.

## Evidence and replay plan

The bounded verifier may establish: exact quotient and refinement identities; completeness of occurrence inventories; certified contraction and tail inclusion; exact cylinder-cover areas and overlap upper bounds; and a strictly separated comparison under declared, independently justified density hypotheses. It may also produce a verifiable zero overlap result from finite residue separation.

The following are outside the finite replay: general compact-lattice uniform distribution, the measure-theoretic proof of Corollary M3, a universal terminating enclosure depth, and any unresolved general C4 implication. Cite the companion note for those written arguments and record their status separately from executable checks. No assertion about hosted CI completion follows from this gate.

## Negative controls and adversarial obligations

Use both productive non-unit fixtures as controls. Replay available explicit left strong-coincidence witnesses, including every letter pair, before treating any alleged strict component as genuine. PR #494 already supplies such witnesses for `1/021/001`; the second fixture needs its own checked witnesses. Low occupancy is not evidence for a strict noncoincident component.

Reject altered occurrence lists, inconsistent residue refinements, underestimated tail bounds, boxes that miss even one certified occurrence image, mismatched coordinate/covolume metadata, unsupported or misnormalized densities, and synthetic graphs presented as genuine substitution components. Synthetic examples remain useful solely as arithmetic and rejection tests with that label retained.

## Nonclaims and remaining gap

The experiment advances the overlap criterion when it computes certified slice-based upper bounds or proves finite-residue separation. It need not and should not manufacture a positive strict-cut premise to finish equation (11). If no genuine strict component and pair-specific lower-density proof are available, report that missing premise as the reproducible obstruction. If such a premise were supplied but the certified upper bound stayed too large, report the remaining geometric separation gap at the chosen finite depths.

The narrowed decision is therefore to implement the exact bounded checker and its adversarial controls, retain every hypothesis in its output, and publish proposed changes for review before any merge. This is an experimental certificate infrastructure result, not a proof of C4 or a counterexample to the Pisot Substitution Conjecture.

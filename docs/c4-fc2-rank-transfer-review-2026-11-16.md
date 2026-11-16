# FC2 coincidence-rank transfer review

Reviewed at `fca00a379087214a6fc8f002f02004c049c1436f` in [PR #590](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/590).
The PR head at review was `abcc8f4aebecbdad1d4f4a860a35239e773022da`. The FC2 argument in §4 agrees at these two revisions.

## Work shown

### Assumptions and hypotheses

Let `σ` be primitive on `d ≥ 2` letters, with incidence matrix `M`, irreducible characteristic polynomial over `ℚ`, and Pisot Perron root `β`. Normalize the positive length row `ℓ` and write `p` for the integral Parikh vector. Let `ν_L` and `ν_R` count maximum families of pairwise noncoincident letters with equal-prefix and equal-suffix witnesses, respectively. Use the left-closed, right-open prototile states of the [class note](c4-geometric-f-class-2026-11-16.md).

### Literature decision

Proceed with the rank transfer for primitive irreducible Pisot substitutions. Baker–Barge–Kwapisz (2006) supplies the edge-state rank in the required non-unit regime, Barge–Diamond (2002) supplies a coincident pair, and Barge–Kellendonk (2013) supplies the characterization of the maximal equicontinuous factor by continuous eigenfunctions. The endpoint and lattice hypotheses must be explicit in the transfer. The unimodular realization and the larger strong-coincidence test using multiple sets of control points are calibration cases. [Baker–Barge–Kwapisz](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), [Barge–Diamond](https://www.numdam.org/article/BSMF_2002__130_4_619_0.pdf), [Barge–Kellendonk](https://arxiv.org/pdf/1108.4065).

### Derivation / reduction

#### The theorem

For this class in every degree $d\ge 2$, let $c$ be the rank in Baker–Barge–Kwapisz (BBK), Definition 4.1. Then

$$
c\ge\max(\nu_L,\nu_R),\qquad 1\le\nu_L,\nu_R\le d-1.
$$

With geometric property (F), $c=\nu_L=\nu_R$. In degree three this gives $c\in\{1,2\}$. On the (F) class, FC1 and BBK Corollary 5.2 give the equivalence of absence of a strict system, prefix coincidence for every pair, suffix coincidence for every pair, rank one, and pure discrete spectrum of the self-similar tiling flow. In degree three, failure of any of these equivalent conditions gives rank two. The proof of the rank bound also works whenever an attaining family of states in each orientation reaches vertex states, since the push to vertices uses only those two finite families.

The two letter maxima can equivalently be taken over the periodic letters of their respective endpoint maps. After applying a common power to an origin-anchored separated family, choose the first descendant in each edge. Each descendant is still origin-anchored. Pairwise noncoincidence is preserved by descent, and a sufficiently large common power makes all the selected letters periodic under the first-letter map. Reversal gives the suffix version. Consequently on (F) the rank is also bounded by the smaller number of periodic letters in the two endpoint maps. Without (F), rank one still implies both all-pairs coincidence conditions by the lower bounds.

The same $c$ is Barge's minimum fibre cardinality on the maximal equicontinuous factor of the legal hull, and is Barge–Kellendonk's coincidence rank in this class. These identifications do not require (F).

#### Primary-source interfaces

| Source | Definition or result used | Scope in this review |
| --- | --- | --- |
| [BBK 2006](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), §§2–5 | Definition 4.1 maximizes over pairwise eventually noncoincident **strands** over a common point of $V/\Sigma$. Remark 4.3 gives the same maximum for edge states at **each** $q$. Equation (4.6) omits the terminal endpoint. Theorems 4.2 and 5.1 give the fibre size and spectrum of the geometric realization. Corollary 5.2 relates its rank to the tiling spectrum. | Primitive, translation-aperiodic, Pisot inflation. Footnote 4 includes automatic translation aperiodicity when $\dim V\ge2$. The inverse-limit target includes non-unit inflation. |
| [Barge–Kwapisz 2006](https://math.montana.edu/jarek/documents/papers/AJM2006.pdf), Definition 7.1, (7.2), Theorems 7.3 and 12.1 | The edge-state rank equals the minimum degree of the canonical torus map. Theorem 12.1 supplies the full return lattice in the irreducible setting of that paper. | The paper assumes unimodularity. The return-lattice argument below supplies the non-unit case of BBK's §3 lattice assertion. |
| [Barge–Diamond 2002](https://www.numdam.org/article/BSMF_2002__130_4_619_0.pdf), pp. 620–621, Theorem 1 | A distinct pair has a common letter with equal abelianized prefixes in a common iterate. | Non-Perron eigenvalues must have modulus strictly between zero and one. Irreducibility and the Pisot hypothesis supply this for both image orders. One pair excludes a separated family of all $d$ letters. |
| [Barge–Kellendonk](https://arxiv.org/pdf/1108.4065), Definitions 2.9 and 2.11, Lemma 2.14, §2.2 and Theorems 2.21, 5.4, 5.6 (arXiv v1) | The first rank is the limit of maximal uniformly orbit-separated families in one maximal equicontinuous fibre. The second is the minimum fibre cardinality. Continuous eigenfunctions determine the maximal equicontinuous fibres. Finite minimal rank and a fibre-distal point give equality of the two ranks. | One-dimensional primitive aperiodic Pisot suspension tilings have the Meyer property by the Pisot-family criterion quoted in Theorem 5.6. Theorem 5.4 supplies fibre-distal points in this case. |
| [Barge 2015](https://www.numdam.org/item/10.24033/bsmf.2691.pdf), §2, Theorem 4(1), (2), (5) | Defines rank as the minimum fibre cardinality of the maximal equicontinuous factor, attained Haar-almost everywhere. It compares the definitions in Barge–Kellendonk and the unimodular Barge–Kwapisz paper. | Scalar Pisot inflation is a one-dimensional Pisot family. The identification with the rank in the separate BBK paper follows from the comparison below. |
| [Minervino–Thuswaldner 2014](https://aif.centre-mersenne.org/item/10.5802/aif.2884.pdf), Definitions 2.1 and 9.4, Proposition 9.5, Theorem 9.10 | The (F) definition uses iterated preimages of the zero states $(0,a)$, equivalently finite expansions. Strong coincidence permits either equal prefixes or equal suffixes **per pair**. Their theorem with (F) and that coincidence hypothesis concludes the self-replicating multiple tiling has covering degree one. | Both unit and non-unit irreducible Pisot substitutions. The numbering of the three §9 results in [arXiv v1](https://arxiv.org/pdf/1402.2002v1) is 9.3, 9.4, 9.9. FC2 compares the ranks of the two uniform orientations individually. |
| [Akiyama–Lee 2014](https://www.math.tsukuba.ac.jp/~akiyama/papers/OverlapC-to-StrongC-EJC_revise4-finalSubmit2_1.pdf), Corollary 4.5, and [Akiyama 2016](https://arxiv.org/pdf/1509.04471), Theorem 3.2, Corollary 3.3 | Overlap coincidence of an irreducible Pisot suspension gives simultaneous prefix coincidence. The converse criterion in Akiyama quantifies over admissible control-point choices at some substitution level. | The FC2 proof uses BBK's edge-state formulation and the (F) absorption property. |

#### 1. Full return lattice

Here $V=\mathbb R^d$, $\Gamma=\mathbb Z^d$, and $E^s=\ker\ell$. Both Perron eigenvectors have rationally independent coordinates. For example, if a nonzero rational row $w$ annihilates the right Perron vector $r$, then each $wM^j$ annihilates $r$. These rows for $0\le j<d$ span the rational row space, since the minimal polynomial of any nonzero row under right multiplication by $M$ divides the irreducible characteristic polynomial and has degree $d$. The same argument with columns gives injectivity of $\ell$ on $\mathbb Z^d$.

Let $H$ be the group generated by the Parikh vectors of all legal segments from one occurrence of a letter to the next or any later occurrence of that same letter, excluding the second endpoint. Fix a legal two-sided sequence $x$. In $\mathbb Z^d/H$, assign each position its cumulative prefix vector relative to position zero, with the sign reversed to the left of zero. Equal letters have equal assigned values. Thus the value at $n$ is $A(x_n)$ and the value at $n+1$ is $B(x_n):=A(x_n)+[e_{x_n}]$. All letters occur, and primitivity gives the letter frequencies proportional to $r$. For every value $v$ in the finite union of the images of $A$ and $B$, counting over $n=0,\dots,N-1$ gives

$$
\sum_{A(a)=v} r_a=\sum_{B(a)=v} r_a.
$$

Indeed the two empirical counts differ by at most one before dividing by $N$. Rational independence implies equality of the two sets of letters for every $v$. Therefore $[e_a]=0$ for all $a$ and $H=\mathbb Z^d$. Every legal return segment occurs in a legal tiling in BBK's minimal hull. Lifting it by Proposition 2.3 gives two same-label edges separated by its integral Parikh vector in $\Theta(a)$ of (3.1), hence in $\Sigma$ by (3.2)–(3.3). Thus $\Sigma=\Gamma$. In BBK (3.5)–(3.9) one can choose all the corrections $u_a=0$.

#### 2. State families and left coincidence

Write $I(x,a)$ for the edge from $x$ to $x+e_a$ with label $a$. The edges over $q=0$ in BBK (4.6) are precisely

$$
I(-v,a),\qquad v\in\mathbb Z^d,\quad 0\le\ell v<\ell_a.
$$

Indeed $\Sigma=\mathbb Z^d$, and intersecting the stable hyperplane anywhere except the terminal endpoint gives exactly the two displayed inequalities. The descendant of $I(x,a)$ at the occurrence $\sigma^k(a)=P\,b\,Q$ is $I(M^k x+p(P),b)$. Hence two origin-anchored edges share a labelled descendant exactly when their seed letters have an equal-prefix strong-coincidence witness. Remark 4.3 bounds any separated family of such edges by $c$, giving $\nu_L\le c$.

BBK Remark 4.3 also gives an attaining family of $c$ states over zero. For a state $I(-v,a)$, its unique descendant meeting the stable hyperplane in the half-open convention has relative vector $Mv-p(P)$, the repository's step. By FC1's vertex-absorption lemma every state in the family reaches a vertex under (F). Use the maximum of their first hitting times and forward invariance of the zero-offset states. If two selected descendants shared an edge after another $k$ substitutions, the two original edges would share that edge after the common time plus $k$. The resulting vertex labels are therefore distinct and left noncoincident. This gives $c\le\nu_L$.

#### 3. Reflection and the right side

Put $\bar\sigma(a)=\operatorname{rev}(\sigma(a))$. For words $w$ one has $\bar\sigma(\operatorname{rev}w)=\operatorname{rev}(\sigma(w))$, so substitution powers obey the same identity. The reflection is $R I(x,a)=I(-x-e_a,a)$. At any occurrence at level $k$, the reflected descendant has left endpoint

$$
-M^k x-p(P)-e_b=M^k(-x-e_a)+p(Q^{\mathrm{rev}}),
$$

using $M^k e_a=p(P)+e_b+p(Q)$. This proves equivariance at the edge level, including all labels. Reflection preserves the stable and unstable subspaces and the radius of the strand cylinder. It reverses the order in all iterated strands and carries the BBK invariant strand space to the corresponding space for $\bar\sigma$ (and each inverse-limit coordinate likewise). Equal vertices modulo $\Sigma$ become equal vertices modulo the same lattice over $-q$, as $e_a\in\Sigma$. Reflecting the families in Definition 4.1 therefore proves $c(\bar\sigma)=c(\sigma)$. The reversed powers identify $\nu_L(\bar\sigma)$ with $\nu_R(\sigma)$.

For (F), reflect only interior periodic states. If $f^k(a,v)=(a,v)$ with $v\ne0$ and $k>0$, then $0<\ell v<\ell_a$ and $(M^k-I)v=p(P)$ at an occurrence $\sigma^k(a)=P\,a\,Q$. The reversed occurrence has prefix $Q^{\mathrm{rev}}$ and

$$
(M^k-I)(e_a-v)=p(Q).
$$

The vector $e_a-v$ has length strictly between zero and $\ell_a$, so it is a valid interior periodic state in the reversed half-open model. Reflection is involutive. Thus (F) is invariant, and the two left-side inequalities applied to $\bar\sigma$ supply the right-side inequalities.

There is also a direct check of the right lower bound. The right-anchored edges $I(-e_a,a)$ end at zero. Translate all of them by the same $t\in E^u$ with $0<\ell t<\min_a\ell_a$. The translated edges are interior states over $[t]$ and a common translation preserves eventual coincidence, since at level $n$ it becomes the common translation $M^nt$. The left endpoint of the descendant of a right-anchored edge at $P\,b\,Q$ is $-e_b-p(Q)$, giving exactly the suffix witness. Apply Remark 4.3 at $q=[t]$.

#### 4. Property (F) in the non-unit normalization

Use an algebraic scaling of $\ell$ in $\mathbb Q(\beta)$ for Minervino–Thuswaldner. With $D=\ell\mathbb Z^d$ one has $\beta D\subseteq D$ and $D\cdot\mathbb Z[\beta^{-1}]=\bigcup_{m\ge0}\beta^{-m}D$. Their half-open interval expansion slides by $x\mapsto\beta x-\ell p(P)$. A point of $\beta^{-m}D$ enters $D$ after $m$ steps because every digit belongs to $D$. Inside $D$ the map is the integral state map via injectivity of $\ell$ on the lattice. Their finite-expansion criterion is eventual zero in this map on the localized interval states. Consequently it is equivalent to eventual zero on the integral states, and hence to the absence of a nonzero periodic integral state by the Pisot bound and vertex absorption. This comparison uses localization even when $M$ has no integral inverse. In the separate BBK realization the target is the inverse limit of $M$ on $\mathbb R^d/\mathbb Z^d$, and the shift on the inverse limit is the automorphism used in the theorem.

#### 5. Coincidence rank on the maximal equicontinuous factor

Let $Y$ be BBK's full strand space in Definition 2.2, $\Omega\subseteq Y$ its legal minimal hull, $h:Y\to\mathbb T_M$ the map in BBK Definition 3.1, and $g$ the maximal equicontinuous factor of $\Omega$.

1. BBK Proposition 2.3 identifies $Y$ with the possibly enlarged tiling space. BBK §3 provides a unique invariant probability on $Y$. The invariant probability of the primitive legal hull is supported on $\Omega$ and equals this measure when viewed on $Y$. The restriction $h|_{\Omega}$ is onto because its image is nonempty, compact and invariant under the dense translation action on $\mathbb T_M$.
2. By BBK Theorem 5.1, each eigenvalue on $L^2(Y)$ is represented by a character pulled back by $h$. The $L^2$ spaces of $Y$ and $\Omega$ for the above measures are canonically identified. Each eigenspace is one-dimensional by ergodicity. Since the invariant measure has full support on $\Omega$, every continuous eigenfunction on $\Omega$ agrees everywhere with a scalar multiple of the corresponding pulled-back character. Characters of a compact abelian group separate its points. In this inverse limit it also suffices to separate the coordinates using torus characters. Hence $h|_{\Omega}$ and $g$ have identical fibres by the continuous-eigenfunction characterization in Barge–Kellendonk §2.2. The induced bijection of their compact Hausdorff targets is an equivariant homeomorphism. After a translation of the origin it identifies their Haar measures, equivalently the unique invariant probabilities for the dense translations.
3. BBK footnote 5 and §3 allow finitely many additional translation orbits in $Y\setminus\Omega$. Under projection to the zeroth torus coordinate their $h$-images lie in finitely many translates of the unstable line. Each is a countable union of images of compact line segments and is Haar-null in the $d$-torus for $d\ge2$. The projection $\mathbb T_M\to V/\Sigma$ is a surjective group homomorphism and pushes Haar to Haar. The exceptional images are therefore Haar-null in $\mathbb T_M$. Over almost every point, the $\Omega$-fibre equals the $Y$-fibre and has size $c$ by BBK Theorem 4.2.
4. Barge 2015 Theorem 4(1) identifies the generic cardinality of $g$ with its minimum, giving $c=\min_z\#g^{-1}(z)$. Barge–Kellendonk Lemma 2.14 and Theorems 5.4 and 5.6 identify this minimum with their separated-family rank in the present Pisot regime.

Corollary E needs BBK Corollary 5.2 for the spectrum and the supported measure in step 1 to read it on the legal hull. The maximal equicontinuous factor comparison supplies the rank import used in the later arguments that cite Barge 2015.

### Evidence and replay

#### Lean interface

`Psc.GeometricFPisot.fc1_pip3` gives the existing standing-class equivalence. Its module, `PscVerif.GeometricFPisot`, also has `exists_contractionData_of_pisot` and `exists_fc1_data_of_primitive_pisot`. The new rank module starts from `LengthData`, `ContractionData` and `PropertyF` and calls `reaches_vertex_of_propertyF` from `GeometricFInclusion`. The construction of the contracting coordinates is upstream of this argument.

| Lean declaration | Statement |
| --- | --- |
| `edgeCoincident_zero_iff`, `vertexCoincident_reverse_iff` | Origin-anchored edges coincide exactly for the prefix witnesses used by FC1. The reversed prefix witness is the original suffix witness. |
| `edgeDescendant_reflect`, `edgeCoincident_reflect_iff` | Reflection respects actual labelled occurrences and their eventual coincidence, with the reflected edge starting at minus its old right endpoint. |
| `reflect_left_vertex_not_state`, `propertyF_reverse_iff` | Vertex reflection crosses the half-open boundary. Interior periodic states reflect to interior periodic states when the length functional has trivial integer kernel, proved in §1 above for the irreducible incidence class. |
| `fc2_rank_lower_bounds`, `fc2_rank_transfer` | Two zero-slice rank realizations with the same rank give the lower bounds, and under (F) identify both letter maxima with that rank. `IsMaximumSize` entails attainment and bounds every finite separated family. |

The next Lean obligation is to instantiate the two zero-slice hypotheses, `IsMaximumSize (StateFamily s L) c` and `IsMaximumSize (StateFamily (reverseSubstitution s) L) c`, for an actual common BBK rank. The binding must identify the geometric zero slice with the integer states via $(a,v)\mapsto I(-v,a)$, with equality of labelled descendants at **every** power. This uses the full-return-lattice lemma and BBK Remark 4.3 for the bound and attainment. Reflection of full strands supplies the same rank parameter in both orientations. The ℤ-kernel premise is a separate algebraic binding of the rational-independence fact in §1. The spectral implication consumes BBK Corollary 5.2, and arguments about Barge's rank also consume the topological comparison in §5.

To replay the module in the repository's Lean environment, run:

```sh
cd proof/PscVerif
lake build PscVerif.GeometricFRank
lake env lean /path/to/evidence/FC2AxiomAudit.lean
```

#### Local verification

The candidate module was checked against both exact revisions with Lean `4.34.0-rc2` and the dependency revisions in the repository's Lake manifest. The focused check covers the thirteen project modules in the import closure and the named axiom queries in the evidence directory. The proof bank was regenerated and checked at the patch base, and the Markdown source and link checks passed.

The author recorded a standing-class FC1 build and axiom check in the commit message for `fca00a3`. The independent full-project replay remained incomplete. The local checks here support the new integer transfer and the FC1 absorption theorem it imports. The geometric and spectral imports are reviewed at the written-proof level.

#### Hosted evidence

| Revision | Geometric (F) regression | C4 overlap Lean verification | PSC research checks |
| --- | --- | --- | --- |
| `fca00a3` | [Queued](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43902003894) | [Queued](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43902003910) | [Cancelled](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43902004094) |
| `abcc8f4` | [Queued](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43914881862) | [Queued](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43914882321) | [Queued](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43914881773) |

### Negative controls

- Reflection on the closed **edge** $I(0,a)$ sends it to $I(-e_a,a)$, whose only intersection with $E^s$ is its right endpoint. This fails the defining inequality of the same half-open zero slice for every $a$, including for a primitive irreducible Pisot example such as Tribonacci.
- BBK Example 3.2 has a reducible characteristic polynomial and a proper $\Sigma\subsetneq\Gamma$. In that example membership in a common $V/\Sigma$ fibre requires checking the type corrections. The equalities above use the full return lattice.
- On three abstract letters, take the sole failure of left coincidence to be the pair $\{a,b\}$ and the sole failure of right coincidence to be $\{a,c\}$. Both separated-family ranks are two, and each pair satisfies the left-or-right disjunction. Thus the equality of the two ranks alone cannot replace either uniform coincidence condition by Minervino–Thuswaldner's mixed pairwise predicate. This is a logical control on the inference, without a substitution realization.

### Non-claims / remaining gaps

The transfer identifies the possible ranks on the (F) class. Excluding rank two there remains a separate obligation. Universal C4, PSC, and the proposed downstream cohomological arguments retain their pending review status. The Lean proofs check the integral transfer from stated rank inputs. The full-strand rank realization, its spectral consequence, and the maximal equicontinuous factor comparison above are written proofs using the cited primary results.

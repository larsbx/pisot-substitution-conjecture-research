# Independent review of the C4 stack graph spectrum

The graph-spectrum bridge of [#633](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/633) holds under its stated hypotheses. The argument uses Barge–Diamond on the original substitution and transfers its result to the return graph using an inflation-equivariant reblocking. Directed edge counts on that refined graph include a separate contribution from its vertices. The stack graph has a simple Perron eigenvalue and its edge spectra have the bounds required for the nonunit Sylvester argument.

The reviewed source is `99878cd524b2a2c7f8796ccc9d3d32f1a2869e5c`, merged as `4f325038d4268bacbccd6e835ff7dc362d96c4bc` with the same tree. [#635](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/635) concerns marker-certificate correctness and uses a separate Lean argument.

## Source decision

The proposed Lean increment concerns a finite graph endomorphism. Its edge characteristic polynomial factors into the action on cycles and the action on the image of the boundary. A finite vertex map contributes only zero and roots of unity to the latter factor. The increment treats these as consequences of a commuting boundary and a finite vertex map.

- Barge (2015), Theorem 12, §4 and Proposition 19, supply the stack presentation and the injective hull cohomology pullback under properness and the stated dynamical hypotheses. [Published article](https://doi.org/10.24033/bsmf.2691)
- Barge–Diamond (2008), Lemma 2, Corollary 3 and the proof of Theorem 4, supply the incidence and eventual-range exact sequence for the original primitive aperiodic substitution. Their Thue–Morse example gives an explicit transition-cycle contribution. [Published article](https://doi.org/10.1090/S0002-9939-08-09225-3) · [Open text](https://arxiv.org/pdf/math/0702669)
- Anderson–Putnam (1998) and Barge's one-dimensional construction identify the inverse-limit shift with inflation when the presentation forces its border. The proper return recoding and stack subdivision must be checked for the chosen inflation power. [Published article](https://doi.org/10.1017/S0143385798100457) · [Barge, §4](https://www.numdam.org/item/10.24033/bsmf.2691.pdf)

Proceed with the finite chain factorization and exact controls. The graph construction, inverse-limit comparison and equivariant use of the imported cohomology theorems belong to the written argument. Thue–Morse tests the independence of the original lengths. Unimodular cubic matrices test the higher-tensor resonance, even on the raw letter graph.

## Work shown

### Assumptions and hypotheses

Let $M_0$ be the original primitive incidence matrix with irreducible Pisot cubic characteristic polynomial and Perron root $\beta_0$. Write $M=M_0^p$ and $\beta=\beta_0^p$. Original tile lengths come from the positive left Perron row. The hull is aperiodic, since a periodic symbolic hull would have rational frequencies and hence rational Perron root. Finite local complexity and convex interval tiles hold. In one dimension rank two gives the absence of an almost automorphic subaction by Barge's Theorem 4 and §4.

| Imported result | Application |
| --- | --- |
| Barge, Theorem 12 | Apply to the proper return substitution with convex tiles and no almost automorphic subaction. Its stack map commutes with inflation and translation, and realizes the quotient by dense stable equivalence within maximal-equicontinuous fibres. |
| Barge, §4 and Proposition 19 | For a proper one-dimensional Pisot substitution with non-pure-discrete spectrum, the stack presentation is proper, and the stack map at graph level is induced by a letter morphism. The rational cohomology pullback is injective. Its equivariance follows by functoriality from Theorem 12. |
| Barge–Diamond, Lemma 2, Corollary 3 and proof of Theorem 4 | Apply to the original primitive aperiodic substitution at the chosen power. Use the natural exact sequence with the inflation actions. The group splitting alone carries no spectral information. |
| Theorem W(1), W(4) and Theorem NI(2) in the rank-two wall note | These give the swap-symmetric primitive strict joining, two distinct simultaneously periodic partners, and equality of their stack images with dense eventual coincidence. Their proofs and their upstream geometric-realization and coincidence-rank inputs are outside this graph audit. |

Theorem 12 and Proposition 19 have no norm parity restriction. Barge's odd-norm bound is Theorem 22, which the argument does not use. [Barge, Theorems 12 and 22 and Proposition 19](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) · [Barge–Diamond, Theorem 4](https://arxiv.org/pdf/math/0702669) · [Theorems W and NI](c4-rank-two-wall-2026-11-16.md)

### Derivation / reduction

On the finite set of legal seams take a periodic seam $b\mid a$ of the map $(b,a)\mapsto(\operatorname{last}(\sigma(b)),\operatorname{first}(\sigma(a)))$. Take a common multiple of its period, the required partner periods, and the period of the original Barge–Diamond eventual-range cell permutation. Further increase this power so that the inflated copies of $a$ and $b$ each have an interior marker. This is possible by primitivity and uniform recurrence. Each return interval between successive copies of the marker starts with $a$ and ends with $b$. Its inflated endpoints remain cuts, so inflation parses into complete return words. The first complete return word lies in the common inflated prefix $\sigma^p(a)$ and the last lies in the common inflated suffix $\sigma^p(b)$. Every finite legal list of return words between marked endpoints corresponds to a legal raw block with its two boundary letters. Uniform recurrence puts that block inside every sufficiently long inflated return word. This proves primitivity and gives the return hull every reblocked patch. Properness follows from the common first and last return words. Cutting at this locally recognizable two-letter pattern and concatenating are inverse maps of tiling spaces. They preserve physical coordinates and intertwine the chosen inflation. The two spaces therefore have the same translation and powered inflation actions. Taking a positive power also preserves the stable relation, by continuity of the finitely many intermediate powers.

Denote the proper return and stack wedges by $R_0,S_0$. Barge's graph morphism $s:R_0\to S_0$ maps each return petal monotonically along its subdivision into stack tiles, preserving physical length. At the origin projections it satisfies $\pi_{S_0}\circ q=s\circ\pi_{R_0}$. Take $U_R$ to consist of the return seam and all original letter cuts in the return petals. Inflation maps these points into $U_R$ because images start and finish at raw tile boundaries. On $S_0$ take $U_S=V(S_0)\cup s(U_R)$. The old stack vertex is carried to a vertex and $f_S s=s f_R$, so $U_S$ is forward invariant. Subdivision retains the underlying topological graphs and their bonding maps. The refined maps on oriented edges follow positive paths. The raw projection $\rho:R\to A$ reads the raw letter of each refined return edge. Both $\rho$ and $s$ commute with inflation on *literal edge paths*, because their traversals agree in order and physical coordinate and every cut in the target is included when an image path crosses it.

For a fixed stack tiling, mark each stack tile with the positions in $U_S$ for its type. This single refinement is used for both lifts. Between two common raw endpoints the directed stack path is obtained by traversing this refined tiling over that interval. In particular an interior raw cut that divides a stack tile is present for both lifts. This proves the literal path equality used in #633.

Use $\chi_T(x)=\det(xI-T)$. The original Barge–Diamond exact sequence over $\mathbb Q$ has terms

$$
0\to \widetilde H^0(ER)\to \varinjlim M^{\mathsf T}\to \check H^1(\Omega;\mathbb Q)\to H^1(ER)\to0.
$$

The eventual-range actions are identities at the chosen power. Since $M$ is invertible and has no eigenvalue 1, the reduced $H^0$ term vanishes. Put $b=\dim H^1(ER;\mathbb Q)$. Multiplicativity in the short exact sequence gives $\chi_{\Phi^*}=\chi_M(x)(x-1)^b$, including algebraic multiplicities. The matrix in this sequence is the incidence of the **original** powered substitution. It enters the computation for $R$ by the equivariant recoding. The return incidence is the separate matrix on the cycles of $R_0$.

For $G=R,S$, let $B_G$ be its edge operator, $P_G$ its vertex operator, and $\partial$ the oriented boundary. Then

$$
\partial B_G=P_G\partial,\qquad
\chi_{B_G}=\chi_{B_G|\ker\partial}\,\chi_{P_G|\operatorname{im}\partial}.
$$

The first identity follows by telescoping the boundary of each image path. The second is the characteristic polynomial identity for the resulting short exact sequence. The cycle action is the action on $H_1(G;\mathbb Q)$. Its dual is the finite-graph cohomology action. Over $\mathbb Q$ the stationary direct limit of the dual discards its generalized zero eigenspace and induces the original action on its stable image. This follows by writing the finite-dimensional space as a stable image plus a stable kernel. The forward inverse-limit shift $\widehat f$ satisfies $\pi_i\widehat f=f\pi_i$ at every coordinate. Thus Čech continuity and the inverse-limit conjugacies identify the stable dual action with pullback by forward inflation. The nonzero cycle factors are the characteristic polynomials of the corresponding hull inflation actions.

If the vertex function has $u$ transient vertices and directed cycles of lengths $d_i$, then $\chi_{P_G}=x^u\prod_i(x^{d_i}-1)$. Order the vertices by distance to the cycles to see the nilpotent and permutation blocks. The graph is connected, so the vertex augmentation $C_0(G)\to\mathbb Q$ has kernel $\operatorname{im}\partial$ and a trivial one-dimensional quotient. Thus the boundary factor is $\chi_{P_G}/(x-1)$. These extra factors can change under subdivision and are independent of the nonzero cycle action.

By equivariant injectivity of the stack cohomology pullback, its characteristic polynomial divides $\chi_M(x)(x-1)^b$. Since $\beta>1$, no boundary eigenvalue equals it. A positive length row of $B_S$ is a left $\beta$-eigenvector, so the stack cycles contain $\beta$. Its algebraic multiplicity on the stack edges is precisely one. In fact $\mathbb Q(\beta)=\mathbb Q(\beta_0)$, since a rational $\beta_0^p$ would have conjugates of different moduli. The field degree is the prime 3, so $\chi_M$ is the minimal polynomial of $\beta$. The nonzero stack cycle factor consequently has the form $\chi_M(x)(x-1)^{b_X}$ for $0\leq b_X\leq b$. The literature and construction give this bound on $b_X$. Determining $b_X$ for a specific graph requires its stack cohomology. The raw wedge has edge operator $M$.

The original Perron length map $\ell:\mathbb Q^3\to\mathbb R$ is injective, since its kernel is $M_0$-invariant and the cubic is irreducible. For an original letter length $c>0$, its image is $c\mathbb Q(\beta_0)$, as witnessed by $c,\beta_0c,\beta_0^2c$. The simple $\beta$-eigenrow over that field, evaluated on the stack path of one original-letter edge of $R$, has a nonzero value. Scaling it to that path's original length shows that all refined stack lengths are in $\ell(\mathbb Q^3)$. Summation along paths preserves the unique degree-one labels, by injectivity.

Choose a common normal splitting field $L$ containing the incidence roots and the vertex roots of unity. The absolute field norm of each nonzero powered incidence root is $D=\lvert\det M\rvert^{[L:\mathbb Q]/3}>1$. Norms of the other allowed edge roots are zero or one. Every degree $j$ tensor eigenvalue has norm $D^j$, so the finite operators are spectrally disjoint for $j\geq2$. Iterating the Sylvester correction gives compatible lifts in all finite truncations. On a path the highest-degree correction is additive because all factors have constant coefficient one. Pullback along $s,\rho$ commutes with inflation and preserves degree one, so uniqueness makes the two path products agree on an interval of two common raw cuts. The first differing homogeneous component of the positive-word expansion survives all higher-degree changes to the letter labels. Equality at all truncations therefore gives literal equality of the words.

The two partners from NI(2) and W(4) have eventual coincidences on either side of the origin. Inflate both to a common multiple of their period, using the left endpoint of a common patch on the negative side and the right endpoint of one on the positive side. These common raw cuts recur arbitrarily far out under further powers. The two partners agree throughout, contradicting their distinctness. This proves the rank-two strict-system exclusion as a written deduction at those inputs, including even determinant.

### Evidence and replay

The new module [PeriodicPartnerGraphSpectrum](../proof/PscVerif/PscVerif/PeriodicPartnerGraphSpectrum.lean) factors the edge characteristic polynomial through the kernel and image of the boundary. It reuses the repository's surjective intertwiner and invariant-subspace theorems. Its finite vertex result obtains repeated powers of the linearized vertex function and rules out nonzero eigenvalues other than roots of unity. The inputs at this interface are finite-dimensional edge and vertex spaces and a commuting boundary. The periodic graph construction and cohomology identification above establish where those inputs come from.

| Evidence class | Coverage |
| --- | --- |
| Existing Lean at #633 | `tensor_norm_separates`, `sylvester_exists_unique`, `pathProduct_add_correction`, `pullback_equivariant`, `same_stack_interval_products_eq` and `fixedTilings_eq_of_common_intervals`, at their declared hypotheses. [Exact-head hosted run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/44809326645) |
| New Lean increment | `boundary_range_invariant`, `edge_charpoly_factor`, `edge_charpoly_dvd_vertex_mul_cycles`, `vertex_power_repeat`, and `vertex_charpoly_root`. |
| Published mathematical imports | Proper stack construction and cohomology injection, Anderson–Putnam inverse limits, Barge–Diamond's original-hull exact sequence and Čech continuity. |
| Written deductions checked here | Compatible subdivision and literal path correspondence, spectral transfer through recoding, stack Perron multiplicity and length transfer, and the all-degree word-rigidity assembly. |
| Upstream inputs retained | W and NI, the geometric-realization and coincidence-rank identifications they use, and any passage from the strict-system theorem to a global hull, productivity, or spectrum assertion. |

```sh
cd proof/PscVerif
lake build PscVerif.PeriodicPartnerGraphSpectrum PscVerif.PeriodicPartnerStackWordRigidity
lake env lean /absolute/path/to/GraphSpectrumAxiomAudit.lean
cd ../..
python3 tools/make_proof_bank.py --check
```

Run `python3 graph-spectrum-controls.py` from the review files for the independent exact rational matrix replay. The control matrices use columns for images. The return refinements check $\partial B=P\partial$, the basis of the cycle space and its intertwiner, the literal label sequence of every refined image edge, and the full polynomial factorization. Their scope is the given finite samples.

### Negative controls

| Control | Exact result |
| --- | --- |
| Thue–Morse $\theta=01/10$, power 2, marker $1\mid0$ | The returns are $001,0011,01,011$. The original incidence polynomial is $x(x-4)$, the return cycle polynomial is $x^2(x-4)(x-1)$, and the refined edge polynomial is $x^7(x-4)(x-1)^4$. One $1$ survives on cohomology and three come from the boundary. Equal raw lengths make the two words $01$ and $10$ indistinguishable under equal letter labels. Barge's stack relation is trivial here. The distinct complementary tilings are twins for the later double-cover factor, so they furnish a length-label control rather than a pair in one stack fibre. [Barge, Example 16](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) · [Barge–Diamond, Example 7](https://arxiv.org/pdf/math/0702669) |
| Even nonunit $1/0112/001$, power 4, marker $1\mid0$ | The original powered polynomial is $p(x)=x^3-72x^2-48x-16$. The refined return edge polynomial is $x^{56}(x-1)^4p(x)$. The boundary accounts for $x^{54}(x-1)^3$. The refined edge polynomial is coprime to both degree-two and degree-three tensor characteristic polynomials. The example realizes a return refinement and carries no claim about a strict system or coincidence rank. |
| Circle doubling with forward-invariant cuts $0,1/3,2/3$ | The one-edge graph has polynomial $x-2$. Its subdivision has $(x-2)(x-1)(x+1)$ on edges and $x-2$ on cycles. This gives a counterexample to invariance of the full edge characteristic polynomial under subdivision. |
| Unit cubics $01/02/0$ and $01/210/1021$ | The polynomials are $x^3-x^2-x-1$ and $x^3-3x^2+1$, with determinants $+1$ and $-1$. Their third incidence powers are positive. The first polynomial has no rational root, negative discriminant and a real root above 1, so its conjugate pair has modulus less than 1. The second has no rational root and has roots in $(-1,0),(0,1),(2,3)$. The rational tensor test below exhibits raw-edge resonance in degrees 4 and 7, respectively. |

For any powered unit cubic incidence $M$ let $\omega\in V^{\otimes3}$ be the alternating tensor of three basis vectors. Then $\omega\ne0$ and $M^{\otimes3}\omega=(\det M)\omega$. Take $r=1$ when $\det M=+1$ and $r=2$ when $\det M=-1$. Tensoring by $\omega^{\otimes r}$ gives a nonzero rational intertwiner $v\mapsto v\otimes\omega^{\otimes r}$ between the raw edge operator $M$ and $M^{\otimes(1+3r)}$. The homogeneous Sylvester map has a kernel in that degree even when the raw edge operator has no neutral eigenvalue. When an edge operator does contain $1$, the invariant tensor also gives the neutral collision in degree $3r$.

### Non-claims / remaining gaps

The result reviewed here excludes *finite strict systems at nonunit coincidence rank two*, covering the even-determinant case. A global rank-two exclusion requires a separate argument. The written follow-up [#636](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/636), using [#634](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/634), still leaves a possible nonunit rank-two hull with $ER=K_{2,2}$ and $\chi_{M_0}\equiv x^3\pmod 2$ in the absence of a strict system. That residual classification is a separate written deduction.

On property (F), the composition with [#608](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/608) gives a written nonunit strict-system exclusion using Barge–Diamond's coincident pair and the geometric identification of the integer rank with the coincidence rank. Outside that composition, W(4) supplies dense eventual coincidence only at rank two. The unit case needs an argument that handles the explicit resonance. Where a productivity or PSC inference requires extracting a finite strict system from arbitrary failure, that extraction remains a separate obligation. [Universal C4, issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)

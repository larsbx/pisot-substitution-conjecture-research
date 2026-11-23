# Symbolic spectrum of the literal σₖ family

## Source decision

Transfer the measured real-translation theorem from PR #650 to the actual two-sided legal shift for \(k\ge 2\). The transfer uses the stable part of the length discrepancy.

- Clark and Sadun, *When size matters*, §3, Theorem 3.1 with exponent offset zero, gives a time-preserving flow conjugacy if the difference of positive length rows tends to zero under right multiplication by incidence powers. Corollary 3.2 supplies the length scaling when exactly one eigenvalue, counted with multiplicity, has modulus at least one. Their setting is a primitive aperiodic substitution. The criterion applies to determinant two. [Published article](https://doi.org/10.1017/S0143385702001633) · [Accessible manuscript](https://arxiv.org/pdf/math/0201152)
- Sirvent and Solomyak, §4 and Corollary 5.2, independently prove the spectral implication for primitive irreducible Pisot substitutions with the positive left PF lengths. Their convention uses an expanding one-sided fixed word, which can be obtained here from \(\sigma_k^2\) on letter \(1\). Primitivity gives the same language for the power. The squared PF root still has degree three, since \([\mathbb Q(\beta):\mathbb Q(\beta^2)]\) divides three and is at most two. The remaining eigenvalues stay strictly inside the unit circle. The existing balanced-pair certificates offer a separate proof route. [Published article](https://doi.org/10.4153/CMB-2002-062-3)
- Barge's β-substitution theorem and its accompanying discussion of reducible examples show why the roof hypothesis matters. The five-letter class of Ei and Ito has a separate pair of unit-circle eigenvalues. The plastic-number member gives the concrete counterexample below. [Barge, Theorem 15 and Remark 16](https://arxiv.org/abs/1505.04408) · [Ei and Ito](https://doi.org/10.46298/dmtcs.347)

The formal proof reuses the real vector lift of the existing realization, the proved Pisot contraction on the stable plane, and the existing recognizability theorem. It derives the roof change directly and uses the measured theorem already on main.

## The legal return map and its measure

Write \(X_k\) for the two-sided words over \(\{0,1,2\}\) whose every finite block occurs in some \(\sigma_k^n(a)\), and write \(Sx(i)=x(i+1)\). In the ordinary hull use \(\varphi_t(T)=T-t\). The transversal \(\Xi_k\) consists of tilings with a tile starting at zero, with the tile to the right indexed by zero. Reading all the tiles in order gives a homeomorphism \(\Xi_k\to X_k\) that carries the next-tile return \(R\) to \(S\).

The Lean proof checks both directions of legality. A contiguous patch of a legal tiling occurs in a translated supertile, where its ordered labels give a literal subword. Conversely, every iterated image occurs in a legal tiling by the positive incidence square and the existing supertile occurrence lemmas. Taking larger centred blocks and using the compact transversal gives every legal bi-infinite itinerary. The signed cumulative sums of the tile lengths recover the original anchored tiling.

The geometric normalization in `C4ParameterFamilyTiling.geometry` is
\[
\ell=(\beta,\beta^2,\beta+2),\qquad \beta^3-k\beta^2-2\beta-2=0.
\]
The first return time is \(r(x)=\ell_{x(0)}\). The half-open physical suspension uses the unique coordinates \([x,s]_r\) with \(0\le s<r(x)\).

Let \(\mu_k\) be the unique invariant Borel probability of the primitive symbolic shift and let \(\nu_k\) be the probability in PR #650. The right PF vector \(u\) from the realization satisfies \(\ell u=1\). The letter frequencies are \(u/(\mathbf 1u)\), giving
\[
c=\int r\,d\mu_k=\frac{1}{\mathbf 1u}
=\frac{\beta^4+2\beta^2+4\beta}{\beta^2+2\beta+2}.
\]
In physical coordinates the measure \(\nu_k\) is
\[
c^{-1}\mathbf 1_{0\le s<r(x)}\,d\mu_k(x)\,ds.
\]
For a Borel set in the base, flow invariance inside a strip shorter than the minimum roof makes the vertical measure a constant multiple of Lebesgue measure. The same calculation on each roof cylinder extends the product to the full physical strip. Translating a sufficiently short strip across the top shows that the transverse measure is shift-invariant. Primitivity identifies the normalized transverse measure with \(\mu_k\), and mass one supplies \(1/c\). Consequently, the physical projection onto the tile containing the origin has the length-weighted law \(r\,\mu_k/c\).

## Changing the return times

The incidence columns count the symbols of the literal images:
\[
M=\begin{pmatrix}0&1&2\\1&k&1\\0&1&0\end{pmatrix}.
\]
The square is positive for \(k\ge 1\), the determinant is \(2\), and the irreducible characteristic polynomial is \(X^3-kX^2-2X-2\). The existing `ParameterFamilyPisot` and `ParameterFamilySolenoid` results bind these facts and the stable contraction to the exact matrix. The actual geometric action is aperiodic, and a symbolic period would give a nonzero real period by summing its positive tile lengths. The existing recognizability proof gives the continuous vector lift in the anchored topology.

The row \(d=\ell-c\mathbf 1\) annihilates \(u\). For a column \(v\), write \(v=(\ell v)u+\Pi(v)\) with \(\ell\Pi(v)=0\). Then \(dM^nv=dM^n\Pi(v)\to0\) exponentially. This is the exact Clark–Sadun hypothesis. Sirvent–Solomyak's length condition is also satisfied since the displayed lengths belong to \(\mathbb Z[\beta]\) and are rationally independent.

Lean derives a continuous change of time using the existing real lift \(V\). For an anchor \(B\) with origin label \(a\), the torus translation law gives
\[
V(RB)-V(B)-r(B)u\in\mathbb Z^3.
\]
Both lifts pair to zero with \(\ell\), so the vector on the left has length pairing \(-\ell_a\). An integral vector \(v\) with \(\ell v=0\) has integral incidence iterates converging to zero by the existing stable contraction. Thus \(M^nv=0\) eventually, and \(\det M=2\) gives \(v=0\). It follows that the integral difference is exactly \(-e_a\). Defining \(h(B)=c\,\mathbf 1V(B)\) yields
\[
r(B)=c+h(RB)-h(B).
\]
This geometry and roof argument holds for \(k\ge1\).

The map \([B,s]_r\mapsto[B,s+h(B)]_c\) commutes with real translation and respects the top identification by the coboundary equation. Subtracting \(h(B)\) gives the inverse. In the original hull the corrected section is \(B\mapsto\varphi_{-h(B)}B\). Its next return is exactly \(c\). The half-open corrected strip \(0\le s<c\) carries the measure \(d\mu_k\,ds/c\) by the same vertical-translation argument. The time-\(c\) map takes \((B,s)\) to \((RB,s)\). The factor to the base therefore has the transverse law \(\mu_k\). Lean defines the base probability by pushforward from the specified \(\nu_k\) and checks invariance of that probability. At the original PR #653 head, the product description and canonical identification were written arguments. The [23 November follow-up](c4-family-canonical-measure-2026-11-23.md) now proves the normalized corrected constant-strip lift, recovery of its base marginal and uniqueness of the invariant word probability. The physical variable-roof disintegration formula remains a separate written statement.

## Spectral conclusion

**Theorem (Lean endpoint).** For every \(k\ge2\), the literal left shift \(S\) on \((X_k,\widehat\mu_k)\), where \(\widehat\mu_k\) is `C4FamilySymbolicSpectrum.wordMeasure k hk hk₂`, has pure discrete complex \(L^2\) spectrum. The closed complex span of its nonzero Koopman eigenvectors is the entire \(L^2\) space. Lean constructs this probability by pushing the specified hull probability through the corrected-strip projection and the itinerary conjugacy, and proves its shift invariance.

**Status:** repository-proved for the induced invariant probability defined by Lean; independent human review pending. This original endpoint is unchanged. The [canonical-measure follow-up](c4-family-canonical-measure-2026-11-23.md) adds a separate equality theorem for every independently supplied invariant Borel probability and explicit spectral transport through that equality, at the same `k >= 2` scope.

The original canonical-measure identification is a written consequence of primitive-substitution unique ergodicity: the positive incidence square gives primitivity, so the invariant Borel probability on the literal legal shift is unique. The standard result follows from uniform word frequencies; see [Durand, Corollaries 12 and 22](https://cantorsalta2015.sciencesconf.org/conference/cantorsalta2015/Durand.pdf), applied to the prolongable square and its bilateral extension. The new Lean proof uses a shorter family-specific route through the existing dense solenoid flow, Haar-conull singleton fibres and constant corrected suspension. It proves `C4FamilySymbolicMeasureUniqueness.invariant_probability_eq_wordMeasure` and `C4FamilyCanonicalSpectrum.existsUnique_invariant_probability`. No separately defined canonical measure is silently identified with the induced measure: an arbitrary candidate's probability and invariance proofs are explicit inputs. The physical-strip Lebesgue disintegration is a separate written statement and is not needed for this equality.

The real-flow theorem gives a dense span of joint eigenvectors and hence a dense span for the time-\(c\) map. The corrected base projection is a measure-preserving factor from that map onto \(R\). Its \(L^2\) pullback \(J\) is an isometry, and the adjoint \(J^*\) is onto because \(J^*J=1\). For Koopman operators \(U,W\), the identity \(UJ=JW\) and unitarity of \(W\) give \(J^*U=WJ^*\). The nonzero projections of the eigenvectors therefore have dense span in the target. The itinerary conjugacy takes the result to the left shift of the literal words. A continuous flow eigenfunction \(F\) of frequency \(\xi\) gives \(e^{-2\pi i\xi h(B)}F(B)\) on the corrected section, with eigenvalue \(e^{2\pi i c\xi}\) for the forward shift.

| Lean endpoint | Checked conclusion |
| --- | --- |
| `C4FamilySymbolicSection.no_boundary_before_roof` | A positive time shorter than the physical roof hits no boundary. |
| `C4FamilySymbolicSection.roof_eq_mean_add_coboundary` | The exact continuous roof change for \(k\ge1\). |
| `C4FamilySymbolicLanguage.itineraryHomeomorph_next` | A conjugacy from the transversal to the left shift on legal bi-infinite words. |
| `C4FamilySymbolicSpectrum.symbolicFactor_translate` | The corrected-strip projection intertwines time \(c\) and the actual next-tile return. |
| `C4FamilySymbolicSpectrum.measurePreserving_wordShift` | Shift invariance of the word probability induced from the specified hull probability. |
| `C4FamilySymbolicSpectrum.pureDiscrete_shift` | Pure discrete complex \(L^2\) spectrum for the actual two-sided word shift with the induced `wordMeasure`, for \(k\ge2\). |
| `C4FamilySymbolicMeasureUniqueness.invariant_probability_eq_wordMeasure` | Every invariant Borel probability on that same actual legal shift equals `wordMeasure`, for \(k\ge2\). |
| `C4FamilyCanonicalSpectrum.pureDiscrete_shift_of_measure_eq` | Explicit transport of the unchanged complex \(L^2\) endpoint through a supplied measure equality. |

## A concrete variable-roof counterexample

Let \(\gamma>1\) solve \(X^3-X-1=0\). Its greedy expansion of one is \(10001\), since \(\gamma-1=\gamma^{-4}\). The literal \(\gamma\)-substitution is \(\tau=(12,3,4,5,1)\) on \(1,\ldots,5\), with PF roof \((1,\gamma^{-4},\gamma^{-3},\gamma^{-2},\gamma^{-1})\). Its PF suspension has pure discrete spectrum by Barge's β-substitution theorem. Its symbolic shift is weakly mixing. The incidence is primitive by the directed cycle and the self-loop at \(1\). Irrationality of \(\gamma\) rules out periodicity by the frequency eigenvector equation. [Barge, Theorem 15](https://arxiv.org/abs/1505.04408) · [Host's eigenvalue theorem](https://doi.org/10.1017/S0143385700003679) · [Modern statement of the return-word criterion](https://doi.org/10.1112/jlms.70136)

The block \(11\) occurs in \(\tau^6(1)=12345112\), so \(1\) is a return word. For a symbolic eigenvalue \(e^{2\pi i\theta}\), Host's criterion gives \(\operatorname{dist}(\theta L_n,\mathbb Z)\to0\) for \(L_n=|\tau^n(1)|\). These lengths satisfy the recurrence with polynomial
\[
q(X)=X^5-X^4-1=(X^2-X+1)(X^3-X-1).
\]
Take nearest integers \(a_n\) to \(\theta L_n\). The integer recurrence defect \(q(E)a\), where \(E\) advances the index, tends to zero and eventually vanishes. The constant coefficient \(-1\) extends the integer solution backwards. The error \(\theta L-a\) now satisfies the recurrence and tends to zero. Its growing mode and period-six modes vanish, so \((E^3-E-1)(\theta L-a)=0\). At index zero this gives \(\theta(L_3-L_1-L_0)\in\mathbb Z\), and \(L_3-L_1-L_0=4-2-1=1\). Thus \(1\) is the only eigenvalue. This example shows the need for a roof hypothesis in the variable-roof transfer.

## Review scope and replay

The source base is PR [#650](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/650), head `686c266f09016d0475e128cb395d6a1bccf566b3`, merge `968fabde6c1c056d5157abc77460a5a4e2a4cfd1`, common tree `ef2b553236641ab94b608520af667c99f96b5e92`. The accepted [family workflow](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/44999791541) succeeded on that head. The symbolic result uses exactly the \(k\ge2\) range of the measured theorem. The universal PSC and separate BH, A1′ and C4 statements lie outside the family endpoint.

The original symbolic audit builds the three symbolic modules and checks their exact endpoint types and recursive axiom closures. Its controls reject the opposite coboundary endpoint type, reject the real-flow theorem as a word-shift endpoint, and prove an actual nonreturn at physical time one. The extended family gate also builds the three canonical-measure modules and runs a separate eight-endpoint uniqueness/measure-transport audit with 22 controls. The original symbolic audit and its historical receipts keep their original scope. The toolchain is Lean 4.34.0-rc2 and Mathlib `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`.

The [hosted family run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/45050059808) succeeded at published head `0762cce18ef708d3bbb0dc56f31f0ae4f0aaf972`, tree `c7de51d5bce56a14dd326539579ece0ea18764cb`. Its [Lean artifact](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/45050059808/artifacts/14769670179) records the checked source identity, 84 built project modules and eleven audit fixtures. The symbolic audit enforces seven independent endpoint contracts, three controls and recursive axiom checks for 198 declarations, including 125 theorem constants; its permitted axiom closure is `propext`, `Classical.choice` and `Quot.sound`. The artifact ZIP digest is `9d28f1174992db19d53ade71ec343fb6d558f7eefcce92f7e3db9efe9ab25015`. This is exact-head family acceptance; repository-wide workflow failures require separate classification and do not become passing checks through this receipt.

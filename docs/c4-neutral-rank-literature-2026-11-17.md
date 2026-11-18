# Corrected neutral-rank obstruction: targeted literature stop/go

**Status:** Targeted literature review and narrowed research decision; no
universal theorem or claim promotion.

**Decision: proceed with a narrowed target.** Investigate a conditional
neutral-rank budget for a realized literal strict component. Stop both the
geometry-only claim that every seam correction is nonpositive and the
substitution of an ambient free-Lie dimension for the actual defect-image
rank. Universal C4 and PSC remain open. No governed claim status changes.

This gate follows the three-source primary-literature review below and
precedes the new theorem-facing controls for this investigation. The local
integration base is `1cf7a6ccac6b20957e153cd8e7f6fd09bb594368`: the literal
constructor of PR #602 at `cbb8c6c64b56bcce60c2e6031da7acb9ffc5b41d`, with
the alphabet-scope correction of merged PR #603. The inherited correction
formula is from merged PR #601. This integration is local review work, not
a published branch or a merged result.

## Proposed claim and experiment

Let `C` be a realized literal aligned nonproductive sink in the normalized
unit PIP3, coincidence-rank-two setting of
[the overlap-return note](c4-periodic-overlap-returns-2026-11-17.md). Let
`N` be the associated strict bigon occurrence matrix and `A_C` the literal
overlap occurrence matrix, with their track-swap odd sectors. For a first
nonzero neutral defect of degree `3m`, set `epsilon = (det M)^m` and
`r = rank D_(3m)`.

The proposed obstruction is the incompatibility of `r` with the corrected
odd multiplicity:

\[
r\le \dim\ker((N^-)^\mathsf{T}-\varepsilon I)
\le m_\varepsilon(N^-)
=m_\varepsilon(A_C^-)+b_\varepsilon.
\]

Here `b_(+1) = b_1` and `b_(-1) = b_2`, as defined by
[the seam-spectrum note](c4-one-track-seam-spectrum-2026-11-17.md).
The first inequality uses the actual intertwiner
`D_(3m) N^- = epsilon D_(3m)`. The last equality retains the written
literal-realization and trace-transfer hypotheses of #598--601. Trace
identities determine algebraic multiplicities; they do not identify
geometric multiplicities or Jordan blocks.

Seek an exact upper bound on the right-hand side, a literal lower bound
on `r`, or a counterexample to an intermediate inequality. Repeating the
48 productive specimen/power comparisons in #602 would not resolve this
obligation and is not the proposed experiment.

## Primary sources inspected

The sources were opened and the stated passages read for this review;
the table does not claim a complete rereading of every cited paper.

| Source | Passage and transferable content | Boundary |
| --- | --- | --- |
| [Barge--Diamond, *Cohomology in one-dimensional substitution tiling spaces*](https://arxiv.org/pdf/math/0702669), Proc. Amer. Math. Soc. 136 (2008), 2183--2191 | Section 3, Theorems 4 and 4-prime, and their exact-sequence argument. The legal transition graph carries last/first-letter dynamics; its eventual range contributes first homology and component coboundaries to the cohomology calculation. | Applies to primitive aperiodic substitutions. It does not make the eventual range a forest, force a sign on every seam correction, or realize an overlap graph as a strict bigon system. |
| [Barge, *Factors of Pisot tiling spaces and the Coincidence Rank Conjecture*](https://arxiv.org/pdf/1301.7094), Bull. Soc. Math. France 143 (2015) | Section 4, Lemmas 20--21, Theorem 22, and Corollaries 23--25 in the arXiv numbering. Coincidence rank two and odd norm imply first-cohomology dimension at least `2d-1`. The proof uses a swap-equivariant ordered-pair substitution and eventual rank. | This is a total cohomological lower bound, not a neutral-eigenvalue upper bound. Its proper rewritten pair system is obtained after quotienting; it is not automatically the literal strict bigon matrix `N`. |
| [Baker--Barge--Kwapisz, *Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces with an application to beta-shifts*](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf), Ann. Inst. Fourier 56 (2006), 2213--2248 | Section 4, Definition 4.1 and Remark 4.3; Section 5, Corollary 5.2 and Example 5.3. Coincidence rank is realized by a maximal pairwise noncoincident family of geometric states over a common fibre. | The projected return module must be retained. Integral offsets and full-rank identifications valid for irreducible PIP3 cannot silently be transferred to reducible controls. Example 5.3 has Pisot-unit dilation without pure discrete spectrum. |

The finite-graph identity `edges - vertices = H_1 - H_0`, equivariantly,
is elementary homological bookkeeping. Its use here is a specialization
of the established eventual-range framework, not a new general trace
theorem. No inspected source supplies the uniform per-neutral-eigenvalue
exclusion sought here.

## Hypotheses that transfer, and those still needed

The standing primitive irreducible Pisot setting supplies aperiodicity,
finite local complexity and the rational independence used to recover
integral starts from physical displacement. The normalized unit
rank-two setting and the repository's prior realization arguments supply
the particular joining and candidate component to which #598--601 apply.

The bounded literal constructor supplies endpoint and seam identities,
source ordinals, prefix equations and integral offsets on its declared
inputs. It does not supply coincidence rank two, a strict component,
literal common-cut coding, arbitrary-degree first-defect transport, or
a positive lower bound larger than one on the actual defect rank.

For the minus-one period corollary, use #603 exactly: odd interior-state
periods and odd cycles in both endpoint maps imply zero correction at
minus one. On three letters, absence of a two-cycle suffices to make
endpoint cycles odd. That simplification is false as an unrestricted
alphabet statement.

## Established source filter for rank-two candidates

Write `E = ER(sigma)`. The repository's irreducible PIP3 argument makes
`E` connected: a nontrivial eventual component coboundary would give the
incidence matrix a root-of-unity eigenvalue. Barge--Diamond then gives

\[
\dim H^1(\Omega_\sigma;\mathbb Q)=3+\beta_1(E).
\]

At unit coincidence rank two, Barge's odd-norm theorem therefore implies

\[
\boxed{\beta_1(E)\ge2.}
\]

This is a consequence of established literature and the existing
irreducibility argument, not a new exclusion theorem. It concerns the
source system and does not identify the spectrum of `N`.

The existing seam record describes the source eventual range of
`01/12/021` as a square, of cycle rank one. That source is consequently
excluded from coincidence rank two by the cohomological filter, while
its positive correction still refutes a sign bound based on literal
geometry alone. The existing
[round-three note, Section 5.4](c4-round3-2026-11-16.md) records source
cohomology dimension five for `1/2/021`, so that control survives this
source-only filter. These are deductions from the cited records; this
literature gate itself reports no fresh executable graph calculation.

## Negative controls and retired shortcuts

- `01/12/021` has correction `+1` at minus one. It is productive, not a
  strict-system example. Preserve it against geometry-only nonpositivity;
  do not describe it as a counterexample to a bound assuming an actual
  strict rank-two component.
- The [round-three note, Sections 5.3--5.4](c4-round3-2026-11-16.md)
  distinguishes the two-dimensional ambient space `Q[M]_0` from the
  image of the defect map. Its abstract neutral model has rank-one
  `D_3`, with `Theta(K_0) = 3M-I`. It has no literal factorization
  realization. A rank-two lower bound needs additional literal input.
- Reducible strict controls calibrate exact word and graph calculations.
  They cannot establish a PIP3 counterexample when rational independence,
  irreducibility or the full return-lattice identification fails.
- A seam-graph embedding bounds its first-homology multiplicity by that
  of the ambient permuted copies of the source eventual range. The
  interior-state permutation and the subtracted `H_0` term must remain
  in the bound; ignoring either can erase the required eigenvalue data.

## Stop/go outcome and non-claims

Proceed with conditional rank statements, exact literal controls and
explicit countermodels to intermediate inequalities. Record independently
which hypotheses come from word replay, which come from graph closure,
which come from the written joining/trace arguments, and which remain
unproved. Any stronger rank lower bound or geometric-multiplicity
transfer requires its own proof.

This review supplies neither a strict PIP3 candidate nor a uniform
exclusion. It does not rerun the existing 48 literal comparisons, prove
property (F) from finitely many powers, identify the proper rewritten
pair substitution with literal `N`, or close C4 or PSC.

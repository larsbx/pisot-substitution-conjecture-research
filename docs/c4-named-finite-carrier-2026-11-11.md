# Finite ancestor carriers for the named actual prefix tiles

Date: 2026-11-11.

This increment connects the actual named prefix systems of #545 with the finite geometric carrier of #544. The [pre-code literature gate](c4-named-finite-carrier-literature-2026-11-11.md) records the primary sources and scope boundaries. The published branch preserves both prerequisite histories, including #542 and #543 through #545. A fresh complete-source audit of the combined revision is required; a prerequisite receipt does not certify this increment.

## Mathematical object and quantifiers

The fixture index `f : Fin 2` selects the literal substitution

| Fixture | Images of `0`, `1`, `2` | Actual word |
| --- | --- | --- |
| 0 | `1 / 021 / 001` | The period-two seed limit starting in `0`; its first three letters are `021`. |
| 1 | `1 / 012 / 001` | Its own period-two seed limit starting in `0`; its first three letters are `012`. |

Their common column incidence is

\[
M=\begin{pmatrix}0&1&2\\1&1&1\\0&1&0\end{pmatrix},\qquad \det M=2.
\]

The ambient group for fixture `f` is the original
\(G_f=\mathbb R^2\times H_M\), using the concrete integer matrix-adic inverse limit. Its integral map is
\(\operatorname{star}_f(z)=(Wz,\iota_M(z))\), and its one-step action is
\(T_f=B\times T_M\). The actual sets \(K_f(a)\) are closures of all projected prefixes of that fixture's infinite word immediately before letter `a`.

The new conclusion is uniform over every packet in a single fixture-dependent finite domain, every even substitution power `2*r`, and every finite inverse depth `n`. It is not a bounded sample of prefix positions or a chosen list of ancestor roots. All incoming edges retain both literal marks.

The existing real root \(\beta>2\) solves
\(\beta^3-\beta^2-2\beta-2=0\). The chart constants are

\[
a=\frac{3\beta-\beta^2}{2},\quad
b=\frac{\beta^2-\beta-2}{2},\quad
c=\beta^2-\beta-1,\quad
\kappa=4\beta-\beta^2>0.
\]

The physical row is \(\ell=(1,\beta,c)\), and the two stable coordinates are
\(Wz=(z_0-a z_1,z_2-b z_1)\). The prior named-chart proof authenticates this construction, including commutation and reconstruction; none of these are supplied numerical inputs to the new named theorem.

## 1. Extend the actual prefix bound to every closed-tile point

The named compactness proof already gives

\[
\|W\operatorname{Parikh}(w_f[0,n))\|_\infty\le R_f
\quad\text{for every }n,\qquad R_f=8D_f.
\]

Here \(D_f\) is the canonical finite sum of the norms of **all** literal block-twelve prefix digits. Its definition preserves repeated occurrences. The estimate comes from the proved block-twelve contraction factor \(7/8\); it uses no unproved numerical bound on \(D_f\).

The inverse image under the continuous first projection of the closed ball of radius \(R_f\) is closed. Every generating prefix lies in that set, so its closure does too. Consequently, for every letter `a`, every point \(x\in K_f(a)\), and each of the two coordinate projections,

\[
|x_i|\le R_f.
\]

This is the all-point enclosure required by `GeometricPacketCarrier.ChartEnclosure`. Compactness by itself was not substituted for a numerical or coordinate bound.

## 2. Recover integer coordinates from the faithful full chart

Write \(h=\ell\cdot z\), \(u=z_0-a z_1\), and \(v=z_2-b z_1\). The existing full reconstruction gives

\[
z_1=\frac{h-u-cv}{\kappa},\qquad
z_0=u+a z_1,\qquad z_2=v+b z_1.
\]

Thus the inverse coefficient matrix for the ordered coordinates `(h,u,v)` is

\[
U=\begin{pmatrix}
a/\kappa&1-a/\kappa&-ac/\kappa\\
1/\kappa&-1/\kappa&-c/\kappa\\
b/\kappa&-b/\kappa&1-bc/\kappa
\end{pmatrix}.
\]

The denominator is justified by the proved positivity of \(\kappa\). All physical lengths are positive. The convenient common physical bound is \(H=1+\beta+c\); sharp optimization is unnecessary for finiteness.

For a packet \(p=(i,j,z)\), let
\(O_f(p)=K_f(i)\cap(\operatorname{star}_f(z)+K_f(j))\), using the repository's top-minus-bottom sign convention. An actual point of this intersection bounds the stable displacement coordinates by \(2R_f\). The strict physical-interior predicate separately bounds \(|h|\) by \(H\). Therefore

\[
|z_j|\le C_{f,j}:=|U_{j0}|H+2|U_{j1}|R_f+2|U_{j2}|R_f.
\]

The full chart is essential: two stable coordinates alone do not bound an integer direction that they fail to detect.

## 3. Construct the finite domain once

Choose natural bounds \(N_{f,j}\ge C_{f,j}\) by the existing Archimedean theorem. Let

\[
S_f=\{(i,j,z): |z_t|\le N_{f,t}\text{ for all }t,
\ p\text{ is physically interior}\}.
\]

The integer inequalities are inclusive. The domain contains every physically interior packet with a nonempty actual overlap, and

\[
|S_f|\le9\prod_{t=0}^2(2N_{f,t}+1).
\]

The same domain works at every inverse depth and every block scale used below. Its natural bounds may be conservative. They are chosen mathematical bounds, not an authenticated serialized list or a claim that the existing native radius-forty packet has exactly this vertex set.

## 4. Derive incoming completeness from actual scaling

The one-step literal image lengths satisfy
\(\operatorname{length}_\ell(\sigma_f(a))=\beta\ell_a\). List substitution and iteration therefore give, for every natural `k`,

\[
\operatorname{length}_\ell(\sigma_f^k(a))=\beta^k\ell_a.
\]

The inverse-occurrence theorem uses this exact positive scale to pull physical interior backwards. If a represented source has an actual incoming ancestor whose overlap is nonempty, that ancestor is physically interior and satisfies the same reconstructed integer bounds. It therefore lies in \(S_f\).

This derives the representation premise that the earlier finite-history theorem had to accept as an input. An incoming ancestor omitted by \(S_f\) has empty actual overlap. Nothing here asserts that every algebraic incoming ancestor is in the box, or that an inverse-complete domain is forward closed.

One can further restrict to
\(S_f^{\mathrm{nd}}=\{p\in S_f:p\text{ is not an integral diagonal}\}\).
The accepted diagonal-parent implication shows that an interior nondiagonal source has a nondiagonal incoming ancestor. Thus this additional filter preserves incoming completeness for the restricted sources. It is a statement about literal inverse occurrences, not a claim that the resulting finite domain realizes every strict balanced-pair source.

## 5. Obtain complete finite covers at each even power

The actual word is fixed by \(\sigma_f^2\). The fixed-prefix power theorem gives fixedness by every \(\sigma_f^{2r}\). The original ambient action has a proved closed embedding; its corresponding power is still an injective closed embedding. Exact block commutation and level-`2*r` residue reflection hold in the original \(H_M\).

Those facts derive the complete tile equation for the same sets \(K_f(a)\) with action \(T_f^{2r}\). Applying the finite-carrier cover theorem yields

\[
O_f(p)=\bigcup_{\substack{h\text{ literal inverse history}\\
\text{of depth }n\text{ within }S_f}}\operatorname{Piece}_f(h)
\quad(p\in S_f).
\]

The index is finite at every finite `n`. Every piece is the exact iterated affine image of the terminal actual overlap, with the accumulated literal prefix translation. Histories with equal endpoints remain distinct indices. The analogous equality holds in the nondiagonal domain for its admitted sources.

The power used for the word equation and the power of the affine action are identical. The useful contraction power remains twelve; no block-two contraction is inferred. The period-two result is not relabelled as a one-step fixed-word result.

## Controls and remaining obligations

The proof source includes controls for actual nonempty diagonal overlaps, the strict physical boundary, and incorrect block scaling. Existing controls remain applicable: missing chart reconstruction, a too-small box, lost residue reflection, unrepresented singular lifts, boundary-only nonempty intersections, and the inverse-closed but forward-leaking `00/11/22` example.

This connection supplies a finite mathematical domain and exact set covers for the two named actual prefix systems. It does not supply:

- a certified executable rounding or enumeration procedure for these chosen real bounds;
- the sharper numerical radius forty or authentication of an archived finite graph;
- an identification of the original matrix-adic product with a number-field representation and its Haar measure;
- measure-disjoint overlap pieces, a Haar scaling/recurrence theorem, or positivity of a strict source overlap;
- a productive coincidence, a uniform construction for arbitrary PIP substitutions, or closure of C4, G1 or PSC.

The immediate consumer is the compact overlap and inverse graph program: geometry now supplies the previously conditional finite-domain representation premise for these named instances. Turning the exact set cover into the required measure or loss conclusion is a further mathematical obligation.

The first useful measure target is affine Haar image scaling on this same product. The real stable determinant is already `2 / beta`; the compact matrix-adic factor still needs its full action-range/index theorem and normalized Haar scaling by `1 / 2`. Their authenticated product would give scale `beta^(-k)` for actual affine pieces. `OverlapContraction.recurrence_of_cover` could then derive the subinvariant inequality by subadditivity: disjointness is not needed for that inequality. An additive equality would need further measure disjointness, while a null-overlap comparison still needs a rate-gap or actual loss certificate on these same literal counts. A contradiction from strict sources separately needs positive overlap measure or a positive cut set covered by the strict roots.

## Replay and acceptance

The new source contributes 40 named proofs: nine in `NamedGeometricEnclosure` and 31 in `NamedFiniteCarrier`. The combined generated inventory has 2,425 named proofs, 126 governed claims and 404 source openings.

| Interface | Named declaration |
| --- | --- |
| Actual closed-tile enclosure and faithful reconstruction | `NamedGeometricEnclosure.chart` |
| Literal physical scaling at every power | `NamedGeometricEnclosure.physicalLength_iterateImages` |
| Complete full and nondiagonal finite domains | `NamedFiniteCarrier.packets`, `NamedFiniteCarrier.strictPackets` |
| All-depth nonempty ancestry finiteness | `finite_nonempty_ancestry`, `finite_strict_nonempty_ancestry` |
| Complete lifting of nonempty literal pairs | `representedAt_packets`, `representedAt_strictPackets` |
| Actual tile equation at every even exponent | `tileEquation_even` |
| Exact finite compact covers at every finite depth | `finite_compact_history_cover`, `strict_finite_compact_history_cover` |

```bash
python3 tools/make_proof_bank.py --check
./tools/verify_all.sh provenance
python3 -m pytest -q tests/test_proof_bank.py tests/test_markdown_links.py tests/test_check_markdown_source.py
./tools/check_lean.sh
```

`check_lean.sh` must build the complete production import in a fresh isolated source workspace with pinned dependencies, audit every compiled local declaration, and reconcile every named source proof with the generated inventory. Local cache probes are development evidence only. The implementation PR records the exact published head, matching source tree, final hosted jobs and audit counts after they complete; pending or failed revisions remain distinct historical records. All governed claim statuses are unchanged. Independent human review remains separate validation debt.

Development history: the initial short chart-import probe timed out without diagnostics. A subsequent single-worker exact-body probe completed and rejected the inverse reconstruction's final simplification: reassociation combined `J` and `W` before the explicit section formula could apply. Generalizing the stable coordinate vector before that calculation repaired the proof without changing its statement. The repaired exact physical-bound and inverse-chart bodies compiled against the genuine pinned named chart with exit zero; this narrow result does not certify the full new modules or combined bank.

# Geometric property (F), coincidence rank and the C4 class theorems: targeted stop/go — 2026-11-16

**Status:** targeted literature stop/go note (`AGENTS.md`, review gate) for
the class theorems of
[`c4-geometric-f-class-2026-11-16.md`](c4-geometric-f-class-2026-11-16.md).
**Decision: proceed with a narrowed, class-restricted target.** Universal C4
remains open; nothing here changes a governed claim status (C4, #138, #139,
#84, G1 and PSC are unchanged); independent human review pending.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

## Timing, stated plainly

The sources below were read on 2026-11-15 and 2026-11-16, in the course of
six proof attempts on universal C4, before any repository code or proof text
of this increment was written. The text of this note was written on
2026-11-16, after that reading and together with the proof note; statement
numbers were re-checked against the downloaded texts while writing. So the
order "sources first, then proof text and kernel code" was kept, but the gate
is recorded at the end of the attempts, not before them. None of the six
attempts proved universal C4
([closure-attempt record](c4-closure-attempt-2026-11-16.md)).

## Proposed claims

Standing class **PIP3**: a primitive substitution `σ` on `{0,1,2}` whose
incidence matrix `M` has an irreducible characteristic polynomial with a
Pisot Perron root `β`; `|det M| = 1` is not assumed. `ℓ` is the positive left
Perron vector, `p(·)` the Parikh vector, `g` and `g_R` the first- and
last-letter maps, `ν_L` (`ν_R`) the maximal number of letters no two of which
are left (right) strongly coincident.

*State map.* A state is `(j, v)` with `j` a letter, `v ∈ ℤ³` and
`0 ≤ ℓ·v < ℓ_j`; `f(j, v) = (j′, Mv − p(P))`, where `σ(j) = P j′ S` is the
factorisation with `ℓ·p(P) ≤ ℓ·Mv < ℓ·p(P) + ℓ_{j′}`. **(F)**: no
`f`-periodic state has `v ≠ 0`.

The claims proposed for a written proof and an exact corpus replay:

1. **Theorem FC1.** For `σ ∈ PIP3` with (F), `τ = σ^m` and `τ`-fixed rays
   `X_c, X_c′` (`c ≠ c′` fixed by `g^m`) with vertex sets `V_c, V_c′`: there is
   `N` with `M^{mN}(V_c ∪ V_c′) ⊆ V_c ∩ V_c′`, so equal-Parikh cuts have gaps
   at most `β^{mN} ℓ_max`; hence `σ` has a strict system iff some pair of
   distinct `g`-periodic letters is not left strongly coincident. No
   literature import.
2. **Theorem FC2.** For `σ ∈ PIP3`: `cr(σ) ≥ max(ν_L, ν_R)` and
   `ν_L, ν_R ≤ 2`; under (F), `cr(σ) = ν_L = ν_R ≤ 2`. Consequently, on the
   (F) class, "no strict system", all-pairs strong coincidence, `cr = 1` and
   pure discrete spectrum are equivalent.
3. **Theorem P.** For `σ ∈ PIP3` with `det M` odd, `cr(σ) = 2` forces
   `tr M ≡ e_2(M) (mod 2)` and `dim H¹(Ω_σ; ℚ) ≥ 5`.
4. **Theorem FC3.** For `σ ∈ PIP3` with (F) and one of (a) `ν_L = 1` or
   `ν_R = 1`, (b) `det M` odd and `dim H¹ ≤ 4`, (c) `det M` odd and
   `tr M ≢ e_2(M) (mod 2)`: `cr(σ) = 1`, hence pure discrete spectrum, strong
   coincidence of all pairs on both sides, and no strict system.
5. **Theorem N.** A strict system for `σ ∈ PIP3` forces `cr ≥ 2`; with
   `det M` odd and (`dim H¹ ≤ 4` or `tr M ≢ e_2(M)`) it forces `cr ≥ 3` and
   the failure of (F).
6. **Theorem Fork.** For unit `σ ∈ PIP3` with `dim H¹ = 3` and a strict
   component `Z ⊆ Ω_σ × Ω_σ`: every `(T, T′) ∈ Z` has a second partner `T″`,
   `(T, T″) ∈ Z`, with `Φⁿ(T′)` and `Φⁿ(T″)` tile-disjoint for all `n`.

Exact statements, hypotheses and proofs are in the proof note. The planned
executable part is the exact decision of (F), the relative states of
Theorem FC1 and the class counts of Theorems P and FC3 over the 4,554-member
corpus (`kernel/psc/c4_geometric_f.mojo`).

## Prior art and field terminology

- **Geometric property (F).** Minervino–Thuswaldner Def. 9.3 defines it for
  irreducible Pisot substitutions, unit or not, and Prop. 9.4 restates it as:
  every point of the self-replicating translation set has a finite
  `(σ, b)`-expansion, i.e. the orbit of every admissible point under their map
  `T_σ: (y, b) ↦ (αy − δ(p), a)` reaches `0`. `T_σ` is the state map `f` above
  read on positions, and their admissible points become lattice states after
  finitely many steps, so (F) above is their property (proof note, Lemma 5).
  Their text attributes the finiteness property to the beta-numeration
  literature and the exclusive-inner-point formulation to Akiyama; those
  sources were not read here. In the repository the same class is the
  hypothesis "no terminal leftmost cycle" of Corollary LC5
  ([leftmost-chain note](p1b-leftmost-chain-periodic-pair-2026-10-05.md)),
  whose own gate cites Siegel–Thuswaldner's zero-expansion graph for unit
  substitutions.
- **Coincidence rank.** Three definitions are in use and agree for Pisot
  substitutions: Baker–Barge–Kwapisz Def. 4.1 (maximal number of pairwise
  non-coincident strands over one point of `V/Σ`), Barge–Kellendonk Def. 2.9
  (a limit of separated fibre families) and Barge 2015 §2 (minimal fibre
  cardinality of the maximal equicontinuous factor map). Barge 2015 §2 states
  the agreement; Baker–Barge–Kwapisz Thm 4.2 gives it for their definition.
- **Strong coincidence.** Barge–Diamond 2002 use the prefix form (equal
  abelianised prefixes followed by the same letter). Minervino–Thuswaldner
  Def. 2.1 asks, per pair, for the prefix form *or* the suffix form. The
  repository keeps left (prefix) and right (suffix) strong coincidence
  separate; Theorem FC2 shows that on (F) the two maximal non-coincident
  families have the same size.
- **Zero fibre, exclusive inner point.** The fibre of the geometric
  realization over the origin consists of the inflation-periodic strands with
  integer vertices; a member whose origin is inside a tile is the same datum
  as an `f`-periodic state with `v ≠ 0`. In the language of
  Minervino–Thuswaldner (Def. 9.6, Prop. 9.7, proof of Lemma 9.8) such a
  state is a loop through a nonzero node of the zero-expansion graph. Their
  Lemma 9.8 phrases (F) as "0 is an exclusive inner point of the central
  tile", under the strong coincidence condition.
- **Eventual range complex.** Barge–Diamond 2008: the subcomplex `S` of
  transition edges `e_{ab}` (`ab` legal), the map `g(e_{ab}) = e_{cd}` with
  `c` the last letter of `φ(a)` and `d` the first letter of `φ(b)`, its
  eventual range `ER`, the number `k` of components and the asymptotic-cycle
  rank `l`. The repository's census
  ([`dim H¹` note](c4-h1-census-2026-11-05.md)) already uses it.

## Primary sources inspected

| Source | Exact result | Hypotheses and transfer boundary | Read |
| --- | --- | --- | --- |
| Baker–Barge–Kwapisz, *Geometric realization and coincidence for reducible non-unimodular Pisot tiling spaces with an application to β-shifts*, Ann. Inst. Fourier 56 (2006) 2213–2248 | Def. 3.1 (geometric realization `h_φ`); Def. 4.1 (`cr_φ`); Thm 4.2 (`h_φ` uniformly finite-to-one, a.e. `cr_φ`-to-one, minimal fibre cardinality `cr_φ`); Remark 4.3 (for every `q`, `cr_φ` is the largest pairwise non-coincident family of states over `q`); Thm 5.1 (eigenfunctions `χ_u ∘ h_φ`); Cor. 5.2 (pure discrete spectrum iff `cr_φ = 1`); Example 5.3 (six letters, reducible, `λ` a Pisot unit, `cr = 2`) | Standing hypotheses (§2, Def. 2.1): primitive, translation-aperiodic, `λ` a Pisot number; reducible and non-unimodular allowed. All hold on PIP3. Two points do **not** transfer literally: (i) p. 2220, "if `A` is irreducible Pisot then `Σ = Γ` by the argument in [5]" defers to Barge–Kwapisz 2006; (ii) the states of Remark 4.3 exclude the terminal end point of an edge, so the remark yields `cr ≥ ν_L` but not `cr ≥ ν_R` | full text, 2026-11-15; numbers re-checked 2026-11-16 |
| Barge–Diamond, *Coincidence for substitutions of Pisot type*, Bull. Soc. Math. France 130 (2002) 619–626 | Theorem 1: there are distinct letters `i, j` and `k, n` such that `φⁿ(i)`, `φⁿ(j)` have the same `k`-th letter and prefixes of length `k − 1` with equal abelianisation | "Pisot type": every eigenvalue other than the Perron one has modulus strictly between 0 and 1. Holds on PIP3, nonunit included. One pair only, prefix form; the suffix form follows by reversal. Unavailable for the reducible controls with eigenvalue `0`, `1` or `−1` | in full, 2026-11-15 |
| Barge, *Factors of Pisot tiling spaces and the Coincidence Rank Conjecture*, Bull. Soc. Math. France 143 (2015); arXiv:1301.7094 | Thm 4 (1)–(5) (fibres of the maximal equicontinuous factor map `g`); Thm 5; Thm 12 (the quotient `Ω/≈_s` is the tiling space of the stack substitution `Φ_s`, on which `≈_s` is trivial); Lemmas 13–14 (`cr = 2`: unique regionally proximal distal partner, `Σ_op` an isomorphism); Prop. 19 (`Σ*` injective on `H¹`); Lemma 20 (`evrank ≥ 2d` for odd norm, matrix `[[X,Y],[Y,X]]`); exact sequence (4.1) and Lemma 21; Thm 22 (odd norm, `cr = 2 ⇒ dim H¹ ≥ 2d − 1`); Cor. 23–25 | §2: primitive, non-periodic, FLC, Pisot dilation; no irreducibility, no unimodularity. Thm 22 needs odd norm (`det M` odd on PIP3), so nothing transfers to `det M = 2`. Proofs of Thm 4 are deferred there to Barge–Kellendonk and Barge–Olimb. The parity statement of Theorem P is not in the paper; it is derived in the proof note from the printed equivariance | full text, 2026-11-15 (two routes); re-checked 2026-11-16 |
| Barge–Diamond, *Cohomology in one-dimensional substitution tiling spaces*, Proc. Amer. Math. Soc. 136 (2008) 2183–2191; arXiv:math/0702669 | Theorem 4: `Ȟ¹(T_φ) ≅ ℤ^l ⊕ lim Aᵗ / G`, `G ≅ ℤ^{k−1}`; its proof (a power of `g` is homotopic to the identity on `ER`; the generators of `G_0` are fixed by a power of `g*`; the exact sequence `0 → G_0 → G_1 → G_2 → G_3 → 0`) | primitive, aperiodic. Holds on PIP3 | TeX source, 2026-11-15 (cohomology route); re-read 2026-11-16. The zero-fibre route used it through Barge 2015 (4.1) and the repository census |
| Barge–Kellendonk, *Proximality and pure point spectrum for tiling dynamical systems*, arXiv:1108.4065 (Michigan Math. J. 62, 2013) | Def. 2.9, Lemmas 2.10 and 2.14 (coincidence rank equals minimal rank), Thms 5.3–5.4, Cor. 5.8, Lemma 5.12 | Used only for the identification of the coincidence ranks. Statements read, proofs not | statements only, 2026-11-15 |
| Barge, *Pure discrete spectrum for a class of one-dimensional substitution tiling systems*, Discrete Contin. Dyn. Syst. 36 (2016); arXiv:1403.7826 | Thm 3.13: primitive, Pisot inflation, injective on initial letters, constant on final letters ⇒ pure discrete spectrum; Remark 3.14 (eventually constant suffices); Lemma 3.11, Cor. 3.12 | "Constant on final letters" is the repository's right endpoint collapse, where Theorem A(3) already excludes a strict system. Its Lemma 3.11 uses that the fixed disjoint tilings have disjoint vertex sets; on (F) two periodic rays always share vertices (Theorem FC1), so the mechanism does not extend | in full, 2026-11-15; used in no proof |
| Minervino–Thuswaldner, *The geometry of non-unit Pisot substitutions*, Ann. Inst. Fourier 64 (2014); arXiv:1402.2002 | Def. 2.1 (strong coincidence, prefix or suffix); the map `T_σ` of §4.1; Def. 9.3, Prop. 9.4 (geometric property (F)); Def. 9.5–9.6, Prop. 9.7 (exclusive inner point, zero-expansion graph); Lemma 9.8; Thm 9.9 ((F) and strong coincidence ⇒ the self-replicating multiple tiling is a tiling) | irreducible Pisot, unit not required. Identifies (F). Thm 9.9 has strong coincidence as a hypothesis, which is the conclusion wanted here | §§2–4 definitions and §9, 2026-11-15; used in no proof |
| Barge–Bruin–Jones–Sadun, *Homological Pisot substitutions and exact regularity*, Israel J. Math. 188 (2012); arXiv:1001.2027 | homological Pisot substitutions (`dim H¹` equal to the degree); the exact regularity property; examples of every degree with coincidence rank 3 and norm divisible by 3; the Coincidence Rank Conjecture, true in degree one | Calibration and negative control only: with minimal cohomology three pairwise non-coincident tilings can share a fibre when the norm is not `±1`, so unimodularity is a real hypothesis of Theorem Fork | TeX source, 2026-11-15 (cohomology route) |
| Akiyama–Lee, *Overlap coincidence to strong coincidence in substitution tiling dynamics*, European J. Combin. 39 (2014) 233–243 | Cor. 4.5: for an irreducible Pisot substitution with overlap coincidence all letters are prefix-coincident simultaneously | **Not re-read in this increment**; taken from the repository gate [`pds-strong-coincidence-literature-gate-2026-10-04.md`](pds-strong-coincidence-literature-gate-2026-10-04.md). Not needed: "`cr = 1` ⇒ strong coincidence of all pairs, both sides" follows from Remark 4.3 of Baker–Barge–Kwapisz (Theorem FC2(1)) | no |
| Barge–Kwapisz, *Geometric theory of unimodular Pisot substitutions*, Amer. J. Math. 128 (2006) | — | **Could not be obtained. Cited for nothing.** Where Baker–Barge–Kwapisz defer to it (`Σ = Γ`) the proof note gives a direct argument (Lemma 6, which is the repository's Theorem R); where Barge 2015 Thm 4 rests on it through Barge–Kellendonk, the later statement is imported as printed | no |

Repository sources relied on: Theorem A of the
[cut-pair note](c4-cut-pair-productivity-2026-11-04.md) (Lean,
`proof/PscVerif/PscVerif/StrictSystem.lean`); Lemma F and Propositions 2–3 of
the [cut-attractor note](c4-cut-attractor-window-2026-11-05.md); Theorem R of
the [fibre gate](p1b-periodic-pair-fibre-literature-gate-2026-10-02.md);
Corollary LC5 of the
[leftmost-chain note](p1b-leftmost-chain-periodic-pair-2026-10-05.md); the
[`dim H¹` census](c4-h1-census-2026-11-05.md). The side-notes ledger was read
first (entries of 2026-10-05 on the leftmost chain and of 2026-11-05 on the
cut attractor, coincidence rank two and the `dim H¹` census).

## Work shown

### Assumptions and hypotheses

Hypotheses that transfer to PIP3, nonunit included: primitivity, aperiodicity
and Pisot inflation (Baker–Barge–Kwapisz, Barge 2015, Barge–Diamond 2008);
Pisot type (Barge–Diamond 2002: an irreducible cubic has no zero root and its
non-Perron roots have modulus below one); irreducibility (Minervino–
Thuswaldner).

Hypotheses that do not transfer, and what replaces them:

| Needed | Source hypothesis | Replacement or restriction |
| --- | --- | --- |
| `Σ = Γ = ℤ³` (the fibre over `0` is the set of integer strands) | deferred to a unimodular paper not obtained | direct proof on every alphabet with ℚ-independent letter frequencies (Lemma 6; Theorem R on main) |
| `cr ≥ ν_R` | Remark 4.3 has half-open states | reflection `x ↦ −x` conjugates `σ` to its reversal and preserves Def. 4.1; (F) is reversal-invariant |
| exclusion of `cr = 2` | Thm 22: odd norm | Theorems P, FC3(b),(c), N are stated for odd `det M` only; nothing is claimed for `det M = 2` |
| every class of `H¹(Ω; ℤ)` is an eigenfunction class | none in print | unit and `dim H¹ = 3` (Theorem Fork only) |
| strong coincidence | hypothesis of Minervino–Thuswaldner Thm 9.9 and of the published (F) criteria | not assumed; replaced by `cr ≤ 2` on (F) plus an arithmetic exclusion of `cr = 2` |

### Derivation / reduction

Theorem FC1 uses no source: equivariance of relative states under inflation,
finiteness from the Pisot contraction, and Theorem A. Theorem FC2 reduces to
Def. 4.1 and Remark 4.3 at `q = 0`, the return-lattice lemma and
Barge–Diamond 2002. Theorem P reduces to the chain
`H¹(Ω_{(Φ_s)_op}) ≅ H¹(Ω_{Φ_s}) ↪ H¹(Ω_Φ)` of Barge 2015 read with the
substitution action, the Barge–Diamond exact sequence, and a computation in
`𝔽₂[t]`. Theorems FC3 and N are compositions. Theorem Fork adds an
equivariant-circle-map argument on Barge's quotient `Ω/≈_s`. What is prior
art and what is new is itemised in §8 of the proof note; in short: the (F)
class, case (a) of FC3, the `dim H¹ ≤ 4` exclusion and the parity class are
known objects; the links "(F) ⇒ bounded gaps for every pair of periodic
rays", "(F) ⇒ `cr = ν_L = ν_R ≤ 2` on three letters" and the parity
exclusion of `cr = 2` were found in no source read.

### Evidence and replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_geometric_f.mojo)
```

The regression decides (F) exactly on all 4,554 corpus specimens (1,794
satisfy it), ties it specimen by specimen to the terminal leftmost cycles of
Corollary LC5, replays the relative states of Theorem FC1 and pins the class
counts of Theorems P and FC3. It certifies no coincidence rank, no strong
coincidence and no spectrum. Numbers are quoted in the proof note, §9.

### Negative controls

From the literature: the Morse substitution (`λ = 2`; Baker–Barge–Kwapisz
§5: `h_φ` a.e. two-to-one) and their Example 5.3 (reducible, `λ` a Pisot
unit, `cr = 2`) show that irreducibility is needed for any `cr = 1`
statement; the Barge–Bruin–Jones–Sadun examples (`cr = 3`, minimal
cohomology, norm divisible by 3) bound what cohomology alone can give;
Akiyama–Lee Examples 4.6–4.7 (reported from the repository gate) are
reducible extensions failing strong coincidence; Fibonacci has `l = 0` and an
asymptotic pair, so "`l = 0`" is not "no asymptotic cycle" (census note).
From the repository: the strict controls Thue–Morse, `10/102/211` and its
reversal, `1/012/1`, `1/012/101`, `012/120/201`, `01/2/120`, and the two new
reducible controls `011/120/2012`, `010/1222/2012`; the productive PIP3
controls `01/12/021`, `1/02/002`, `01/20/200`. The proof note states where
each argument stops on each of them.

### Non-claims / remaining gaps

Universal C4; strong coincidence or pure discrete spectrum on the (F) class
outside Theorem FC3; `cr ≤ 2` off (F); any statement for even determinant;
infinitude of the non-trivial part of the FC3 class; novelty relative to the
literature beyond "not found in the sources read". Barge–Kwapisz 2006 was not
obtained and Akiyama–Lee 2014 was not re-read. The proofs of Barge 2015 Thm 4
were not followed into Barge–Kellendonk. Theorem P and Theorem Fork are
re-derivations from printed statements and are not machine-checked.

## Decision

**Proceed, narrowed.** Record Theorem FC1 with its elementary proof,
Theorems FC2, P, FC3, N and Fork as proofs conditional on the imports above,
and the exact (F) decision with its corpus class counts as a canonical Mojo
module with a regression. Do not claim universal C4, and do not present the
class theorem as a route to it: by Theorem FC1 the bounded-gap hypothesis of
C4 is automatic on the (F) class, so there C4 is equivalent to strong
coincidence of all pairs and to pure discrete spectrum, and a proof of
universal C4 would in particular give the conclusion of the published (F)
criterion without its strong-coincidence hypothesis for every ternary
irreducible Pisot substitution with (F). The means inspected here do not
reach that.

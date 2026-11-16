# Two infinite families in the geometric property (F) class: targeted stop/go — 2026-11-16

**Status:** targeted literature stop/go note (`AGENTS.md`, review gate) for
the family theorems of
[`c4-fc3-family-2026-11-16.md`](c4-fc3-family-2026-11-16.md).
**Decision: proceed with a narrowed target: the family specialisation
only.** No novelty is claimed for the method or for the root location, and
the families are not new C4 cases. Universal C4 remains open; nothing here
changes a governed claim status (C4, #138, #139, #84, G1 and PSC are
unchanged); independent human review pending.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

## Timing, stated plainly

The sources marked below as read by the prover or by a verifier were read on
2026-11-16 during the round-2 attempt (begun about 12:10 UTC; the text of
Berthé–Bourdon–Jolivet–Siegel was downloaded at 12:43 UTC) and during its
verification (the shift-radix-system survey was downloaded at 14:34 UTC; the
records were closed at about 14:53 UTC). No repository file of this
increment existed then. The Mojo module `kernel/psc/c4_fc3_family.mojo` and
its regression were written at the build stage (file times 15:39 and 15:43
UTC), after that reading and before the text of this note, which was written
from about 16:40 UTC together with the proof note. So, as in round 1, the
order "sources first, then proof text and kernel code" was kept for the
reading, not for the gate: the decision below was recorded after the
executable part existed, and at the end of the attempt, not before it.

Two things happened only at landing, after the proofs and the module were
written. (i) The statements quoted from Berthé–Bourdon–Jolivet–Siegel, from
the shift-radix-system survey, from Barge 2016, from Barge's β-substitution
paper and from Minervino–Thuswaldner were re-checked against the texts on
disk. (ii) One source was obtained and read for the first time: Akiyama,
*Cubic Pisot units with finite beta expansions*. It is marked in the table
and enters no proof; it is the text from which the statements of
Frougny–Solomyak and of Hollander are quoted here. Reading it changed one
recorded statement: the root location of Theorem FM1 is prior art in the
range `n ≥ r + s` (below).

One clause of the route's own prior-art comparison was false; it was found
by the logic verifier and is withdrawn (below, "Products of Brun and
Jacobi–Perron substitutions").

## Proposed claims

Notation of the [(F)-class note](c4-geometric-f-class-2026-11-16.md):
standing class **PIP3** (primitive on `{0,1,2}`, `χ_M` irreducible with a
Pisot Perron root `β`, nonunit allowed), the prototile state map `f`, and
**(F)**: no `f`-periodic state has `v ≠ 0`. For integers `r ≥ 1`, `s ≥ 0`,
`n ≥ 1`:

```text
σ_{r,s,n} = (1^r, 0 1^n 2, 0 1^s),      τ_n = (1, 2 1^n 0, 01),
χ(t) = t³ − n t² − (r + s) t − r,       det M = r     (τ_n: the matrix of σ_{1,1,n}).
```

The claims proposed for a written proof and an exact replay on a finite
grid:

1. **Theorem FM1.** `σ_{r,s,n} ∈ PIP3` for `n ≥ r + s + 1`, with
   `β ∈ (n, n+1)` and `χ(t) = (t − β)(t² + εt + r/β)`, `ε = β − n`;
   `τ_n ∈ PIP3` for every `n ≥ 1`.
2. **Theorem FM2.** `σ_{r,s,n}` satisfies (F) for all `n ≥ 3r + s`, and
   `τ_n` for all `n ≥ 5`.
3. **Theorem FM3.** `g = (1,0,0)`; `g_R = (1,2,1)` and `dim H¹ = 4` for
   `s ≥ 1`; `g_R = (1,2,0)` and `dim H¹ = 5` for `s = 0`; for `τ_n`,
   `g = (1,2,0)`, `g_R = (1,0,1)`, `dim H¹ = 5`.
4. **Corollary FM4, Proposition FM6.** For `r` odd and `s ≥ 1`,
   `n ≥ 3r + s`; for `r` odd, `s = 0`, `n` even, `n ≥ 3r`; and for `τ_n`,
   `n` odd, `n ≥ 5`: the substitution lies in the non-trivial part of the
   FC3 class ((F), at least two periodic letters for both endpoint maps,
   odd determinant, clause (b) or (c) of Theorem FC3). The members are
   pairwise unrelated by powers, relabelling and reversal. So that part of
   the class is infinite, with nonunit members of every odd determinant
   `r ≥ 3`. The conclusion `cr = 1` is conditional on the imports of
   Theorem FC3.
5. **Proposition FM5.** Explicit left and right strong-coincidence
   witnesses at levels at most 3. So "no strict system" is elementary on
   the families.

The executable part is `kernel/psc/c4_fc3_family.mojo` with
`kernel/tests/test_c4_fc3_family.mojo`: the statements on the grid
`1 ≤ r ≤ 5`, `0 ≤ s ≤ 2`, `1 ≤ n ≤ 3r + s + 6` and `τ_n`, `n ≤ 16`.

## Prior art and field terminology

- **Property (F) of β-expansions.** For `β > 1`, `Fin(β)` is the set of
  numbers with a finite greedy β-expansion, and (F) is
  `Fin(β) = ℤ[β⁻¹] ∩ [0, ∞)` (Frougny–Solomyak; the definition as printed
  by Akiyama). (F) implies that `β` is a Pisot number (Frougny–Solomyak,
  Lemma 1, as quoted by Akiyama).
- **Geometric property (F).** Minervino–Thuswaldner Def. 9.3 and Prop. 9.4,
  for irreducible Pisot substitutions, unit or not; their text says that it
  "is an equivalent formulation of the finiteness property firstly
  introduced in [17] in the beta-numeration framework and further studied
  in [1]" (their reference numbers). It is the property (F) of the
  (F)-class note (its Lemma 5). In the repository the class is also the
  "no terminal leftmost cycle" class of Corollary LC5.
- **Shift radix systems.** For `𝐫 = (r₁, …, r_d) ∈ ℝ^d`,
  `τ_𝐫(a₁, …, a_d) = (a₂, …, a_d, −⌊r₁a₁ + ⋯ + r_d a_d⌋)` on `ℤ^d`; `τ_𝐫` is
  a shift radix system if every orbit reaches `0` (Akiyama–Borbély–
  Brunotte–Pethő–Thuswaldner). The set of such `𝐫` is written `D_d⁰`.
- **β-substitution.** For a Pisot `β` whose expansion of `1` is finite,
  `d_β(1) = t₁ ⋯ t_m`, the substitution `i ↦ 0^{t_{i+1}}(i+1)`,
  `m − 1 ↦ 0^{t_m}` on the letters `0, …, m − 1` (the usual definition,
  not taken from a text on disk; Barge's paper uses another prototile
  convention and says in a footnote that the two are related by rewriting
  and give isomorphic tiling systems). Its first-letter map is eventually
  constant, with the fixed letter `0`.
- **Dominant and non-increasing coefficients.** Two classical sufficient
  conditions for (F) of β-expansions, for
  `Irr(β) = x^m − a_{m−1}x^{m−1} − ⋯ − a_0`: non-increasing coefficients
  `a_{m−1} ≥ ⋯ ≥ a_0 > 0` (Frougny–Solomyak) and a dominant coefficient
  `a_{m−1} > a_{m−2} + ⋯ + a_0`, `a_i ≥ 0` (Hollander).

## Primary sources inspected

"Prover", "logic verifier", "prior-art verifier" are the round-2 route and
its two verifiers; "landing" is the author of this note.

| Source | Exact result | Hypotheses and transfer boundary | Read |
| --- | --- | --- | --- |
| Akiyama–Borbély–Brunotte–Pethő–Thuswaldner, *Basic properties of shift radix systems* (survey, 9 pages; author-hosted text; published in Acta Math. Acad. Paedagog. Nyházi., reference not checked against the journal) | **Theorem 1** (attributed there to Hollander): for `β > 1` an algebraic integer with minimal polynomial `X^d − b₁X^{d−1} − ⋯ − b_d` and `X^{d−1} + r₂X^{d−2} + ⋯ + r_d` its cofactor by `X − β`, `(r_d, …, r₂) ∈ D⁰_{d−1}` iff every element of `ℤ[1/β] ∩ [0, ∞)` has a finite greedy expansion. **Theorem 3**: spectral radius below 1 gives eventual periodicity, and finiteness is decidable on a computable box. **Theorem 4**: `0 ≤ r₁ ≤ ⋯ ≤ r_d < 1` implies `𝐫 ∈ D_d⁰` | Statements only; all proofs are deferred there to two papers on generalized radix representations, which were not read. For `χ = t³ − nt² − (r+s)t − r`: the cofactor is `t² + εt + rθ`, so the attached system is `τ_{(rθ, ε)}`, and `0 < rθ ≤ ε < 1` for `β ∈ (n, n+1)`: Theorem 4 gives finiteness of that one-branch system. **Does not transfer** to the state map of `σ_{r,s,n}`, which has three branches (next section) | prior-art verifier (Theorems 1 and 4), 2026-11-16; whole text at landing |
| Akiyama, *Cubic Pisot units with finite beta expansions* (author-hosted text; in *Algebraic Number Theory and Diophantine Analysis*, de Gruyter 2000; publication data not checked) | Definition of (F). "Theorem 1 (Frougny and Solomyak)": `a_{m−1} ≥ ⋯ ≥ a_0 > 0` implies (F), stated there for a Pisot number `β`. Hollander's sufficient condition `a_{m−1} > a_{m−2} + ⋯ + a_0`, `a_i ≥ 0`, as quoted from his thesis. Theorem 3 (printed with "cubic Pisot number"; the abstract and §2 make clear that units are meant): a cubic Pisot unit has (F) iff it is a root of `x³ − ax² − bx − 1` with `a ≥ 0`, `−1 ≤ b ≤ a + 1` | β-numeration only. For the unit members (`r = 1`, `b = 1 + s`): `β` has (F) iff `s ≤ n`. A statement about `β`, i.e. about the β-substitution with that polynomial, not about `σ_{1,s,n}` | §1 (introduction and statements), **at landing only**, after the proofs were written; used in no proof |
| Frougny–Solomyak, *Finite beta-expansions*, Ergodic Theory Dynam. Systems 12 (1992) 713–723 | the non-increasing-coefficient theorem and Lemma 1, as quoted by Akiyama | For `n ≥ r + s` the coefficients `n ≥ r + s ≥ r > 0` are non-increasing: (F) of β-expansions for the Perron root of every member in that range. Covers the root location of Theorem FM1 in spirit; the proof note keeps its own proof | **not read**; quoted from Akiyama |
| Hollander, *Linear numeration systems, finite beta expansions, and discrete spectrum of substitution dynamical systems*, PhD thesis, University of Washington, 1996 | the dominant-coefficient condition; the theorem behind Theorem 1 of the survey | as quoted by Akiyama and by the survey | **not read** |
| Brauer, *On algebraic equations with all but one root in the interior of the unit circle*, Math. Nachr. 4 (1951) 250–257 | the usual reference for "non-increasing positive coefficients give a Pisot root" | — | **not read**; a search did not surface a statement, so nothing is attributed to it beyond the title |
| Minervino–Thuswaldner, *The geometry of non-unit Pisot substitutions*, Ann. Inst. Fourier 64 (2014); arXiv:1402.2002 | Def. 9.3, Prop. 9.4 (geometric property (F)); the sentence relating it to β-numeration; Thm 9.9 ((F) and strong coincidence imply that the self-replicating multiple tiling is a tiling) | irreducible Pisot, unit not required. Names (F). Thm 9.9 has strong coincidence as a hypothesis; on the families strong coincidence is explicit (FM5) | round-1 routes; these statements re-checked at landing; used in no proof |
| Barge, *Pure discrete spectrum for a class of one-dimensional substitution tiling systems*, Discrete Contin. Dyn. Syst. 36 (2016); arXiv:1403.7826 | Thm 3.13 (primitive, Pisot, injective on initial letters, constant on final letters: pure discrete spectrum); Remark 3.14 (eventually constant suffices, after passing to a power) | No member is in the class or its mirror, for any power: `g = (1,0,0)` is never injective and `g^k` has image `{0,1}`; `g_R^k` has image `{1,2}` (`s ≥ 1`) or is a 3-cycle (`s = 0`); for `τ_n`, `g` is a 3-cycle and `g_R^k` has image `{0,1}`. No power has a common first or a common last letter, so no power has a non-trivial conjugate | round-1 routes in full; the two statements re-checked at landing |
| Barge, *The Pisot conjecture for β-substitutions*, arXiv:1505.04408 | Abstract and §1: for a Pisot number `β` the tiling system of the β-substitution has pure discrete spectrum; §2: the definition | Applies to the β-substitution of `β`, hence to the letter order `(1^r, 1^n 0 2, 1^s 0)` of the same matrix as far as that order is a β-substitution in disguise (below). **Does not transfer**: no member is a β-substitution (no fixed letter of `g` or `g_R`), and `dim H¹` is 4 or 5 against at most 3 for a three-letter β-substitution | abstract, §1 and the definition in §2, at landing; round 1 had read §1, §3 and Cor. 17 |
| Berthé–Bourdon–Jolivet–Siegel, *A combinatorial approach to products of Pisot substitutions*, arXiv:1401.0704v2 | §2.2: the Brun substitutions `(1, 2, 32)`, `(1, 3, 23)`, `(2, 3, 13)` on `{1,2,3}`; Prop. 2.3; Remark 2.4 (the letter ordering is not canonical; for Brun the same results hold for other orderings by the same techniques). §2.3: the Jacobi–Perron substitutions `σ_{a,b}: 1 → 3, 2 → 1 3^a, 3 → 2 3^b` "for all `a, b ≥ 0`"; admissible sequences (`0 ≤ a_k ≤ b_k`, `b_k ≠ 0`, `a_k = b_k ⇒ a_{k+1} ≠ 0`); Prop. 2.6. §5: admissible products; Cor. 5.7 (pure discrete spectrum for every admissible finite product of Brun or Jacobi–Perron substitutions) | Unimodular. See "Products of Brun and Jacobi–Perron substitutions" below for what transfers; the corollary covers admissible products only | prover (definitions, Prop. 2.3, 2.6, Remark 2.4, list of results; proofs not read); both verifiers (definitions and admissibility); §§2.2–2.3, the definition of admissible products in §5 and the statements of Cor. 5.5–5.7 re-read at landing |
| Mercat–Akiyama, *Yet another characterization of the Pisot substitution conjecture*, arXiv:1810.03500 | the families `a → a^k b c, b → c, c → a` and `a → a^l b a^{k−l}, b → c, c → a` with pure discrete spectrum (§6) | Unit. After `a = 1, b = 2, c = 0` the first family is `(1, 1^k 2 0, 0)`: the incidence matrix of `σ_{1,0,k}`, whose image of `1` is the cyclic rotation `0 1^k 2`. The substitutions are not conjugate (the one-letter images force an empty conjugating word), and `dim H¹` is 3 there (first-letter map eventually constant) against 5 | on main: [gate of 2026-10-12](mercat-akiyama-interior-language-gate-2026-10-12.md) (§§3, 5–7); abstract page by the prior-art verifier; not re-read at landing |
| Sellami, *Balanced pair algorithm for a class of cubic substitutions*, Turkish J. Math. 39 (2015); Loridant 2016 | the β-substitution of `x³ − ax² − bx − 1`, `a ≥ b ≥ 1` | the polynomial of `σ_{1,s,n}` with `(a, b) = (n, 1 + s)`, another matrix | **not read**: journal abstract (prior-art verifier), search summaries (prover) |
| Akiyama–Gähler–Lee (three-letter substitutions of incidence trace at most 2) | as recorded in the side-notes ledger | covers members with `tr M = n ≤ 2`; in the proved regime `n ≥ 3` | **not re-read** |
| Akiyama–Scheicher 2007; Huszti–Scheicher–Surer–Thuswaldner 2007; Kirschenhofer–Pethő–Surer–Thuswaldner 2010 | stable integer recurrences with bounded rounding; symmetric shift radix systems | already recorded on main as prior art for the Class-A recurrences ([gate of 2026-11-15](bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md)) | **not re-read** here |
| Barge–Diamond, Proc. Amer. Math. Soc. 136 (2008) 2183–2191 | Theorem 4, through Lemma 7 of the (F)-class note | primitive, aperiodic; holds on PIP3 | round-1 routes; not re-read |

Repository sources relied on: the three round-1 notes; Lemma 7 and Theorems
FC2, FC3 of the (F)-class note; Theorem A(4) of the
[cut-pair note](c4-cut-pair-productivity-2026-11-04.md) (Lean,
`Psc.StrictSystem.no_strictSystem_of_strongCoincidence`). The side-notes
ledger was read first (the entries of 2026-11-16 on the (F) class, on
Theorem P and on the nonunit families).

### What the shift-radix-system literature gives, and where it stops

Let `β ∈ (n, n+1)`, `θ = 1/β`, `ε = β − n`, `v = (a, b, c)`,
`m = ra + nb + sc`. The proof note shows that the state map of
`σ_{r,s,n}` acts on `(c, b)` by `c′ = b` and

```text
tile 0:                          b′ = −⌊rθ·c + ε·b⌋                 (the system τ_{(rθ, ε)})
tiles 1, 2, non-empty prefix:    b′ = −⌊rθ·(c − 1) + ε·b⌋           (the same map at (c − 1, b))
tiles 1, 2, empty prefix:        b′ = −⌊rθ·(c − 1) + ε·b⌋ − 1.
```

The first line is literally the shift radix system that Theorem 1 of the
survey attaches to `β`. Theorem 4 of the survey gives its finiteness for
every member with `β ∈ (n, n+1)`; this is the Frougny–Solomyak regime
`n ≥ r + s`, and it is property (F) of the β-numeration of `β`. The state
map of `σ_{r,s,n}` is a variant with two further branches, and neither
theorem applies to it as stated. The trapping lemma of the proof note is
the elementary dominant-coefficient (`ℓ¹`) argument for that variant; its
hypothesis is `ε + 2rθ ≤ 1` (equivalently `n ≥ 3r + s`), where the
one-branch argument needs `ε + rθ < 1` (equivalently `n ≥ 2r + s`,
Hollander's condition `n > (r + s) + r` up to the boundary case). The extra
`rθ` is the price of the shifted branch. The repository already records
this methodology as established for its Class-A recurrences.

### The same matrix in another letter order: a β-substitution in disguise

(Observation of the prior-art verifier; the identities below were
re-derived at landing.) The substitution
`σ′ = (1^r, 1^n 0 2, 1^s 0)` has the incidence matrix of `σ_{r,s,n}`. With
the blocks `B₀ = 1`, `B₁ = 02`, `B₂ = 0`:

```text
σ′(B₀) = 1^n 0 2 = B₀^n B₁,     σ′(B₁) = 1^r 1^s 0 = B₀^{r+s} B₂,     σ′(B₂) = 1^r = B₀^r.
```

This is the β-substitution for `d_β(1) = n (r+s) r`, which is the expansion
of `1` exactly when `n ≥ r + s` (the lexicographic condition; `χ(β) = 0`
reads `1 = nθ + (r+s)θ² + rθ³`). So that letter order falls under the
β-numeration literature: property (F) by Frougny–Solomyak, pure discrete
spectrum by Barge's theorem for the β-substitution. Its first-letter map is
constant, so it is in the endpoint-collapse stratum of the repository
(Theorem A(3)) and has `dim H¹ = 3`. The families of the proof note move the
letter `0` to the front of two images. Their tiling spaces have
`dim H¹ = 4` or `5`, so they are not homeomorphic to that of `σ′`, and
nothing transfers. The exact relation between the tiling space of `σ′` and
that of the β-substitution on the blocks was not written out; it is not
used.

### Products of Brun and Jacobi–Perron substitutions

The route record stated: "`σ_{1,s,n}` and `τ_n` are not products of Brun or
of Jacobi–Perron substitutions (in either orientation)". **This is false and
is withdrawn.** With the Jacobi–Perron substitutions as printed (letters
`0, 1, 2` for `1, 2, 3`: `σ_{a,b}: 0 → 2, 1 → 0 2^a, 2 → 1 2^b`), for every
`n ≥ 0`, rightmost factor first:

```text
τ_n  =  σ_{0,0} ∘ σ_{n,0} ∘ σ_{0,1} ∘ σ_{0,0} ∘ σ_{0,1}
reversal of σ_{1,0,n}, relabelled by 0 → 1 → 2 → 0:   (1, 2, 0 2^n 1)  =  σ_{n,0} ∘ σ_{0,1}.
```

(Found by the logic verifier; checked by hand at landing.) The factors
`σ_{0,0}`, `σ_{n,0}` have `b = 0` and are not admissible.

What survives, in the form the verifiers state it, with the argument
re-derived at landing:

- Every Brun substitution (in the printed letter ordering) and every
  Jacobi–Perron substitution has a bijective first-letter map; so does
  every product, and every relabelling of one.
- The last-letter maps of the three Brun substitutions are weakly
  increasing (`(1,2,2)`, `(1,3,3)`, `(2,3,3)`), so the last-letter map of a
  Brun product has no cycle of length at least 2.
- For `b ≥ 1` the Jacobi–Perron last-letter map sends `1` and `3` to `3`
  and `2` to `1` or `3`; so the last-letter map of a product of
  Jacobi–Perron substitutions with all `b_k ≥ 1` (in particular of an
  admissible product) is eventually constant. For `b = 0` it is not:
  `σ_{a,0}`, `a ≥ 1`, has last-letter map `1 → 3, 2 → 3, 3 → 2`.
- Hence: **`σ_{1,s,n}` with `s ≥ 1` is not a product of Brun or
  Jacobi–Perron substitutions, in either orientation and up to relabelling**
  (`g = (1,0,0)` and `g_R = (1,2,1)` are not bijective).
  **`σ_{1,0,n}`, `τ_n` and their reversals are not Brun products with the
  printed letter orderings and not Jacobi–Perron-admissible products**
  (where the first-letter map is bijective, the last-letter map has a
  2-cycle and is not eventually constant); the same holds for their powers.
  So Cor. 5.7 of Berthé–Bourdon–Jolivet–Siegel does not cover them. But
  `τ_n` and the relabelled reversal of `σ_{1,0,n}` are products of
  non-admissible Jacobi–Perron substitutions, as displayed.
- Not excluded: Brun substitutions with other letter orderings (their
  Remark 2.4); those need not have bijective first-letter maps. Only an
  exploratory matrix-level computation of the prover speaks to that (the
  matrix of `σ_{1,1,n}` is a product of Brun matrices only for `n = 1`,
  `n ≤ 14`; scratch).
- **Not examined:** the Jacobi–Perron literature beyond admissible
  products, including the modified Jacobi–Perron substitutions that the
  paper cites. Whether pure discrete spectrum is in print for the
  non-admissible products above is not known here.

*Stop/go re-run for the two clause-(c)-only families (`σ_{r,0,n}` and
`τ_n`), with this in hand.* The proof note claims for them (F), class
membership and explicit witnesses; it claims no novelty for pure discrete
spectrum, which on these members is a conditional consequence of Theorem
FC2 with the witnesses. The Jacobi–Perron factorisation changes none of the
proofs and none of the hypotheses. It removes one sentence of the
comparison and adds one unexamined body of literature. Decision for these
two families: proceed, with the statement "not Jacobi–Perron-admissible
products" in place of "not Jacobi–Perron products", and with the novelty
claim restricted to "not found in the sources read". The clause-(b) family
(`s ≥ 1`) is unaffected.

### Families already in the repository

| Family | Where | Relation to `σ_{r,s,n}`, `τ_n` |
| --- | --- | --- |
| `(01, 1^a 2 1^b, 012)`, its reversal, `(01, 1^a 2 1^b, 021)`, `(01, 1^k 2 1^k, 012)` | on main: the run-family notes of 2026-11-04 ([closed run family](c4-closed-run-family-four-level-coincidence-2026-11-04.md), [reversed](c4-reversed-run-family-four-level-coincidence-2026-11-04.md), [direct source](c4-direct-source-coincidence-2026-11-04.md), [uniform third level](c4-uniform-third-level-coincidence-family-2026-11-04.md)) | incidence `[[1,0,1],[1,s,1],[0,1,1]]`, `χ = x³ − (s+2)x² + 2sx − s`, `e₂ = 2s > 0`; a member here has `e₂ = −(r+s) < 0`. No member is a relabelling or reversal of one of them |
| `F1_c = (0^{c−1}1, 120^{c−1}, 0^c)`, `F3_c = (0^{c−1}10, 021, 20)` | round 1, [closure-attempt note](c4-closure-attempt-2026-11-16.md) §5.5 | `χ = x³ − cx² − c` (`e₂ = 0`) and `x³ − (c+2)x² + 2cx − c` (`e₂ = 2c`): different polynomials |
| Theorem K's family (`σ(o) = y`, `σ(y) = o w₁ o`, `σ(z) = o w₂ o`, `abs(det M) = 2`) | on main, [`p1a-a1-prime-2026-10-05.md`](p1a-a1-prime-2026-10-05.md) | a member with `det M = 2` has `σ(0) = 11`; a one-letter image occurs only for `s = 0` (`σ(2) = 0`), and then `σ(0) = 11` does not begin and end with that letter. Not of that shape, in either orientation |
| the plus Class-A family `σ(x) = x y^{n+d} x`, `σ(c) = c y^n x`, `σ(y) = x y^{n+1} c` (`det M = 2`) | on main, [gate of 2026-11-15](bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md) | `χ = X³ − (n+4)X² + (n−d+5)X − 2`. For `d ≥ n + 7` this is the polynomial of `σ_{2, d−n−7, n+4}`. The substitutions differ: every image there has at least `n + 2 ≥ 9` letters and `g` has two fixed letters; here `σ(0) = 11` and `g`, `g_R` have none |
| `(1, 0 1^k 2, 0^q 1)`, `q ≥ 2` | **unmerged** draft branches (PR #576 and the family branches; quoted for orientation only) | `σ_{1,1,n}` is the member `q = 1` of that shape; the draft notes treat `q ≥ 2`. Exploratory scratch observation of the prover and of both verifiers: for `q ≥ 2` the tested members fail (F), so the two families overlap in no theorem |
| the six members named in round 1 (`102/20/1200`, …) | (F)-class note §9, scratch | none is of the shape |

Corpus overlap (pinned through the grid): `σ_{1,1,1} = 1/012/01` and
`τ_1 = 1/210/01` are corpus specimens in the non-trivial part of the FC3
class; `σ_{1,0,1} = 1/012/0` and `σ_{2,0,1} = 11/012/0` are corpus
specimens in PIP3 with (F) outside it; `σ_{2,1,1} = 11/012/01` is a corpus
specimen that fails (F).

## Work shown

### Assumptions and hypotheses

Hypotheses that transfer to the families: primitivity and the Pisot
property are conclusions of Theorem FM1; Lemma 7 (Barge–Diamond 2008) needs
PIP3 only; Theorem A(4) needs only the witnesses; the imports of Theorems
FC2 and FC3 hold on PIP3 as recorded in the (F)-class note, nonunit
included.

Hypotheses that do not transfer, and what replaces them:

| Needed | Source hypothesis | Replacement or restriction |
| --- | --- | --- |
| (F) for the state map of `σ_{r,s,n}`, `τ_n` | finiteness theorems for the one-branch system `τ_{(rθ, ε)}` (Frougny–Solomyak; Hollander; Theorem 4 of the survey) | a direct trapping lemma for the three-branch map, under `ε + 2rθ ≤ 1` (`n ≥ 3r + s`), resp. `5θ + 2θ² ≤ 1` (`n ≥ 5`); nothing is proved for `r + s ≤ n < 3r + s` |
| pure discrete spectrum | Barge 2016: injective initial, eventually constant final letters; Barge's β-substitution theorem: the β-substitution; Berthé–Bourdon–Jolivet–Siegel Cor. 5.7: admissible products; Mercat–Akiyama: their two families | none applies; not needed, since Theorem FC2 with the explicit witnesses gives `cr = 1` conditionally |
| irreducible Pisot `χ` | non-increasing coefficients (Frougny–Solomyak as quoted; Brauer not read) | a direct root location (Theorem FM1), needed anyway for the bounds on `ε` and `rθ` |
| a canonical machine decision of (F) | `psc.c4_geometric_f` is certified for images of at most six letters | the written proof; on the grid a screened decision, guarded as listed in the proof note §12 |

### Derivation / reduction

Theorem FM1 is a sign change and a division. Theorem FM2 reduces (F) to an
integer recursion for `(c, b)` with a bounded rounding term, a trapping
lemma and a finite class table. Theorem FM3 is a closure of two-letter words
and Lemma 7. Corollary FM4 is a parity count; Proposition FM6 uses the
Perron column and the periodic letters of the endpoint maps. Proposition
FM5 is a list of word identities. What is prior art and what is not is
itemised in §11 of the proof note: the root location and the method are
prior art; (F) for the one-branch system is Frougny–Solomyak; the family
statement and the discharge of the round-1 non-claim were not found in the
sources read.

### Evidence and replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_fc3_family.mojo)
```

The regression pins the statements on 240 members of the first family (220
in PIP3) and on `τ_1, …, τ_16`; numbers are quoted in the proof note, §6
and §12. It certifies no coincidence rank and no spectrum, and it does not
replay the trapping lemma. The Jacobi–Perron factorisations, the block
identities of the disguised β-substitution and the comparison of
characteristic polynomials above were checked by hand and by a landing
scratch script on words (`n ≤ 39`, resp. `r ≤ 5`, `s ≤ 3`); they are
comparisons, not evidence of record.

### Negative controls

From the literature: Akiyama's Theorem 3 shows that (F) of β-expansions
fails for cubic Pisot units outside `−1 ≤ b ≤ a + 1`, so finiteness is not
automatic for a Pisot root; the survey records that the set `D_d⁰` is cut
out of the stable region by infinitely many polyhedra, so no spectral
condition alone gives finiteness. From the repository and the grid: ten
PIP3 members of the shape fail (F), all with `n ≤ r + s − 1`; the reducible
member `σ_{1,2,1} = 1/012/011` shares its matrix with the strict control
`1/012/101`; the unmerged shape `(1, 0 1^k 2, 0^q 1)`, `q ≥ 2`, fails (F)
on the members tested (scratch); the 20 grid members outside PIP3 are
refused. The proof note states where each argument stops on each control
that has a strict system.

### Non-claims / remaining gaps

Universal C4; any new C4 case; (F) for `r + s ≤ n < 3r + s` (expected, not
proved); novelty of the method or of the root location; novelty of the
family statement beyond "not found in the sources read". Frougny–Solomyak
1992, Hollander's thesis and Brauer 1951 were not read; Sellami and
Loridant only as abstracts or summaries; Akiyama–Gähler–Lee and the
symmetric shift-radix-system papers were not re-read; the two papers that
contain the proofs of the survey's theorems were not read; the
Jacobi–Perron literature beyond admissible products was not examined;
Akiyama's cubic paper was read only at landing. Whether (F) for the families
follows from a known finiteness theorem for some other numeration system
was not examined beyond the sources in the table.

## Decision

**Proceed, narrowed.** Record Theorems FM1–FM3, Corollary FM4 and
Propositions FM5, FM6 as a family specialisation, with: the attribution of
the method to the shift-radix and β-numeration finiteness theory; the root
location marked as prior art for `n ≥ r + s`; the corrected Brun and
Jacobi–Perron clause; the statement, next to the corollary, that every
member also has explicit witnesses and is therefore not a new C4 case; and a
Mojo regression on a finite grid that says plainly that the canonical
decision of (F) refuses all but three members of the proved regime. Do not
claim universal C4, a new C4 case, or (F) below the thresholds. Do not
pursue the expected statement "(F) for every `n ≥ r + s`" without first
reading Frougny–Solomyak 1992 and the two papers behind Theorems 1 and 4 of
the survey in the primary text: the threshold `n ≥ r + s` is exactly their
non-increasing-digit condition, and the question is whether their rewriting
argument extends to the three-branch map.

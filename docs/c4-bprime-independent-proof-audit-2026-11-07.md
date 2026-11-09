# Independent audit: Proposition B′ and Corollary B (2026-11-07)

**Source revision:** merged PR #504, mathematical note at `e9cfafebb0b0c7448757fee6ef53f77d8042e95a`, `docs/c4-general-structure-2026-11-06.md`, §3. **Audit disposition:** the B′ argument is mathematically sound **under the Sirvent–Solomyak prefix-seeded definition**, subject to human mathematical review; the proof can be shortened and its actual obligations isolated. This is **not** a kernel-checked theorem, a claim of originality, or a closure of C4, G1, A1′, BH, or PSC. Corollary B(i) follows with that same restriction; (ii) and (iii) depend separately on R3 and R2 and are **not independently formalized here**.

## Corrected theorem (exact scope)

Let `ζ` be a primitive, nonerasing substitution of a finite alphabet with incidence matrix `M` whose degree-`d` characteristic polynomial is irreducible over `Q`. Let `u` be a one-sided fixed point of `ζ` and `W` any nonempty prefix of `u`. Define `I_n(W)` **exactly as in** Sirvent–Solomyak (2002), §3: start with the irreducible reduction of `(u, shift^{|W|}u)` and successively reduce all substituted pairs; termination means the union `I(W)` is finite, **not** termination with coincidence. If `I(W)` is finite, every eigenvalue of `M` other than the Perron root `β` has absolute value at most 1.

For an irreducible cubic there are no unit-circle conjugates, so termination implies Pisot. Equivalently, if its Perron root is non-Pisot, **every** prefix-seeded BPA on every one-sided fixed point fails to terminate. The theorem does not address the pure-discrete-spectrum half of Sirvent–Solomyak Remark 2, and does not assert infinite closure for arbitrary balanced-pair seeds in the one-outside cubic class.

## Independent proof, with each dependency visible

1. **Reduction/descendant identity (imported, verified against §3).** Sirvent–Solomyak (2002), p. 700, formula (3.1), asserts that `I_{n+1}(W)` consists of the irreducible subpairs of the substitutions of `I_n(W)`, *equivalently* those arising in the reduction of `(u, shift^{|ζ^n(W)|}u)`. The initial reduction exists and is finite for each prefix by uniform recurrence. This is not a claim about all balanced pairs. Take `t_n=|ζ^n(W)|`, `w=p(W)`, and `L=max{|x| : (x,y) in I(W)}`, finite under the termination hypothesis. The infinite pair `(u, shift^{t_n}u)` has a full partition into aligned, irreducible balanced blocks of length at most `L`. This is exactly the step requiring *prefix-seeded* termination and the fixed-point relation; it does not follow from existence of some unrelated finite child-closed system.

2. **Cut-bound and factor identity (elementary).** Let `P(k)=p(u[0,k))` and `D_n(k)=P(k)-[P(t_n+k)-P(t_n)]`. At every common balanced-block boundary, `D_n=0`. Inside a block of length at most `L`, each letter-coordinate of the difference of its two prefixes has magnitude at most `L`; hence `||D_n(k)||_∞≤L` for every `k≥0`, independently of `n`. Exactly, by cancellation of prefix sums,

   `D_n(k) = P(t_n) - [P(k+t_n)-P(k)]`.

   Since `u=ζ^n(u)` and `W` is its prefix, `P(t_n)=p(ζ^n(W))=M^n w`. Thus every length-`t_n` factor has count vector within `L` of `M^n w` (not an estimate for all factor lengths).

3. **Frequency averaging (no stronger balance assumption).** Primitivity supplies letter frequencies `f∈R^d`, normalized by `1^T f=1`, and `Mf=β f`. For each *fixed* `t_n`, Cesàro averaging the sliding-factor vectors `P(k+t_n)-P(k)` over `0≤k<K` converges to `t_n f`: it is a finite sum of shifts of the letter-indicator sequence, each with the same frequency `f`. Averaging the bound in (2) and passing to the limit gives

   `||M^n w - t_n f||_∞ ≤ L` for **every** `n`. No uniform convergence in `n` is required; first fix `n`, then send `K→∞`. No measure-theoretic spectral hypothesis enters.

4. **Nonvanishing in every conjugate direction (purely algebraic).** The rational cyclic subspace `U=span_Q{w,Mw,...,M^{d-1}w}` is nonzero (`W≠ε`), `M`-invariant, and must equal `Q^d`: the minimal polynomial of `M` on the cyclic span is nonconstant and divides the irreducible characteristic polynomial, so it equals that polynomial and has degree `d`. Equivalently, the Krylov matrix `[w|Mw|...|M^{d-1}w]` has nonzero determinant. For **any** nonzero complex left eigenfunctional `q` with `qM=λq`, we must have `q(w)≠0`: otherwise `q(M^j w)=λ^j q(w)=0` for every `j`, contradicting the Krylov spanning property. This argument avoids all choices of Galois-normalized eigenbases or coefficient conjugacy. Irreducibility over `Q` is essential here; primitivity by itself does not guarantee cyclicity of an arbitrary nonzero integer seed.

5. **Spectral contradiction.** If `λ≠β`, then `λq(f)=q(Mf)=βq(f)`, so `q(f)=0`. Apply `q` to (3):

   `|λ|^n |q(w)| = |q(M^n w - t_n f)| ≤ L Σ_a |q(e_a)|`.

   The right-hand side is independent of `n` and `q(w)≠0`. Thus `|λ|≤1`. Irreducibility in characteristic zero also makes the eigenvalues distinct, although diagonalizability is **not needed** for the displayed argument (just a left eigenvector for any chosen eigenvalue).

6. **Cubic boundary.** If an irreducible monic cubic in `Z[x]` had a conjugate on the unit circle, a real one would equal `±1`, impossible by irreducibility. Otherwise two nonreal conjugates are on the circle and their product is 1; the remaining real Perron root equals the integer determinant (up to sign), contradicting degree-three irreducibility. Therefore `|λ|<1` for both non-Perron conjugates. In higher degree the conclusion is only a **closed** disc; when a unit-circle conjugate exists the irreducible polynomial is reciprocal up to sign, giving the usual Salem situation. Do **not** upgrade B′ to strict Pisot on arbitrary alphabets.

## Adversarial assumption inventory

- **Fixed point:** used *twice*: to identify `ζ^n(W)` with the prefix of `u`, and to identify the substituted pair-reduction with a shift of the same `u`. A mere periodic substitution point requires passing to its fixing power and adjusting the seed/claim.
- **Prefix W nonempty:** ensures `w≠0`; the empty word gives no cyclicity. **All children and coincidences** must be retained in `I(W)`; a strict SCC is not a substitute for this set.
- **Primitivity:** ensures Perron frequencies and recurrence/initial reductions. The averaging step only requires frequencies; the imported reduction identity requires the substitution setup.
- **Irreducibility:** supplies cyclicity of every nonzero rational seed and the Perron/Galois correspondence. Without it the projection of `w` on an expanding eigenmode may vanish, *even if `M` is positive*: `M=[[3,1],[1,3]]`, `w=(1,1)`, eigenvalues 4 and 2 and the 2-eigenvector is orthogonal to `w`. This is a **counterexample to dropping irreducibility in step (4)**, not to B′ itself.
- **Diagonalizability:** unnecessary in the corrected proof; irreducibility already implies separability in characteristic zero.
- **Length:** `t_n` is an *integer letter count* `|ζ^n(W)|`, not a Perron-weighted geometric length. Do not substitute the latter.
- **No quantifier leakage:** a uniform bound for the special lengths `t_n` is not a proof that the whole fixed point is `C`-balanced at every length. Conversely, it is enough for the spectral contradiction.

## Independent finite/symbolic negative control (not a theorem proof)

Substitution `0→01, 1→2, 2→00` has `M=[[1,0,2],[1,0,0],[0,1,0]]` and `χ_M=x^3−x^2−2`. `M^5` is strictly positive; the rational-root test proves irreducibility; the unique real Perron root `β` lies strictly between 1 and 2, while the complex pair has squared modulus `2/β>1` (product of all three roots is 2). With `W=0`, the **exact** Krylov determinant `det[e_0|Me_0|M²e_0]=1`. The swap seed `(01,10)` produces new irreducible balanced pairs in each of the first 12 generations; bounded exploration is only a regression, not a proof of nontermination. Run `python3 tools/audit_bpa_bprime.py`; it uses the Python standard library and asserts all integer identities and pair reductions.

## Prior-art disposition (as of this audit)

| Source | Inspected scope | Consequence for novelty |
|---|---|---|
| Sirvent–Solomyak, *Canad. Math. Bull.* **45** (2002), §3, Remark 2; DOI `10.4153/CMB-2002-062-3` | Full relevant §3 including equation (3.1), definition of termination, and explicit 2002 open remark | Establishes correct terminology and the exact identity; **does not establish contemporary novelty**. |
| Adamczewski, *Theoret. Comput. Sci.* **307** (2003), Theorem 13 and Corollaries 15, 17; DOI `10.1016/S0304-3975(03)00092-6` | Direct paper: bounded balance versus expanding eigenvalues; Cor. 17 classifies eventually periodic fixed points | Strongly overlapping technique, but B′ only assumes bounded discrepancy along substitution-prefix lengths. No exact B′ claim located in these passages. |
| Martensen, *Topology Proc.* **28** (2004), *Generalized Balanced Pair Algorithm* | Introductory definitions, reducible cases and termination/nontermination discussion | Generalized **reducible** algorithm differs from prefix-seeded standard BPA; no exact B′ equivalence established. |
| Bernat, *RAIRO Theor. Inf. Appl.* **42** (2008), 663–678, DOI `10.1051/ita:2007062` | Sections 3, 5 and references; finite/infinite examples, Livshits attribution | Provides examples and prior algorithm formalism, not in inspected passages the universal irreducible non-Pisot statement. |
| Hollander 1996 PhD thesis, Livshits 1987/1992, Solomyak 1992, Hollander–Solomyak 2003 | Thesis abstract/bibliographic metadata or abstract only; primary proofs **not read** | **Open priority search**. Absence in searched excerpts is not evidence of first discovery. |
| Later monographs/surveys | Selective searchable passages only | Novelty status **undetermined**; a specialist citation trace and proof comparison is required. |

**Bibliographic links:**
- https://www.cambridge.org/core/services/aop-cambridge-core/content/view/4BC0FD9DBA6ECA027A32568F9E5C1D12/S0008439500017537a.pdf/pure_discrete_spectrum_for_onedimensional_substitution_systems_of_pisot_type.pdf
- https://adamczewski.perso.math.cnrs.fr/article_tcs.pdf
- https://www.numdam.org/item/10.1051/ita%3A2007062.pdf
- https://arxiv.org/abs/math/0309194
- https://www.cambridge.org/core/journals/ergodic-theory-and-dynamical-systems/article/abs/twosymbol-pisot-substitutions-have-pure-discrete-spectrum/602A997C102D38DB5F9C3B84B6CACB59
- https://www.mathsoc.spb.ru/pers/livshits/publ.html

## Formal-verification plan and acceptance matrix

1. **P0: isolate and kernel-check the count-vector shift identity.** `proof/bpa/BpaPrefixBridge.lean` supplies this Lean lemma without opaque spectral axioms. Check in the pinned Lean/Mathlib environment; do **not** count it as proof of B′. Its exact-head CI receipt is the accepted evidence.
2. **P0: formalize bounded-block cancellation**: prove in Lean for an infinite sequence of aligned, balanced blocks of lengths at most `L` that `||D_n(k)||_∞≤L`, including cuts and the off-by-one end of each finite block. A finite-state Quint model may check counterexample-free instances but cannot discharge the unbounded statement. Avoid treating bounded model exploration as a theorem.
3. **P0: bind Sirvent–Solomyak (3.1)** to the repository's exact `bpa-W` implementation and prove/replay a refinement of infinite reductions; include orientation, coincidences, and index `I_{n+1}` versus `t_n`.
4. **P1: algebraic cyclicity**: machine-check `irreducible χ_M ∧ w≠0 ⇒ span_Q{M^n w}=Q^d` and its left-eigenfunctional corollary. This is the most consequential mathematical dependency. No unverified normalization of Galois eigenvectors should appear.
5. **P1: averaging and growth**: in Lean, prove finite sliding-window averages converge to `t f` from letter frequencies, and show bounded `λ^n c` with nonzero `c` forces `|λ|≤1` over `C`. Separate the analytic and finite combinatorial layers.
6. **P1: check source definitions/novelty** with full Livshits, Hollander thesis, Solomyak and subsequent citation network; record passages and explicit result equivalence before any priority or novelty assertion.
7. **P2: Quint/TLA+ finite bounds**: explicit small-state model for cuts, local cumulative Parikh difference and common reset; check invariants and adversarial mistakes (missing child, wrong orientation, shifted offset). No model can prove the algebraic `d`-unbounded statement.

**Claim ledger:** No modifications. This audit adds a verification *interface*, not new statuses. B′/Corollary B remain written repository arguments, human review pending; Q(b) keeps its 28-class finite calibration; R2/R3 and C4/G1/PSC keep their original classifications. Any subsequent verified CI job supports **only the declaration it actually replays**.
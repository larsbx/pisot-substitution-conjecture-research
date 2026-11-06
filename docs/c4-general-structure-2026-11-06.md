# General C4: what a strict system forces, and where the Pisot property enters — 2026-11-06

**Status:** Proposition Q is repository-proved (written proof; one adversarial
audit: correct; independent exact oracle and canonical Mojo regression on 28
strict-carrier classes). Theorems R2 and R3 are repository-proved (written
proofs re-derived by hand; two adversarial audits found no mathematical
error); R1, R3′ and R5 are proved in §3 (same audits). A7′ is conditional and
its proof exists only in scratch (§4). The landscape census of §6 and the
Tribonacci packet of §4 are scratch evidence, not repository evidence, except
the 28 classes pinned natively. No change to C4, BH (#139),
A1′ (#138), G1 or PSC. Human review pending.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline: branch `ccr-5059e568-lh2509` at `8d97d7d` (PR #499).

A **strict system** (the manuscript's *strict component*) is a finite nonempty
set `C` of ordered irreducible noncoincident balanced pairs, strictly
child-closed. **General C4**: a primitive irreducible Pisot (PIP) substitution
on three letters has none. The standing corpus is settled
([finite-domain closure](c4-finite-domain-closure-2026-11-05.md)); this note
asks what a strict system forces for an arbitrary substitution, and isolates
exactly where the Pisot hypothesis has to do the work.

## 1. Stop/go literature check

- **Fibre cardinality.** Baker–Barge–Kwapisz 2006 (Ann. Inst. Fourier 56(7))
  Theorem 4.2: the geometric realisation map is uniformly finite-to-one and
  almost everywhere `cr`-to-one (read in the 2026-11-05 workflow). So
  finiteness of fibres is not a lever.
- **Branching arguments.** Barge–Štimac–Williams 2013 run a single `cr + 1`
  contradiction whose non-generic input is "a common vertex puts two tilings in
  one fibre", which is the hub / A1′ gap again (reported).
- **Non-Pisot balanced pairs.** Sirvent–Solomyak 2002 leave non-termination of
  the balanced-pair algorithm for non-Pisot substitutions unproved (reported).
- **Proposition Q.** Two targeted searches found no statement of it. It is the
  standard bounded-projection technique (a discrepancy that stays bounded under
  inflation has no component along an expanding eigendirection) applied to the
  Parikh span, followed by Kronecker's theorem; novelty is claimed only for its
  use here.

Decision: **proceed, narrowed** — record the structural consequences, separate
the non-Pisot cases that they settle from the Pisot case they do not, and do
not claim C4.

## 2. Proposition Q (any alphabet, any primitive substitution)

**Proposition Q.** Let `σ` be a primitive nonerasing substitution on `d`
letters with incidence `M`, and `C` any finite nonempty child-closed set of
balanced pairs (strictness is not needed). Let `V = span_ℚ{p(u_S) : S ∈ C}`.
Then
(a) `V` is `M`-invariant, so `χ_M = χ_{M|V} · χ̄` with `χ̄` the characteristic
polynomial of `M` on `ℚ^d / V`, both monic in `ℤ[x]`;
(b) every root of `χ̄` is 0 or a root of unity.

*Proof.* (a) `M p(u_S) = p(σ(u_S))` is the sum of the Parikh vectors of the
children of `S`, all in `C`. A rational invariant subspace splits `χ_M` into
monic rational factors, integral by Gauss's lemma.

(b) Let `Λ = max_S |u_S|`. By the concatenation lemma (Theorem A(2) of the
[cut-pair note](c4-cut-pair-productivity-2026-11-04.md)), every
`(σⁿ(u_S), σⁿ(v_S))` is a concatenation of members of `C`. Hence (i) every
cut prefix vector of `σⁿ(u_S)` is a sum of state Parikh vectors, so lies in
`V`; and (ii) every index of `σⁿ(u_S)` lies fewer than `Λ` letters after a
cut. Suppose `χ̄` has a root `α` with `|α| > 1`. The annihilator `V^⊥` is
invariant under `φ ↦ φM` and carries the spectrum of `χ̄`, so there is a
complex row `φ ≠ 0` with `φM = αφ` and `φ(V) = 0`. By (i) and (ii),
`|φ(y)| ≤ Λ max_a |φ(e_a)|` for every prefix vector `y` of every `σⁿ(u_S)`.
At the index `|σⁿ(u_S[:k])|` the prefix vector is `Mⁿ p(u_S[:k])`, with
`φ`-value `αⁿ φ(p(u_S[:k]))`; boundedness forces `φ(p(u_S[:k])) = 0` for all
`k`, hence `φ(e_a) = 0` for every letter of every state word. By primitivity
and the concatenation lemma every letter occurs in some state word, so
`φ = 0`, a contradiction. All roots of `χ̄` therefore lie in the closed unit
disc; `χ̄` is monic in `ℤ[x]`; Kronecker's theorem gives roots in
`{0} ∪ {roots of unity}`. ∎

**Corollary Q1.** If `M` has no eigenvalue that is 0 or a root of unity, then
every finite child-closed system has `V = ℚ^d`, i.e. `rank P = d`. For
irreducible `χ_M` on three letters this is already Proposition 2 of the
[Parikh-intertwiner note](c4-parikh-intertwiner.md) and PR #460, which use
irreducibility alone (no Pisot hypothesis); Proposition Q extends it to every
`M` without a neutral eigenvalue, on any alphabet.

A neutral quotient of the Parikh span is the only mechanism Proposition Q
detects. It accounts for the 27 strict-carrier classes with `rank P < 3`. It
does not account for the class of `01/2/120`, whose strict system has
`rank P = 3` and a trivial quotient although `χ_M = x²(x−2)` has the neutral
eigenvalue 0 inside `V`. For PIP the quotient is trivial, which is why
Proposition Q says nothing more there.

## 3. The defect spectrum for an irreducible cubic

Let `σ` be primitive on `{0,1,2}` with `χ_M` irreducible, roots `β`
(Perron), `α₂`, `α₃`. Let `C` be an ordered strict system, `N` its child
matrix, `P` its Parikh matrix, `K_r(S)` the degree-`r` scattered-subword
defect of a state, `D_r` the matrix of the `K_r`, and `r(C)` the least degree
at which some state has `K_r ≠ 0` (finite and at least 2, since states are
noncoincident and balanced).

**Lemma 0** ([lowest-defect intertwiner](c4-lowest-defect-intertwiner.md)).
At `r = r(C)`, `D_r N = M^{⊗r} D_r`; at `r = 2` this holds for every strict
system, with `W = Λ²M` in place of `M^{⊗2}`.

**R0.** `ρ(N) = β`: `L = ℓP > 0` and `L N = β L`.

**R1.** `Λ²M` is rationally similar to `det(M)·M^{−T}`, so `spec W = {det/β, det/α₂, det/α₃}` and `χ_W`
is irreducible and coprime to `χ_M`. If some state has `K₂ ≠ 0` then
`im D₂ = ℚ³`, the map `(P, D₂)` is onto `ℚ³ ⊕ Λ²ℚ³`, `|C| ≥ 6`, and
`χ_M χ_W | χ_N`.

*Proof.* A common root `α_i = α_j α_k` gives `α_k = 1` or `α_i² = det ∈ ℤ`,
both impossible. `im D₂` is a nonzero `W`-invariant rational subspace, so all
of `ℚ³`. If `D₂(ker P) = 0` then `D₂ = ΦP` with `ΦM = WΦ`, and coprimality
forces `Φ = 0`. The image of `(P, D₂)` is `(M ⊕ W)`-invariant and projects
onto both factors; applying `χ_W(M ⊕ W)` and `χ_M(M ⊕ W)` shows it contains
both summands. ∎

**Theorem R2.** If an irreducible-cubic substitution has a strict system with
a state of nonzero degree-two defect, then it is Pisot. Equivalently: for an
irreducible non-Pisot cubic, every strict system has `K₂ ≡ 0`.

*Proof.* By R1 the eigenvalues `βα₂, βα₃, α₂α₃` of `W` are eigenvalues of `N`,
so by R0 they have modulus at most `β`, giving `|α₂|, |α₃| ≤ 1`. Modulus
exactly 1 is impossible for a root of an irreducible cubic (a real root would
be `±1`; a complex pair on the circle gives `α₂α₃ = 1`, so `β = ±det ∈ ℤ`). ∎

**Theorem R3.** If both non-Perron roots of an irreducible cubic `χ_M` have
modulus greater than 1, then `σ` has **no strict system** (no restriction on
state lengths or legality).

*Proof.* Let `r = r(C)` and `V_r = im D_r ≠ 0`, an `M^{⊗r}`-invariant rational
subspace. `M` is diagonalisable, so the eigenvalues of `M^{⊗r}|V_r` are
monomials `β^a α₂^b α₃^c` with `a + b + c = r`; the characteristic polynomial
of the restriction is rational, so its roots form a union of Galois orbits,
and the Galois group acts transitively on the roots of `χ_M`. Each such
eigenvalue is an eigenvalue of `N` (Lemma 0 makes `V_r` a quotient
`N`-module), so has modulus at most `β`. Choose a conjugate that puts the
largest exponent `m ≥ 1` on `β`. If the other two exponents vanish, the
modulus is `β^r > β`. Otherwise it is `β^m |α₂|^x |α₃|^y > β^m ≥ β` with
`x + y ≥ 1`. Either way it exceeds `β`. ∎

**R3′** (one root outside, totally real). If `|α₂| > 1 > |α₃|`, then
`r(C) ∈ {3k, 3k+1}`, and `im D_r` lies in the sector of weight `(k,k,k)`
(where `M^{⊗r}` acts as `det^k`; admissible only if `|det|^k ≤ β`) or, for
`r = 3k+1`, of weight `(k+1,k,k)` (admissible only if `|det| = 1`).

*Proof.* Let `β^a α₂^b α₃^c` be an eigenvalue on `im D_r`, with the exponents
sorted as `x ≥ y ≥ z`. Since `|α₂α₃| = |det|/β ≥ 1/β`, putting `x` on `β`, `y`
on `α₂` and `z` on `α₃` gives modulus
`β^x |α₂|^y |α₃|^z = β^x |α₂|^{y−z} |α₂α₃|^z ≥ β^{x−z} |α₂|^{y−z}`. This
arrangement is in the Galois orbit when the group is `S₃`. When it is `ℤ/3`
and the orbit is the mirror one, the arrangement `y` on `β`, `x` on `α₂`, `z`
on `α₃` is in it, with modulus at least `β^{y−z} |α₂|^{x−z}`. Every orbit
member is an eigenvalue of `N`, hence of modulus at most `β`. Either bound
forces `x − z ≤ 1`, and `x − z = 1` forces `y = z`. So the weights are
`(k,k,k)` or `(k+1,k,k)`. The corresponding eigenvalues are `det^k` and
`det^k·{β, α₂, α₃}`; the bound `≤ β` gives the stated admissibility. ∎

**R5.** For a sink SCC `C′`, `χ_M` divides `χ_{N′}` exactly once; hence every
`N′`-equivariant map `ℚ^{C′} → (ℚ³, M)` equals `Φ∘P` with `Φ ∈ ℚ[M]`.

*Proof.* `N′` is nonnegative and irreducible with Perron root `β`, which is a
simple root of `χ_{N′}`. `P` is a surjective `N′`-equivariant map onto
`(ℚ³, M)`, so `χ_M | χ_{N′}`; since `χ_M` is irreducible with root `β`,
`χ_M² ∤ χ_{N′}`. The `χ_M`-primary component of `ℚ^{C′}` is therefore
three-dimensional, and `P` maps it isomorphically onto `ℚ³`. An equivariant
`φ` vanishes on the components with characteristic polynomials coprime to
`χ_M`, so `φ = Φ∘P` with `Φ` commuting with `M`. `M` is cyclic, so `Φ ∈ ℚ[M]`. ∎

**Consequence for the strengthening (H).** Call (H) the statement "a primitive
substitution on three letters with irreducible `χ_M` has no strict system" (no
Pisot hypothesis). Then

```text
(H)  ⟺  C4 for every PIP (unit or not)
        ∧  no strict system for irreducible totally real χ_M with exactly one non-Perron root outside the unit disc.
```

R3 settles the remaining class (two non-Perron roots outside, including every
irreducible complex non-Pisot cubic) completely, and R2 shows that degree-two
strict systems are a Pisot-only phenomenon.

## 4. Negative controls

- **Full Parikh rank is not an obstruction.** `01/2/120` (`χ_M = x²(x−2)`,
  `det 0`, `M²` of rank one) carries a 20-state ordered strict system with
  `rank P = 3`, lattice index 1 and `A(C)` all three pairs (all four pinned
  natively). So (H1) "every strict system has `rank P ≤ 2`" is false, and
  Corollary Q1's `rank P = 3` cannot by itself exclude a PIP strict system.
- **The degree-two identities are jointly satisfiable (scratch).** For
  Tribonacci `01/02/0` there is a packet with
  `N = [[A,B],[B,A]]`, `A = [[0,0,0],[0,0,0],[1,1,0]]`,
  `B = [[0,1,0],[0,1,1],[0,0,0]]`, `P = [P₊, P₊]` with columns
  `(0,1,1), (3,2,0), (2,0,1)` of `P₊`, and `D = [D₊, −D₊]` with
  `D₊ = [[0,1,0],[0,0,1],[−1,0,0]]` in the basis `(K₀₁, K₀₂, K₁₂)`. It is
  nonnegative, integral and irreducible, and satisfies `PN = MP`, `DN = WD`,
  `χ_N = χ_M χ_W`, `L = ℓP > 0`, `Dz = 0` for the positive Perron right vector
  `z` of `N`, and `|K_ab| ≤ p_a p_b` (scratch replay `verify_packet.py`). This
  shows only that those identities are jointly satisfiable. Tribonacci is a
  degenerate control: every image starts with `0`, so the first-letter map is
  constant and every balanced pair's first child is a coincidence, which
  Theorem A(3) already exploits. Independently, the column `(2,0,1)` with
  `K₂ = (0,1,0)` is the defect of no irreducible balanced pair (that Parikh
  vector admits only `(0,±2,0)`; on two letters an irreducible pair of length
  `n` has `|K_ab| ≥ n − 1`).
- **The branching route (A7), scratch only.** The earlier sketch and the proof
  of its repair exist only in scratch, not in the repository. The repaired
  statement A7′ (unit PIP; conditional on Barge–Kwapisz 2006 (7.2), Thm 5.3
  and Thm 7.3, with the coincidence rank of Baker–Barge–Kwapisz Def. 4.1) is:
  a one-track branching of a strict pair over a hub pair without a left
  strong-coincidence witness forces `cr ≥ 3`. Nothing forces that branching:
  on the reducible control `10/102/211` every branching is over the good edge.
  That control also carries Parikh-balanced certified strict *triples* (12 at
  level `Φ²`, 40 at `Φ⁴`, no 4-clique; physical sharing excluded to depth 7;
  scratch), so a contradiction could only come from the fibre bound, i.e. from
  `cr` itself. The claim that the two-track case never yields a triple is
  downgraded to "yields none certifiable by this method".

## 5. What general C4 now is

For PIP the linear and spectral facts proved here give no exclusion:

- Proposition Q is vacuous (`V = ℚ³`);
- if some state has `K₂ ≠ 0`, R1 forces `|C| ≥ 6` and the `(P, D₂)`
  direct-sum structure; otherwise only `|C| ≥ 3` (Corollary Q1);
- the orbit argument of R3/R3′, run with the Pisot inequalities
  `1/β < |α_j| < 1`, leaves the sectors of weight `(1,1,1)`, `(2,2,0)` and
  `(2,1,1)` at degrees 3–4, all compatible with Pisot;
- the identities in use are jointly satisfiable (the degenerate Tribonacci
  packet above).

What remains is word-level, and it is the same residual as before:
`C4(σ) ⟺ bounded-gap A1′ for every power of σ`
([cut-attractor note](c4-cut-attractor-window-2026-11-05.md), Proposition 3).
The two concrete next experiments are:

1. **Realisable degree-two packets.** For a PIP `M` whose first-letter map is
   not constant, search for an abstract packet with `PN = MP`, `D₂N = WD₂`,
   `N` irreducible nonnegative, satisfying the first-letter constraints of
   Theorem A(1),(3) and one-step noncoincident children, in which each column
   `(p_S, K₂(S))` is realised by an irreducible balanced pair. Absence for
   bounded `|C|` and bounded Parikh vectors would exclude small degree-two
   strict systems without building the balanced-pair automaton.
2. **The degree-three det-sector criterion.** For PIP, the orbit argument at
   degree 3 admits only weight `(1,1,1)`, where `M^{⊗3}` acts as `det`. So a
   state with `K₁ = K₂ = 0` whose `K₃` lies outside the two-dimensional
   `det`-eigenspace of `M^{⊗3}` on `Lie₃` lies in no degree-three strict
   system. Enumerating `K₂ = 0` pairs per PIP `M` tests whether any can
   satisfy the sector law.

## 6. The strict-system landscape (scratch evidence)

An exhaustive swap-seeded balanced-pair census was run over all 59,319
substitutions on `{0,1,2}` with images of length 1 to 3. It used a state cap
of 2,000 and a length cap of 20,000 letters, and a seed-independent bounded
search that is complete for state length up to 7. The census is a Python
computation, reproduced once independently; it is **not repository evidence**
until ported. Only the 28 class representatives below are pinned.

- 33,318 substitutions are primitive. Of these, 7,974 are productive, 276
  carry 294 strict systems (28 relabelling × reversal classes), and 25,068 are
  capped (all length-divergent, never a verdict).
- Every strict system has reducible `χ_M` with an eigenvalue 0 or a root of
  unity. So (H) holds on every decided specimen, and so does (H2): "the
  incidence matrix of a primitive substitution carrying a strict system has an
  eigenvalue 0 or a root of unity". Twelve systems, all in the class of
  `01/2/120`, have `rank P = 3`.
- No substitution outside the 276 carriers has a strict system with states of
  length at most 7. In particular none of the 7,176 irreducible non-Pisot ones
  does.
- 4,422 PIP corpus members are productive at the census caps. The other 132
  are length-capped there and productive on a re-run at 20,000 states and
  10⁶ letters (longest state 48,020 letters). This is consistent with
  `C4StandingCorpus`.

The 28 representatives, one strict system each, are pinned in
`kernel/tests/test_c4_quotient_spectrum.mojo`. Their ranks are 1, 2 and 3 in
10, 17 and 1 classes, and every quotient polynomial is a product of `x` and
cyclotomic factors.

## 7. Replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_quotient_spectrum.mojo)
python3 -m pytest -q tests/test_c4_quotient_spectrum_oracle.py
```

The Mojo module `kernel/psc/c4_quotient_spectrum.mojo` computes the quotient
polynomial with integers only:
- rank 1: `Mp = λp`, and the quotient is `χ_M / (x − λ)`;
- rank 2: the normal `n = p × q` satisfies `nM = μn`, and the quotient is
  `x − μ`;
- rank 3: the quotient is trivial.

It refuses any non-invariant span; the regression exercises all four reachable
refusal branches on hand-made non-closed systems and matches each refusal
message. A fifth guard (the Perron factor not dividing `χ_M`) is unreachable:
an integral eigenvalue of `M` is a root of `χ_M`. The oracle uses a different
construction: an exact rational change of basis and the quotient block, and
it decides neutrality by exact divisibility into `x²(x¹²−1)²` rather than by a
table. It builds its closures from scratch.

## 8. Non-claims

C4, BH, A1′, G1, PSC, SC_all; (H) beyond the class settled by R3; (H2) in
general (no mechanism is known; it holds on the decided domain only); any
statement about strict systems with states longer than the census bounds.

A two-letter non-Pisot family without strong coincidence, and a
constant-length form of (H2), were reported by an unaudited agent and are not
adopted here.

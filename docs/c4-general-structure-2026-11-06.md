# General C4: what a strict system forces, and where the Pisot property enters — 2026-11-06

**Status:** revised the same day after a prior-art audit (§9). Most of the
structural facts used here were already in the repository: the manuscript
`manuscripts/PSC_balanced_pair_state_2026-09-13.tex` (`thm:parikh`,
`thm:defect-intertwiner`, `thm:deg23`, `thm:sieve`, `prop:wedge-dichotomy`,
`sec:synthetic`) and the notes it rests on. They are cited where they are used.

New here, and repository-proved by written proofs (each re-derived by an
independent audit verifier; human review pending):
- Proposition Q(b), a neutral quotient spectrum for any finite child-closed
  system on any alphabet;
- Theorems R2 and R3 and the non-Pisot part of R3′, i.e. the manuscript's
  first-defect machinery run without the Pisot hypothesis, and their
  balanced-pair-algorithm consequence, Corollary B. Corollary B is
  literature-facing; at this revision its adversarial check (proof, prior
  art, attribution; workflow `wf_7fa1fcb8-25a`) is still in progress;
- R5 and the ordered refinement R1(c).

Proposition Q is calibrated by a canonical Mojo regression and an
independent oracle on 28 strict-carrier classes, on three letters only. The
landscape of §6 is scratch evidence. Nothing here changes the ledger node C4,
BH (#139), A1′ (#138), G1 or PSC.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline: branch `ccr-5059e568-lh2509` at `8d97d7d` (PR #499).

**Conventions.** The children of an ordered balanced pair `(u,v)` are the
irreducible factors of `(σ(u), σ(v))`, with the top word taken from `σ(u)`. A
set `C` of ordered balanced pairs is **child-closed** if it contains every
child of each member. Coincidences `(a,a)` count as members, so a
child-closed set may contain them. A **strict system** is a finite nonempty
child-closed set of irreducible pairs with no coincidence. It is the ordered
lift of the manuscript's *strict component*, a finite closed nonproductive
recurrent noncoincident SCC on normalized states (manuscript §5.1). A
normalized component of `m` states lifts to `m` ordered states when its
orientation cocycle is gauge-trivial, and to `2m` (the oriented double cover)
otherwise; see manuscript `prop:cocycle` and the
[orientation monodromy](c4-orientation-monodromy.md) note. Strict systems
need not be reachable or legal. On ordered pairs the child matrix `N` is
unsigned. The manuscript's signed identities `Q_r S = Φ_r Q_r` then read
`D_r N = M^{⊗r} D_r`, and the spectrum of `N` contains that of `S`
([orientation spectrum](c4-orientation-spectrum.md)).

**NS(σ)** is the statement "σ has no strict system". "General C4" in this
note means NS for every primitive irreducible Pisot (PIP) substitution on
three letters. NS(σ) implies the ledger node C4 for σ vacuously (every strict
component has a one-step interior synchronizing zero return). As stated, it
is stronger, because it imposes no reachability. The standing corpus is done
([finite-domain closure](c4-finite-domain-closure-2026-11-05.md)).

## 1. Stop/go literature check (revised)

The first version of this section examined Proposition Q only. The audit of
§9 found that incomplete under the repository's stop/go rule. The prior art
is as follows.

- **Repository manuscript (2026-09-13).**
  - `thm:parikh`: `PN = MP`, `rank P = d`, `|C| ≥ d`, `χ_M | χ_N`,
    `ρ(N) = β`, for irreducible `χ_M` on any `d`.
  - `lem:descendants` and `lem:return-gap`: uniform return gaps, with no
    Pisot hypothesis.
  - `thm:defect-intertwiner`: `Q_r S = Φ_r Q_r`, `K_r ∈ Lie_r`, `ρ ≤ β` on
    `im Q_r`.
  - `thm:deg23`: (i) `χ_{Λ²M}` is irreducible. (ii) `r = 2` gives
    `rank Q₂ = 3`, `χ_{Λ²M} | χ_S` and a mod-2 size floor in `{3,…,6}`.
    (iii) `r = 3` gives `im Q₃ ⊆ ker(Φ₃ − det M)`, a two-dimensional space.
  - `thm:sieve`: the Galois-orbit, log-modulus sieve at every degree, for PIP.
  - `prop:wedge-dichotomy` and `prop:v34`.
  - `ex:nonpisot`: a reducible non-Pisot strict component, class `1/012/1`.
  - `sec:synthetic`: a three-state system for a PIP, on realised states. It
    satisfies the Parikh, signed degree-two and endpoint constraints and is
    rejected only by the order-sensitive mid-area identity.
  - `thm:global-sync`, and the open problems Concentration and Wedge
    productivity.
- **Repository notes and ledger.**
  - [Parikh intertwiner](c4-parikh-intertwiner.md), Propositions 1–4.
  - The [cut-pair note](c4-cut-pair-productivity-2026-11-04.md), where R0 is
    stated for strict systems.
  - [Lowest-defect intertwiner](c4-lowest-defect-intertwiner.md) §§2–6.
  - [Multidegree spectral sieve](c4-multidegree-spectral-sieve.md) (`Mod3Sieve`).
  - [Degree four](c4-degree4-free-lie.md) (`Degree4Floor`).
  - [W₃ low growth](c4-w3-low-growth-and-interface-correction.md) (`W3LowGrowth`).
  - [P1-A degree three](p1a-degree3-partial-theorem.md) (`BoundedDegree3Exclusion`).
  - [Degree-two synthetic realizability](c4-degree2-synthetic-realizability.md).
  - `archive/2026-09-08/certificates_patched/PROOF_CERTIFICATE.md` §§3, 5 and
    8–10: `Lie₃ ≅ sl(V) ⊗ det` and `Φ₃ = det(M)·Ad_M`, with ledger nodes
    `PhiSemisimplicity` and `ThetaIntertwining`.
- **Literature.**
  - Sirvent–Solomyak 2002 (Canad. Math. Bull. 45), §3. It defines `bpa-W` and
    says "the bpa-W terminates if `I(W)` is finite". Remark 2 after Theorem
    3.1 reads: "it seems that if the characteristic polynomial of the
    substitution matrix is irreducible and the Perron-Frobenius eigenvalue is
    not Pisot, then ζ does not have pure discrete spectrum and the bpa does not
    terminate. We do not know if these claims have been proved in full
    generality". It cites partial spectral results, Solomyak 1992 and
    Ferenczi–Mauduit–Nogueira 1996.
  - Adamczewski 2003 (Theoret. Comput. Sci. 307), Theorem 13 and Corollaries
    15 and 17: bounded discrepancy against the eigenvalues of `M`, with a 0 /
    root-of-unity conclusion.
  - Martensen 2004 (Topology Proc. 28): the balanced-pair algorithm in the
    reducible case, with root-of-unity eigenspaces as the obstruction to
    termination (stated as a hope).
  - Baker–Barge–Kwapisz 2006 Theorem 4.2: fibres are finite-to-one, so fibre
    cardinality is not a lever.
  - Barge–Štimac–Williams 2013: the branching contradiction needs the
    hub / A1′ input.
  - Barge–Diamond 2007 Theorem 4.5 (reported by the audit). For strong Pisot,
    GCC holds iff every balanced pair terminates with coincidence, iff the
    flow has pure discrete spectrum. So NS for *legal* pairs of a PIP follows
    from PSC; it rests on Barge–Kwapisz 2006, and Barge–Štimac–Williams
    report a gap there.

**Decision: proceed, narrowed** to Proposition Q(b), R2, R3, the non-Pisot
part of R3′, Corollary B, R5 and R1(c), with every other fact attributed.
Both experiments proposed in the first version of §5 are withdrawn (§5).

## 2. Proposition Q (any alphabet, any primitive substitution)

**Proposition Q.** Let `σ` be a primitive nonerasing substitution on `d`
letters with incidence `M`, and `C` a finite nonempty child-closed set of
balanced pairs (coincidences admitted; strictness is not needed). Let
`V = span_ℚ{p(u_S) : S ∈ C}`. Then:

(a) `V` is `M`-invariant, so `χ_M = χ_{M|V} · χ̄`, where `χ̄` is the
characteristic polynomial of `M` on `ℚ^d / V`, and both factors are monic in
`ℤ[x]`;

(b) every root of `χ̄` is 0 or a root of unity.

Closure under *all* children is essential. Under the manuscript's
`closed`, coincidence children may lie outside `C`. For such a set, (a) fails:
closed productive SCCs with `ρ(N) < β` exist (remark after `thm:parikh`),
which `PN = MP` and `L = ℓP > 0` would forbid.

*Proof.* (a) `M p(u_S) = p(σ(u_S))` is the sum of the Parikh vectors of the
children of `S`, all in `C`. A rational invariant subspace splits `χ_M` into
monic rational factors, which are integral by Gauss's lemma.

(b) Let `Λ = max_S |u_S|`. Every `(σⁿ(u_S), σⁿ(v_S))` is a concatenation of
members of `C`. This is manuscript `lem:descendants`, also Theorem A(2) of the
[cut-pair note](c4-cut-pair-productivity-2026-11-04.md). Hence:
- (i) every cut prefix vector of `σⁿ(u_S)` is a sum of state Parikh vectors,
  so it lies in `V`;
- (ii) every index of `σⁿ(u_S)` lies fewer than `Λ` letters after a cut
  (manuscript `lem:return-gap`, no Pisot hypothesis).

Suppose `χ̄` has a root `α` with `|α| > 1`. The annihilator `V^⊥` is invariant
under `φ ↦ φM` and carries the spectrum of `χ̄`, so there is a complex row
`φ ≠ 0` with `φM = αφ` and `φ(V) = 0`. By (i) and (ii),
`|φ(y)| ≤ Λ max_a |φ(e_a)|` for every prefix vector `y` of every `σⁿ(u_S)`.
At the index `|σⁿ(u_S[:k])|` the prefix vector is `Mⁿ p(u_S[:k])`, with
`φ`-value `αⁿ φ(p(u_S[:k]))`. Boundedness forces `φ(p(u_S[:k])) = 0` for all
`k`, hence `φ(e_a) = 0` for every letter of every state word. By primitivity
and the concatenation lemma every letter occurs in some state word, so
`φ = 0`, a contradiction.

All roots of `χ̄` therefore lie in the closed unit disc. Since `χ̄` is monic in
`ℤ[x]`, Kronecker's theorem puts its roots in `{0} ∪ {roots of unity}`. ∎

*Attribution.* Part (a) is the Parikh intertwiner, restated for any finite
child-closed set. It appears in manuscript `thm:parikh` (proof),
Proposition 1 of the [Parikh-intertwiner note](c4-parikh-intertwiner.md), and
archived v15 Lemma `alg-structure`(i). Its integral rank-two form is §3 of
the [complete-cone audit](c4-complete-cone-rank-hub-audit-2026-11-03.md).

The technique of (b) is Adamczewski's: bounded discrepancy excludes expanding
eigendirections, and Kronecker's theorem then gives roots of unity. His
Corollary 17 reaches the same 0-or-root-of-unity conclusion for eventually
periodic fixed points. New here is conclusion (b) for the Parikh span of a
finite child-closed balanced-pair system, on any alphabet, with neither
irreducibility nor Pisot. The executable calibration covers `d = 3` only.

**Corollary Q1.** If `M` has no eigenvalue that is 0 or a root of unity, then
every finite child-closed system has `V = ℚ^d`, i.e. `rank P = d`.

The irreducible case holds on any alphabet and is already in four places:
manuscript `thm:parikh`, archived v15 Lemma `alg-structure`(ii), Proposition 2
of the [Parikh-intertwiner note](c4-parikh-intertwiner.md), and PR #460. All
use irreducibility only. Q1 is new only for reducible `M` without a neutral
eigenvalue. On three letters that is a rational root outside `{0, ±1}`.

A neutral quotient of the Parikh span is the only mechanism Proposition Q
detects. Its first recorded instances are manuscript `ex:nonpisot` (quotient
`x + 1`) and the rank-two control `10/102/211`
([two-generation Parikh span](c4-two-generation-parikh-span-2026-11-02.md)).
It accounts for the 27 strict-carrier classes with `rank P < 3`. It does not
account for the class of `01/2/120`, whose strict system has `rank P = 3` and
a trivial quotient although `χ_M = x²(x−2)` has the neutral eigenvalue 0
inside `V`. For PIP the quotient is trivial.

## 3. The defect spectrum for an irreducible cubic

Let `σ` be primitive on `{0,1,2}` with `χ_M` irreducible, with roots `β`
(Perron), `α₂` and `α₃`. Let `C` be a finite child-closed set of ordered
balanced pairs (coincidences admitted), `N` its unsigned child matrix and
`P` its Parikh matrix. Let `K_r(S)` be the degree-`r` scattered-subword
defect of a state and `D_r` the matrix of the `K_r`.

Let `r(C)` be the least degree at which some state has `K_r ≠ 0`. If `C`
contains a noncoincident pair `(u,v)`, then `2 ≤ r(C) ≤ |u|`: the word `u`
occurs once in `u` as a scattered subword and not in `v ≠ u`. Coincidences
have `K_r ≡ 0`.

**Lemma 0** (manuscript `thm:defect-intertwiner`;
[lowest-defect intertwiner](c4-lowest-defect-intertwiner.md) §§2–4). At
`r = r(C)`, `D_r N = M^{⊗r} D_r` and every `K_r(S)` lies in `Lie_r(ℚ³)`. At
`r = 2` this holds for every such `C`, with `W = Λ²M`.

On ordered pairs no signs occur. The children concatenate on both tracks with
equal lower defects, so the cross terms cancel. Only the lower-defect vanishing
is used, which is why coincidences may be members.

**R0** (prior: [cut-pair note](c4-cut-pair-productivity-2026-11-04.md),
manuscript `thm:parikh`, Parikh-intertwiner Proposition 4). `ρ(N) = β`. The
vector `L = ℓP` is strictly positive and `LN = βL`. For a nonnegative `N` that
need not be irreducible, the `L`-weighted `ℓ¹` norm gives `ρ(N) ≤ β`, and `β`
is an eigenvalue.

**R1.** (a) and (b) are prior: manuscript `thm:deg23`(i)–(ii) and
`prop:wedge-dichotomy`. Coprimality with `χ_M` is the Sylvester remark after
`prop:midarea`.
- (a) `Λ²M` is rationally similar to `det(M)·M^{−T}`, so
  `spec W = {det/β, det/α₂, det/α₃}`; `χ_W` is irreducible and coprime to
  `χ_M`.
- (b) If some state has `K₂ ≠ 0`, then `im D₂ = ℚ³`.
- (c) *New, for ordered systems.* If moreover `C` is a strict system, then
  `D₂(ker P) = ℚ³`. The map `(P, D₂)` is onto `ℚ³ ⊕ Λ²ℚ³`, so
  `|C| ≥ 6` *ordered* states and `χ_M χ_W | χ_N`.

For a normalized component of `m` states, the double-cover case of (c) gives
only `m ≥ 3`, which is the orientation-spectrum fact. The gauge-trivial case
gives `m ≥ 6`, which sharpens the manuscript's mod-2 floor.

*Proof of (c).* `P` is onto by Corollary Q1. `ker P` is `N`-invariant because
`PN = MP`, so `D₂(ker P)` is a `W`-invariant rational subspace. If it were 0,
then `D₂ = ΦP` with `ΦM = WΦ`, and coprimality would force `Φ = 0`,
contradicting (b). So `D₂(ker P) = ℚ³` by irreducibility of `χ_W`. The image
of `(P, D₂)` therefore contains `0 ⊕ ℚ³` and projects onto `ℚ³`, so it is
everything. Then `ℚ^C / ker(P, D₂) ≅ (ℚ³ ⊕ ℚ³, M ⊕ W)` as `N`-modules. ∎

**Theorem R2.** If some finite child-closed set `C` (coincidences admitted)
contains a pair with `K₂ ≠ 0`, then `χ_M` is Pisot. In particular, for an
irreducible non-Pisot cubic every strict system has `K₂ ≡ 0`.

*Proof.* By Lemma 0 at `r = 2` and R1(b), `ℚ³ = im D₂ ≅ ℚ^C / ker D₂` as
`N`-modules. So the eigenvalues `βα₂`, `βα₃`, `α₂α₃` of `W` are eigenvalues of
`N`, and by R0 they have modulus at most `β`, giving `|α₂|, |α₃| ≤ 1`. Modulus
exactly 1 is impossible for a root of an irreducible cubic: a real root would
be `±1`, and a complex pair on the circle gives `α₂α₃ = 1`, so `β = ±det ∈ ℤ`. ∎

*Attribution.* R2 is a corollary of the manuscript's chain
`thm:defect-intertwiner` + `thm:deg23`(i)–(ii) + `thm:parikh`, whose proofs
use irreducibility only. An equivalent route is `prop:wedge-dichotomy` +
`prop:v34`. The manuscript ran the chain under PIP, where it "yields no
contradiction". New is the observation that without Pisot it forces
`|α_j| ≤ 1`, together with the exclusion of `|α_j| = 1`. Irreducibility is
necessary: `ex:nonpisot` (`χ_M = x(x−2)(x+1)`) is a strict system with
`K₂ ≠ 0`. Among irreducible cubics, then, strict systems of first defect
degree two occur only for Pisot.

**Theorem R3.** If both non-Perron roots of an irreducible cubic `χ_M` have
modulus greater than 1, then no finite child-closed set of balanced pairs
contains a noncoincident pair. In particular `σ` has no strict system, with
no restriction on state lengths or legality.

*Proof.* Suppose `C` contains one. Let `r = r(C)` and `V_r = im D_r ≠ 0`, an
`M^{⊗r}`-invariant rational subspace. The eigenvalues of `M^{⊗r}|V_r` are
monomials `β^a α₂^b α₃^c` with `a + b + c = r`. The characteristic polynomial
of the restriction is rational, so its roots form a union of Galois orbits,
and the Galois group acts transitively on the roots of `χ_M`. Lemma 0 makes
`V_r` a quotient `N`-module, so each such eigenvalue is an eigenvalue of `N`
and has modulus at most `β` (R0).

Choose a conjugate that puts the largest exponent `m ≥ 1` on `β`. If the other
two exponents vanish, the modulus is `β^r > β`. Otherwise it is
`β^m |α₂|^x |α₃|^y > β^m ≥ β` with `x + y ≥ 1`. Either way it exceeds `β`. ∎

*Attribution.* The method is the Galois-orbit modulus comparison of manuscript
`thm:sieve` and `thm:deg23`(iii) and the
[multidegree sieve](c4-multidegree-spectral-sieve.md). Those sources run it
only in the PIP cone. New is its application to this class, where no weight
survives at any degree, and the observation that strictness is not used.

**Corollary B (the balanced pair algorithm off the Pisot cone).** Let `σ` be
primitive on three letters with irreducible, non-Pisot `χ_M`.
- (i) If both non-Perron roots lie outside the closed unit disc, the child
  closure of every noncoincident balanced pair is infinite. In particular,
  for every prefix `W` of a fixed point, the `bpa-W` of Sirvent–Solomyak does
  not terminate.
- (ii) In all cases, the child closure of any balanced pair with `K₂ ≠ 0` is
  infinite. Examples are the swap pairs `(ab, ba)`, which seed the
  manuscript's automaton `B_σ`, so `B_σ` is infinite. A terminating `bpa-W`
  has `K₂ ≡ 0` on `I(W)`, and `r(I(W))` obeys R3′.

*Proof.* `I(W)` contains every irreducible subpair that arises, coincidences
included (Sirvent–Solomyak §3: coincidences "need not be in `I(W)`, but if
they are …"), so it is child-closed. The fixed point `u` is not eventually
periodic, because its letter frequencies span a cubic field. Hence
`[u, S^{|W|}u]` has a noncoincident irreducible factor in `I₁(W)`. Apply R3
for (i). For (ii), apply R2 to the closure, noting `K₂(ab, ba) ≠ 0`. ∎

This proves the *non-termination* half of Sirvent–Solomyak's Remark 2 in case
(i) on three letters. In case (ii) it proves non-termination only for seeds
with `K₂ ≠ 0`. It does not reach prefix seeds in the one-outside class, nor
the spectral half of the remark. We found no proof of these statements in the
sources of §1; the partial results that Sirvent–Solomyak cite concern the
spectrum. Among irreducible cubics, (ii) also calibrates the finiteness
hypothesis G1: `B_σ` can be finite only in the Pisot case.

**R3′** (exactly one non-Perron root outside the unit disc). Let
`|α₂| > 1 > |α₃|`; then both roots are real, since a complex pair has equal
moduli. Then `r(C) ≢ 2 (mod 3)`. For `r = 3k` every eigenvalue of `M^{⊗r}`
on `im D_r` equals `det^k`, admissible only if `|det|^k ≤ β`. For `r = 3k+1`
it lies in `det^k·{β, α₂, α₃}`, admissible only if `|det| = 1`.

*Proof.* Let `β^a α₂^b α₃^c` be an eigenvalue on `im D_r`, with the exponents
sorted as `x ≥ y ≥ z`. Each orbit member is an eigenvalue of `N`, hence of
modulus at most `β`. Since `|α₂α₃| = |det|/β ≥ 1/β`, two arrangements give
lower bounds:
- (1) `x` on `β`, `y` on `α₂`, `z` on `α₃`:
  `β^x |α₂|^{y−z} |α₂α₃|^z ≥ β^{x−z}|α₂|^{y−z}`;
- (2) `y` on `β`, `x` on `α₂`, `z` on `α₃`: at least `β^{y−z}|α₂|^{x−z}`.

Bound (1) at most `β` forces `y = z`, since otherwise `x − z ≥ 1` and
`|α₂| > 1`; then it forces `x − z ≤ 1`. Bound (2) at most `β` forces `y = z`
and nothing more.

Whenever two exponents are equal, all distinct arrangements form a single
orbit, which contains arrangement (1). If the group is `S₃`, every orbit
contains (1). If it is `ℤ/3` and `x > y > z`, the six arrangements split into
the rotations of (1) and the rotations of (2). In the first orbit, bound (1)
forces `y = z`; in the second, bound (2) does. Either contradicts `y > z`.

So the weight is `(k,k,k)` or `(k+1,k,k)`, with eigenvalues `det^k` and
`det^k·{β, α₂, α₃}`, and the bound `≤ β` gives the stated admissibility. Which
of these weights occur in `Lie_r` is given by the generalized Witt formula
(manuscript, proof of `thm:sieve`). ∎

For PIP the same argument is the manuscript's `thm:sieve`, with the sharper
degree-3/4 list of `thm:deg23`(iii) and `Degree4Floor`. Only the one-outside
specialization above is new.

**R5.** Let `C′` be a sink SCC of the child graph of a strict system, so `C′`
is itself child-closed. Then `χ_M` divides `χ_{N′}` exactly once, and every
`N′`-equivariant map `ℚ^{C′} → (ℚ³, M)` equals `Φ∘P` with `Φ ∈ ℚ[M]`.

*Proof.* `N′` is nonnegative and irreducible with `ρ(N′) = β` (R0). The Perron
root is a simple root of `χ_{N′}`. `P` is onto by Corollary Q1, so
`χ_M | χ_{N′}` (manuscript `thm:parikh`), and since `χ_M` is irreducible with
root `β`, `χ_M² ∤ χ_{N′}`. An equivariant map into `(ℚ³, M)` kills every
primary component of `ℚ^{C′}` for a factor coprime to `χ_M`, because its image
would be a primary part of `(ℚ³, M)` for a coprime polynomial. So `P` maps the
three-dimensional `χ_M`-primary component isomorphically onto `ℚ³`, and any
equivariant `φ` factors as `Φ∘P` with `Φ` commuting with `M`. `M` is cyclic,
so `Φ ∈ ℚ[M]` (the rational centralizer, recorded in the W₃ note §3). The
statement can fail for the whole `N` when there are several sinks. ∎

**The strengthening (H).** Call (H) the statement "a primitive substitution on
three letters with irreducible `χ_M` has no strict system" (no Pisot
hypothesis). An irreducible cubic has no root on the unit circle, so its
non-Perron roots are both inside (PIP), both outside, or straddle the circle
(then real). Hence

```text
(H)  ⟺  NS for every PIP (unit or not)
        ∧  NS for every irreducible χ_M with exactly one non-Perron root outside the unit disc.
```

R3 decides the remaining class, which includes every irreducible complex
non-Pisot cubic. No prior statement of (H) or of this split was found; the
only published expectation nearby is Sirvent–Solomyak's Remark 2, which
concerns non-termination and spectrum.

## 4. Negative controls

- **Full Parikh rank does not exclude strictness (calibration).** The
  algebraic form is the manuscript's retired route (iii): `N = M`, `P = I`
  satisfies every identity of `thm:parikh`. `01/2/120` (`χ_M = x²(x−2)`,
  `det 0`) is a realised specimen. It carries a 20-state ordered strict system
  with `rank P = 3`, lattice index 1, and `A(C)` containing all three pairs;
  all four facts are pinned natively. It is singular and reducible, so it says
  nothing about PIP. No repository source asserted `rank P ≤ 2`, and the
  complete-cone audit explicitly declined to.
- **The Tribonacci packet (scratch; superseded).** The first version recorded
  a six-state ordered packet for `01/02/0`. It has `N = [[A,B],[B,A]]`,
  `A = [[0,0,0],[0,0,0],[1,1,0]]` and `B = [[0,1,0],[0,1,1],[0,0,0]]`. Its
  `P₊` has columns `(0,1,1), (3,2,0), (2,0,1)`, and
  `D₊ = [[0,1,0],[0,0,1],[−1,0,0]]` in the basis `(K₀₁, K₀₂, K₁₂)`. It
  satisfies `PN = MP`, `DN = WD`, `χ_N = χ_M χ_W` and `L > 0`; an audit
  verifier replayed this. It is strictly weaker than the manuscript's
  synthetic template, for three reasons:
  - it is excluded outright by `thm:global-sync`, since every image starts
    with `0`;
  - its column `(2,0,1)` with `K₂ = (0,1,0)` is realised by no irreducible
    pair, which admits only `(0,±2,0)`;
  - its column `(3,2,0)` with `K₂ = (1,0,0)` is not realised either, which
    admits only `(±4,0,0)`, `(±5,0,0)` and `(±6,0,0)`.

  It is kept as a record only.
- **The branching route (A7), scratch only.** The question whether a branching
  over a cut pair forces `cr ≥ 3` was posed in the
  [cut-attractor note](c4-cut-attractor-window-2026-11-05.md) §8. The repaired
  statement A7′ is conditional and exists only in scratch. It concerns unit
  PIP and depends on Barge–Kwapisz 2006 (7.2), Thm 5.3 and Thm 7.3, with the
  coincidence rank of Baker–Barge–Kwapisz Def. 4.1. It says that a one-track
  branching of a strict pair over a hub pair without a left strong-coincidence
  witness forces `cr ≥ 3`.

  Nothing forces that branching on the reducible control `10/102/211`, which
  lies outside the hypothesis class. That control also carries
  Parikh-balanced certified, not physical, strict triples (12 at `Φ²`, 40 at
  `Φ⁴`, no 4-clique; scratch). That we see no source of contradiction in
  this route other than `cr` itself is a heuristic, not a derivation.

## 5. What general C4 now is

For PIP every linear and spectral fact in play is already in the manuscript:
- `rank P = 3`, `|C| ≥ 3` and `χ_M | χ_N` (`thm:parikh`);
- at `r = 2`, `rank Q₂ = 3` and the mod-2 floor (`thm:deg23`(ii)). R1(c)
  refines this to at least 6 ordered states, i.e. at least 6 normalized states
  for a gauge-trivial component;
- at `r = 3`, the det-sector (`thm:deg23`(iii)), excluded on the corpus by
  `BoundedDegree3Exclusion`;
- at `r = 4`, `|det M| = 1` and `ρ(S) = β` (`thm:sieve`, `Degree4Floor`), so
  first-degree-four strict systems are excluded for every non-unimodular PIP;
- at `r ≥ 5`, the sieve shapes.

The synthetic template shows that the Parikh, signed degree-two and endpoint
constraints are jointly satisfiable on realised states for a PIP; it is
rejected only by the mid-area identity. The manuscript's conclusion stands:
no invariant coarser than the factorization itself closes the problem. What
remains is Open Problems Concentration and Wedge productivity, which together
are NS for PIP split by first defect degree. Equivalently,
`NS(σ) ⟺ bounded-gap A1′ for every power of σ`
([cut-attractor note](c4-cut-attractor-window-2026-11-05.md), Proposition 3).

**Withdrawn experiments.**

1. *Realisable degree-two packets.* Already answered: manuscript
   `sec:synthetic`, [synthetic realizability](c4-degree2-synthetic-realizability.md)
   (three normalized states, realised columns, non-degenerate endpoints), and
   `comp:threestate`. Of the corpus substitutions, 546 pass the three
   necessary conditions for a three-state component, and none has a
   three-state recurrent SCC. The proposed filters were weaker than
   the existing pipeline: type-G exclusion, mid-area identity, mean-area
   integrality, lattice lift and side-area parity. Checking one-step children
   needs the state words anyway.
2. *The degree-three det-sector criterion.* Already a theorem
   (`thm:deg23`(iii), `W3LowGrowth`). It is implemented in centralizer form
   `[M, Θ(K₃)] = 0` and run on every reachable degree-3 corpus state
   (`BoundedDegree3Exclusion`), and on the six length-7 seeds for every PIP
   `M` (`Target1`). Lean `Psc.target1` also supplies an `M`-independent
   prefilter: `Θ(K₃)` with a rational eigenvalue commutes with no PIP `M`.
   Testing unreachable `K₂ = 0` pairs is already the remaining task of the
   W₃ note §7, and without a length cap it has no finite domain.

**What this note adds off the Pisot cone.** The only open non-Pisot class of
(H) is the one-outside class. There a strict system, or a terminating
`bpa-W`, must have `K₂ ≡ 0` and first defect degree `≢ 2 (mod 3)`, with the
eigenvalues of R3′. The scratch landscape (§6) found no strict system there
with all states of length at most 7.

## 6. The strict-system landscape (scratch evidence)

An exhaustive swap-seeded balanced-pair census was run over all 59,319
substitutions on `{0,1,2}` with images of length 1 to 3. It used a state cap
of 2,000, a length cap of 20,000 letters, and a seed-independent bounded
search complete for systems all of whose states have length at most 7. The
census is a Python computation, reproduced once independently, and is **not
repository evidence** until ported. Only the 28 class representatives below
are pinned. An audit verifier reproduced the primitive, PIP and non-Pisot
counts, the 28 representatives, and the 276 carriers as the union of their
orbits; the other counts are unverified.

- 33,318 substitutions are primitive. Of these, 7,974 are productive, 276
  carry 294 strict systems (28 relabelling × reversal classes), and 25,068 are
  capped (never a verdict).
- Every strict system has reducible `χ_M` with an eigenvalue 0 or a root of
  unity. So (H) holds on every decided specimen, and so does the observation
  **(N0)**: "the incidence matrix of a primitive substitution carrying a strict
  system has an eigenvalue 0 or a root of unity". (N0) was called "(H2)" in
  the first version, which collides with the manuscript's hypothesis `H2`.
  Manuscript `ex:nonpisot` is the first recorded instance, class `1/012/1`.
  Twelve systems, all in the class of `01/2/120`, have `rank P = 3`.
- No substitution outside the 276 carriers has a strict system all of whose
  states have length at most 7. In particular none of the 7,176 irreducible
  non-Pisot ones does.
- 4,422 PIP corpus members are productive at these caps. The other 132 are
  length-capped there and productive on a re-run at 20,000 states and 10⁶
  letters (longest state 48,020 letters). The canonical PIP statement is the
  manuscript's `comp:bpa`, under different caps, and `C4StandingCorpus`.

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

It refuses any non-invariant span. The regression exercises all four reachable
refusal branches on hand-made non-closed systems and matches each refusal
message. A fifth guard (the Perron factor not dividing `χ_M`) is unreachable,
because an integral eigenvalue of `M` is a root of `χ_M`. The oracle uses a
different construction, an exact rational change of basis and the quotient
block. It decides neutrality by exact divisibility into `x²(x¹²−1)²` rather
than by a table, and builds its closures from scratch. Theorems R2 and R3 and
Corollary B rest on their written proofs; no executable claim is made for
them.

## 8. Non-claims

The following are not claimed: NS for PIP (general C4), the ledger node C4,
BH, A1′, G1, PSC and SC_all. Nor is (H) beyond the class decided by R3, or
Corollary B for prefix seeds in the one-outside class. The spectral half of
Sirvent–Solomyak's Remark 2 is not claimed, and neither is (N0) in general
(no mechanism is known; it holds on the decided domain only). Nothing is
claimed about strict systems with states longer than the census bounds.

A two-letter non-Pisot family without strong coincidence, and a
constant-length form of (N0), were reported by an unaudited agent and are not
adopted here.

## 9. Revision record

The first version (`5650f70`, with review fixes in `bc84f30`) was audited for
prior art by a nine-agent workflow, `wf_6920b8a8-85f`. Five source-partitioned
sweeps covered the manuscripts, two halves of `docs/`, the formal and archived
layers, and the literature. Four adversarial verifiers re-opened every cited
source and re-derived the proofs. Its scratch replays are in the session
scratchpad. Changes:

- **Attribution.**
  - R0, Lemma 0, R1(a)–(b), Q(a), the irreducible case of Q1 (on any
    alphabet), the Pisot sector list and the degree-3 det-sector are prior,
    and are now cited.
  - The first version presented them as derived here and equated ordered
    strict systems with the manuscript's components.
  - The §1 check covered Proposition Q only.
- **Scope.**
  - R1's `|C| ≥ 6` counts ordered states. Read on normalized components it
    contradicted `thm:deg23`(ii).
  - R2 and R3 are stated without strictness, which yields Corollary B.
- **Proofs.**
  - R1(c) now proves `D₂(ker P) = ℚ³`; the first version proved only that it
    is nonzero.
  - The `ℤ/3` case of R3′ is written out; the claim "either bound forces
    `x − z ≤ 1`" was false for bound (2) alone.
  - Lemma 0 now records `K_r ∈ Lie_r`, which the degree-3 count needs.
  - Proposition Q now defines child-closed.
- **Withdrawn.**
  - Both §5 experiments, which were already answered.
  - The claim that the Pisot sectors "give no exclusion"; degree 4 does
    exclude non-unimodular PIP.
  - "(H1) is false", reframed as a calibration.
- **Renamed.** "(H2)" is now (N0).

# Lateral generalization of the scoped closures (2026-10-23)

**Status:** strategy note plus the stop/go and result of its first move.
The move-1 proposition (§2) is derived from an already-imported invariance and
a hand proof, and is checked by an exact bounded Mojo census. No ledger node,
manuscript statement or claim status changes. Independent human review is
pending for everything here, as for the Theorem C, Theorem S and Theorem B
inputs it uses. Companion to the
[direct-attack frontier](direct-attack-frontier-2026-10-23.md).

## 1. The strategy: relax one load-bearing hypothesis at a time

*Lateral* means moving a certified piece (a family, an engine or a lemma) to
neighbouring territory. The move names the one hypothesis the piece really
uses and relaxes it. None of these moves is the universal step; their purpose
is to shrink the territory where universal BH and A1′ must do new work.

| Engine | Load-bearing hypothesis |
| --- | --- |
| constant-graph cones (Theorems L, L′, L″, C, W) | constant labels on a cone; Perron signs as polynomials in `h` |
| residue-ray carriers (A `d≤4`, C `d≤5`) | with `n = d l + r`, labels affine in `l` |
| occurrence templates (class D) | symbolic run-index lifts with an exact legality interval |
| parametric witness paths (Theorems E, H, K) | one affine check proves a shared tile on a cone |
| Lemma P / Proposition P′ | catch-up-free; P′ (level = M-adic valuation) holds for every `|det M| ≥ 2` |

Lemma P's simultaneous-birth corollary needs only that every proper prefix
lies in **one coset** of `Λ = M Z³`. For `|det M| = 2` this is automatic
(Proposition C). It is a weaker requirement than determinant two itself.

The ranked moves are listed below; each needs its own stop/go note.

1. **Conjugacy, power and symmetry transfer.** This move is done; §2 gives the
   result.
2. **Make the gap a parameter for A and C, then port to the class-B top
   layer.** Along `p = 3q + 11 − d`, B's top layer grows linearly in `q`,
   which is the class-A slope-one behaviour that residue rays handle.
3. **A single compiler for run-affine families.** All four engines consume
   images that are fixed letters interleaved with runs of affine length.
   Generalize the input past Theorem E's one-run-letter normal form.
4. **Single-coset catch-up-free classes with `|det M| = k`.** Fix
   `f : Z³ → Z/k` with `Λ = ker f`, and take shapes in which every proper
   prefix has `f ≡ c ≠ 0`: first letter in class `c`, interior letters in
   class 0, last letter in class `−c`. At `k = 2` this is Proposition C.
5. **Swap engines between the lemmas.** Use residue splitting with rank
   descent on Theorem K's `F` residue; use witness-path cones for the
   strict-zipper targets that are coincidences.
6. **The catch-up regime.** Look for arithmetic conditions that force catch-up
   hits. §2 supplies its first calibration family.

Metric for ranking the moves: one coverage ledger, by window and separate from
the Theorem Ω domain. Coverage counts are finite evidence and never closures.

## 2. Move 1: stop/go and result

### Proposed claim and prior art

The proposal was to extend every certified family by its orbit under
relabelling, reversal, powers, roots and letter-rotation conjugacy. Pure
discrete spectrum is invariant under all of these
([S-adic transfer gate §2](sadic-transfer-literature-gate-2026-10-11.md)).
`τ` is a *left conjugate* of `σ` by `p` when `σ(a) p = p τ(a)` for every
letter `a`. Then `σ` and `τ` have the same subshift and incidence matrix, so
`τ` is again PIP. The invariance is classical and already imported, and it
adds no literature dependency. **Decision: proceed, narrowed** by the
arithmetic below, which predicted most of the orbit to be empty.

### What the arithmetic rules out

- **Powers and roots.** `det(σⁿ) = (det σ)ⁿ = (±2)ⁿ` is not `±2` for `n ≥ 2`,
  and `det(τ)ⁿ = ±2` has no integer solution for `n ≥ 2`. So no
  `|det M| = 2` family gains a new `|det M| = 2` member this way. Powers
  produce determinant `±2ⁿ` presentations of the *same* tiling space, which
  is legitimate but bookkeeping only.
- **Relabelling and reversal.** These are already absorbed in Theorem E's
  four mirror classes. They are bookkeeping.
- **Rotations of classes A, C and D.** These classes have no rotations: `x`
  and `c` head their own images, so there is never a common first letter, and
  their endings `(s_x, s_c, s_y)` are never constant. Each class is
  conjugacy-isolated.

### Class B is the exception

Class B is `σ(x) = x yᵖ x`, `σ(c) = c y^q x`, `σ(y) = c yʳ x`. Put
`m = min(p, q, r)`.

**Proposition (conjugacy chain).** The conjugacy class of a class-B member is
exactly

```text
σ, τ_1, …, τ_{m+1},
τ_k(x) = y^{k-1} x x y^{p-k+1},
τ_k(c) = y^{k-1} x c y^{q-k+1},
τ_k(y) = y^{k-1} x c y^{r-k+1},
```

of size `m + 2`, and no `τ_k` is catch-up-free.

*Proof.*
1. `σ` has no common first letter, since its images begin with `x`, `c`,
   `c`. Its common last letter `x` gives `τ_1`.
2. For `2 ≤ k ≤ m + 1`, `τ_k` has common first letter `y`, so its left step
   returns `τ_{k−1}`. Its right step exists exactly while every run exceeds
   `k − 1`, which yields `τ_{k+1}` for `k ≤ m`.
3. At `k = m + 1` the image with the shortest run ends in `x` or `c`.
   Because `q ≠ r`, the `c`- and `y`-images do not end alike, so there is no
   further step. Hence the class is closed at size `m + 2`.
4. Odd letters are `{x, c}` (Proposition C). In `τ_k(x)`, the proper prefix
   `y^{k−1} x x` has even odd-count, so its abelianization lies in
   `Λ = ker f`. By Lemma P this means `τ_k` is not catch-up-free. `square`

**Corollary (lateral transfer).** Let `σ` satisfy Theorem C's hypothesis.
Then each of its `m + 1` nontrivial conjugates
- is PIP with `|det M| = 2`;
- has pure discrete spectrum, by conjugacy invariance;
- has finite BPA, by `PDSImpliesRepoG1`;
- satisfies BH, by Theorem S (PDS ⇒ PPVC) and Proposition V (PPVC ⇔ BH);
- lies in the **catch-up regime**, outside every Theorem E class.

The corollary is quantified over Theorem C's whole region. The census below
checks it on a bounded box only.

### Evidence and replay

```sh
cd kernel
pixi run mojo run -I . lateral_conjugacy_census.mojo 30
pixi run mojo run -I . tests/test_conjugacy_orbit.mojo
```

- **Canonical code.** `kernel/psc/conjugacy_orbit.mojo` computes the
  one-letter step closure. It refuses a step without a shared letter, and
  refuses rather than truncates past a cap.
- **Driver.** `kernel/lateral_conjugacy_census.mojo` raises on any departure
  from the proposition: a nontrivial A/C/D conjugate, a class-B class size
  other than `m + 2`, a failed conjugacy equation `τ_k(a) z = z τ_{k−1}(a)`
  checked on words, a changed incidence matrix, or a catch-up-free conjugate.
- **Results.** Packet: [`evidence/lateral-conjugacy-2026-10-23/`](../evidence/lateral-conjugacy-2026-10-23/).
  Over `p, q, r ≤ 30`:

  | Class | PIP `|det M| = 2` members | Conjugacy classes |
  | --- | --- | --- |
  | A | 685 | all singletons |
  | B | 685 | all chains of size `m + 2` (largest 31) |
  | C | 327 | all singletons |
  | D | 829 | all singletons |

  The 667 class-B members in Theorem C's region have **8,576** nontrivial
  conjugates. None is catch-up-free, 8,571 lie outside the Ω domain, and no
  member has a Barge power/rotation witness up to power 2. The run takes about
  4 s.

### Negative controls

- A step without a shared letter raises.
- A wrong conjugate fails the word equation.
- A cap below the class size raises.
- Tribonacci gives a class of size 2 by one left step. This checks the closure
  outside Theorem E's normal form.

### Non-claims

- Conjugates are new *substitutions*, not new tiling spaces. They add nothing
  to the universal problem beyond these presentations.
- The BH conclusion for conjugates depends on Theorem S and on Proposition V,
  which rests on Theorem B. Both are repository-proved with human review
  pending.
- Barge coverage was tested only up to power 2.
- Powers were not enumerated: they change the determinant and are bookkeeping.

### Why this matters despite being cheap

The overlap graph, catch-up hits and BH are **presentation-dependent**, while
PDS is not. The Corollary therefore provides an infinite, explicit family of
catch-up-regime substitutions on which BH is *known* to hold. That is exactly
the calibration set move 6 lacked. The same family is a ready negative
control for any proposed catch-up-regime mechanism: it must not refute BH on
any `τ_k`.

## 3. Next

Move 2 (gap-uniform A/C, then the class-B top layer) remains the
highest-value proof move. Move 6 can now start by running the existing
catch-up witness census on a sample of class-B conjugates and measuring how
their hits divide between catch-up and simultaneous births.

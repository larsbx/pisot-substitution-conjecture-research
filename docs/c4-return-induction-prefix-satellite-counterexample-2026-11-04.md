# C4 return-word induction: a primitive Pisot prefix satellite disappears at every derived power — 2026-11-04

**Status:** A fully literal, finite-alphabet **negative control** for transferring the prefix-satellite sufficient condition through return-word induction. This is not a counterexample to strong coincidence, return-substitution theory, C4, or PSC. It is a proof that one proposed *shortcut* (inheritance of a literal prefix relation) fails, even for a primitive irreducible Pisot substitution. No governed claim status changes.

## Question prompted by forward-family PR #483

[PR #483](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/483) proves a useful *conditional* ternary exit criterion: when `sigma(k)=sigma(i)W` as **literal** words, strong coincidence of the remaining pair transports to every pair.

Could ordinary return-word induction create or preserve that same literal prefix relation, making the C4 strict-carrier problem accessible via a return substitution?

The precise answer to the naive **preservation** question is **no**. Return-word recoding respects substitution via an intertwining but does **not** generally preserve prefix comparability *of images of return letters*.

This construction uses the standard return-word/derived-sequence framework of F. Durand, *A characterization of substitutive sequences using return words*, Discrete Mathematics **179** (1998), 89–101 (https://doi.org/10.1016/S0012-365X(97)00029-0). The primitive-return-substitution framework itself is prior art; the exact small negative control below and its obstruction to the proposed PSC proof route are the scoped observations.

## Original substitution: genuine primitive irreducible Pisot

Use the symmetric s=2 member of the forward family:

```text
sigma: 0 -> 01, 1 -> 121, 2 -> 012.
```

Its incidence matrix (columns are letter images) and polynomial are

```text
M = [ 1 0 1 ]
    [ 1 2 1 ]
    [ 0 1 1 ]

det M = 2
chi_M(x) = x^2(x-2) - 2(x-1)^2
```

The proof of primitivity and irreducible Pisot spectrum is in merged [#479](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/479). The exact *literal* prefix-satellite relation is

```text
sigma(2) = sigma(0) + "2" = "012".
```

Indeed the three second images simultaneously have equal Parikh prefix
`(1,2,1)` at physical cut `p=4`, followed by the letter `1`:

```text
sigma^2(0) = 01121
sigma^2(1) = 121012121
sigma^2(2) = 01121012.
```

Thus this source substitution is a **productive PIP**, not a strict counterexample.

## The exact return words to marker 0

Because sigma(0) begins in 0 and sigma is primitive, it defines an infinite fixed word `x=sigma^infinity(0)`.

A **return word to 0** is the exact factor starting at one 0 and stopping immediately before the next 0; it has exactly one zero, at its first position.

Define the coding `h` from a four-letter return alphabet `{0,1,2,3}` by

| Return symbol | Exact physical return word |
| ---: | --- |
| 0 | `r0 = 01121121` |
| 1 | `r1 = 012121121` |
| 2 | `r2 = 012121` |
| 3 | `r3 = 01121` |

All four strings begin with 0 and have no other zero.

The first return word of x is r0: direct expansion gives
`sigma^3(0)=01121121 012121`, with zeros at positions 0 and 8.
The candidate return set above is **exact and complete**, not an inference from a finite census; the proof follows from the factorisation identities below.

## The genuine induced return substitution

For each r_i, substitute its *actual physical letters* and split at every 0. The resulting pieces are **complete** return words and their ordered indices define `tau`:

| i | Exact sigma(r_i) factorisation | tau(i) |
| ---: | --- | --- |
| 0 | r0 r1 r2 | `012` |
| 1 | r3 r2 r1 r2 | `3212` |
| 2 | r3 r2 r2 | `322` |
| 3 | r0 r2 | `02` |

The literal identities prove the morphism intertwining

```text
sigma(h(i)) = h(tau(i))       for each return letter i
sigma ∘ h = h ∘ tau          on all return-letter words.
```

They also prove that h(tau^n(0))=sigma^n(r0) is a prefix of x for every n. Its length tends to infinity (sigma has strictly growing primitive incidence). Each of these long prefixes splits into complete words from the four-element set; **every** return word of x appears inside some such prefix and hence belongs to the set. Conversely, r0,r1,r2 occur already in the expansion of r0, and r3 occurs when r1 or r2 is expanded one more time, so all four occur. Thus they are precisely the return words to 0, with the displayed ordering determined by first appearance.

The induced return substitution is

```text
tau: 0 -> 012, 1 -> 3212, 2 -> 322, 3 -> 02.
```

Its incidence matrix is

```text
N = [ 1 0 0 1 ]
    [ 1 1 0 0 ]
    [ 1 2 2 1 ]
    [ 0 1 1 0 ].
```

A direct integer multiplication gives

```text
N^3 = [  3  4  3  2 ]
      [  3  2  1  2 ]
      [ 17 20 13 10 ]
      [  7  8  5  4 ] > 0.
```

So the return substitution is itself **primitive**. No irreducible-degree-four Pisot assertion is made: the return alphabet is not the original three-letter alphabet.

## A uniform obstruction at *every* return-substitution power

**Proposition (exact all-powers loss of literal prefix satellites).**
The four first-generation return-substitution images are pairwise **prefix-incomparable**:

```text
tau(0)=012       versus tau(3)=02     (second letter 1 vs 2)
tau(1)=3212      versus tau(2)=322    (third letter 1 vs 2)
```

Images across the two groups have different first letters (0 vs 3). Hence
`{tau(0),tau(1),tau(2),tau(3)}` is a **prefix code**.

More generally, if a nonerasing substitution theta maps its individual letters to pairwise prefix-incomparable words, then theta maps any two prefix-incomparable words to prefix-incomparable words: at their first differing letter, distinct theta-codewords cannot be prefixes of one another. Induction on n proves the family `{theta^n(i): i in A}` is prefix-incomparable for **every n>=1**.

Therefore this genuine return substitution has **no literal prefix-satellite pair at any positive substitution power**, although its parent substitution has `sigma(2)=sigma(0)2`. This conclusion is an all-powers proof, **not** a bounded absence test.

The phenomenon is subtle: the physical return words themselves are **not** prefix-free (r3 is a proper prefix of r0, and r2 is a proper prefix of r1), but the ordered return-word image *encodings* are prefix-free. Their concatenations are uniquely segmented by zeros; the physical prefix relation need not land at a complete return boundary. Uniqueness of parsing does not imply preservation of letter-image prefix comparisons under this change of alphabet.

**What is not refuted:** Strong coincidence can hold for the induced substitution, and a more elaborate induced/return-word proof using offset-decorated partial words might still work. Only the naive inheritance (even after passing to a power) is disproved here.

## Exact growth of the lost return-boundary residual

**Corollary (one expanding residual suffix).** The four true physical return words satisfy the two **literal** identities

```text
r0 = r3 + B       and       r1 = r2 + B,
B = 121 = sigma(1).
```

Consequently, for **every n>=0**,

```text
sigma^n(r0) = sigma^n(r3) + sigma^(n+1)(1)
sigma^n(r1) = sigma^n(r2) + sigma^(n+1)(1).
```

The suffix at both comparable return-word pairs is **the same expanding physical word**, not an arbitrary collection of numerical discrepancies. The identities follow immediately by applying the morphism sigma^n to the two displayed literal equalities, with **no** finite-parameter or finite-depth extrapolation.

Primitivity gives `|sigma^(n+1)(1)| -> infinity`. Thus no *uniformly bounded physical-character-length residual* can encode these pairwise prefix relations at all substitution levels. This does **not** rule out a finite **symbolic** residual representation: the missing suffix is already represented succinctly by `sigma^(n+1)(1)` plus an iteration counter.

The apparent paradox clarifies exactly where return coding loses information. Although `h(tau^n(3))=sigma^n(r3)` is a physical prefix of `h(tau^n(0))=sigma^n(r0)`, the shorter encoded word `tau^n(3)` is **not** a prefix of `tau^n(0)`. The shorter physical prefix ends **inside** a return-code word in the longer segmentation; the return-code boundary is not common to both parsings. The same phenomenon holds for indices 2 and 1.

This suggests a more precise viable research interface: carry a *residual word with a substitution-level address* together with both complete return-code prefixes, and require physical seam/marker alignment before asserting any coded letter-pair coincidence. The result is a control on a naive **bounded raw suffix** state-space, not a proof that a finite-state symbolic/transducer construction is impossible.

## Full-rank spectral transport still does not restore literal prefix order

**Corollary (exact spectral transport with a killed return redundancy).**
Let P be the 3-by-4 integer matrix whose columns are the Parikh vectors
of r0,r1,r2,r3, respectively. The literal return identities above give

```text
P = [ 1 1 1 1 ]
    [ 5 5 3 3 ]
    [ 2 3 2 1 ]

M P = P N = [ 3  4 3 2 ]
              [13 14 9 8 ]
              [ 7  8 5 4 ].
```

The leading 3-by-3 minor of P has determinant **2**, so P has
rational rank 3 and kernel exactly `span{v}` with
`v=(-1,1,-1,1)^T`. Moreover the **exact** derived incidence
satisfies `Nv=0`. Consequently N induces M on the quotient
`Q^4/ker(P)`, and its characteristic polynomial factors as

```text
chi_N(x) = x * chi_M(x)
         = x * (x^3 - 4*x^2 + 4*x - 2).
```

This is the same nonzero irreducible Pisot spectrum as the source,
plus a single zero eigenvalue from the redundant return-letter
direction. The source-return Parikh relation in v follows directly
from `r0=r3+B` and `r1=r2+B`: the extra letter coordinate is
eliminated **in one derived substitution step**.

Thus even a **full-rank exact Parikh intertwiner** and preservation
of the complete nonzero Pisot spectrum do *not* imply preservation
of literal prefix-satellite order. This is a precise limitation of
an incidence-only or rank-only return-induction attack on #461,
not an obstruction to a properly occurrence-labelled geometric proof.

## The stronger interface that would actually be required

A correct induced-carrier proof needs a **boundary-synchronous prefix relation**: if an original word image is an initial segment of another, the extra endpoint must lie on a complete return-code boundary. Equivalently, the original literal prefix has to be expressible as the image under h of a full return-code prefix.

The original forward-family relation `sigma(2)=sigma(0)2` cannot be naively encoded this way, since the leftover physical letter `2` is not a complete return word to 0.

The next useful research target is to prove an occurrence-indexed, finite-offset analogue retaining the *unmatched suffix* as part of the state, and show it is preserved under every legal child occurrence. Such a theorem would need to track return-word seam addresses, not just the derived incidence matrix or a collapsed symbolic first-letter map. No such theorem is proved here.

## Reproducible evidence and trust boundaries

Canonical Mojo in `kernel/psc/c4_return_induction_prefix_satellite.mojo` reconstructs each `sigma(r_i)` as a true 3-letter physical word, splits it at zeros into **ordered** return words, checks the exact induced 4-letter substitution, verifies the source generation-two three-letter strong-coincidence certificate and checks that all four return images are pairwise prefix-incomparable. It refuses malformed marker/code words and over-budget depth.

The native test `kernel/tests/test_c4_return_induction_prefix_satellite.mojo` checks intertwining, primitive positive `N^3`, bounded powers and prefix-code negative controls. An independently written Python oracle in `tests/test_c4_return_induction_prefix_satellite_oracle.py` reconstructs the first four return words from a deep physical prefix **without supplying their identities to the discovery pass**, checks exact closure, occurrence, decode/re-encode and bounded powers, and verifies the general first-divergence argument on independent codewords. These finite checks support the literal identities; the all-powers statement uses the displayed prefix-code proof.

Replay:

```sh
python -m pytest -q tests/test_c4_return_induction_prefix_satellite_oracle.py
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_return_induction_prefix_satellite.mojo)
python tools/make_proof_bank.py --check
```

**Stop/go:** Standard return-substitution existence is prior art; no novelty claim beyond the explicit counterexample/PSC proof-route diagnosis. Do **not** infer a general strict PIP system exists, C4 is false, C4 is proved, G1 or PSC closes, or that return-word induction destroys strong coincidence itself. The earlier productive-PIP control remains productive. Hosted exact-head CI and independent mathematical audit are distinct and pending.

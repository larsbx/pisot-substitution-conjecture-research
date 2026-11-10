# Uniform third-level strong coincidence in a non-unit Pisot family — 2026-11-04

**Status:** Proved parameter-uniform integer/word identity and bounded exact
Mojo/Python controls. This establishes a family-specific strictly child-closed
balanced-pair exclusion, NOT general C4, BH, A1′, G1, PDS or PSC.

## Prior art and stop/go

[Barge–Diamond (2002)](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
define strong coincidence using a common next letter after prefixes of
**equal abelianization**. Equal letter indices alone are insufficient.
The balanced-pair literature identifies a diagonal one-letter child when
consecutive balanced cuts enclose a common letter:
[balanced-pair study](https://www.numdam.org/item/10.1051/ita%3A2007062.pdf).

Draft [PR #475](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/475)
excludes the single substitution 01/121/012 using an exact legal-seam
residue filter. First inspect direct pairwise strong coincidence before
generalizing that mechanism: the specimen belongs to an infinite
non-unit Pisot family with **simultaneous** coincidence at level three.
The seam filter is a separate valid-style necessary-condition instrument;
for this specimen it is not needed to exclude finite strict balanced
components. No assertion of general pure discreteness follows.

## Exact family and Pisot verification

For any integer k >= 1 define the letter images

~~~text
A = sigma_k(0) = 01
B = sigma_k(1) = 1^k 2 1^k
C = sigma_k(2) = 012

M_k = [1   0   1]
      [1  2k   1]
      [0   1   1]

M_k^2 = [   1       1       2]
        [2k+1    4k²+1   2k+2]
        [   1     2k+1      2]

det M_k = 2k
f_k(x) = x³-(2k+2)x²+4kx-2k
       = x²(x-2)-2k(x-1)²
disc(f_k) = -4k(8k²-13k+16) < 0.
~~~

The positive matrix square proves primitivity. Every rational root of the
monic cubic would be an integer z. For z <= 2 the expression
z²(z-2)-2k(z-1)² is strictly negative. For z >= 3, equality would imply
(z-1)² divides z²(z-2), but the latter is coprime to (z-1)² and
(z-1)² > 1. Thus no rational root exists, and f_k is irreducible over Q.

The discriminant is negative because 8k²-13k+16 is positive at k=1
and increases by 16k-5 for successive positive integers. The unique
real root beta satisfies

~~~text
f_k(2k)   = -2k < 0,
f_k(2k+1) = 4k²-2k-1 > 0,
so 2k < beta < 2k+1.
~~~

The other two roots are complex conjugates with squared modulus
(det M_k)/beta = 2k/beta < 1. Every sigma_k is therefore primitive,
irreducible Pisot and non-unimodular, for **all k >= 1**.

## Uniform simultaneous strong coincidence at a common address

Define p_k = k(2k+1)+1 = 2k²+k+1 and Q_k = (1,2k²,k).

For every a in {0,1,2}, the complete literal word sigma_k³(a) has:
(1) Parikh of its first p_k symbols exactly Q_k; and
(2) next symbol at index p_k exactly letter 1.

To prove this without finite enumeration, expand:

~~~text
sigma²(0) = A B
sigma²(1) = B^k C B^k
sigma²(2) = A B C

sigma³(0) = A B^(k+1) C B^k
sigma³(1) = (B^k C B^k)^k (A B C) (B^k C B^k)^k
sigma³(2) = A B^(k+1) C B^k A B C
~~~

In sigma³(1), the prefix of length p_k is B^k followed by the
first 0 of C; it has Parikh Q_k and is followed by the letter 1
(second letter of C). In sigma³(0), the prefix of length p_k
is A followed by B^k **without its final 1**. Its Parikh vector is
(1,1,0) + (0,2k²,k) - (0,1,0) = Q_k, and it is followed by
that omitted final 1. Sigma³(2) starts with the **entire**
sigma³(0), so it has the same prefix and next letter.

Consequently all three letter pairs are strongly coincident
simultaneously by substitution level 3, with the *same* exact
address (p_k, letter 1). This is stronger than a collection of
unrelated finite good-edge witnesses.

### Sharper base case k=1

The specific substitution 01/121/012 in draft #475 admits a
**generation-two** simultaneous coincidence, not merely the common
level-three witness. Directly:

~~~text
sigma²(0)=01121
sigma²(1)=121012121
sigma²(2)=01121012
~~~

All three words have the exact Parikh prefix (1,2,1) at
zero-based position 4, followed by the letter 1.
In particular, the *remaining* unordered first pair {0,1}
left undecided by the two-good-edge restriction in #475 is
itself already strongly coincident at depth two.
Thus that singleton no-strict-component exclusion has
a shorter independent proof, without the local seam-residue
calculation. The latter remains a useful filter for
substitutions not exhibiting this stronger coincidence.

## Exact balanced-pair consequence (family-scoped)

Let T=(u,v) be **any** nonempty irreducible noncoincident
Parikh-balanced word pair. Its first two letters a=u[0] and
b=v[0] differ: if they agreed, a one-letter balanced prefix
would contradict irreducibility and noncoincidence.

The full inflation sigma_k³(T) starts with sigma_k³(a)
and sigma_k³(b). Their first p_k letters have equal Parikh,
so p_k is a genuine balanced cut. The next letters on both
sides are 1; thus p_k+1 is also a balanced cut. The complete
actual irreducible factorization must include the diagonal
one-letter block (1,1) at physical positions [p_k,p_k+1).

**Proved result:** For every k >= 1 and every such T,
the **complete literal** three-generation balanced
factorization contains a diagonal child (1,1). No nonempty
finite strictly child-closed noncoincident balanced-pair
component can exist for any member of this infinite family.

The proof does not assume seed legality, G1 extraction,
a finite entire balanced-pair automaton, or a global C4 theorem.

## Replay and controls

- Canonical bounded checker: kernel/psc/c4_third_level_coincidence_family.mojo.
  It rejects k <= 0 and k > 16 rather than treating the cap as a
  mathematical refusal, and compares all three full third-level words
  against p_k, Q_k and the shared letter.
- Canonical tests: kernel/tests/test_c4_third_level_coincidence_family.mojo.
  They replay k=1..12 and all three actual two-letter swap
  balanced-factor decompositions for k=1..8.
- Independent Python: tests/test_c4_third_level_coincidence_family_oracle.py.
  It reconstructs all third-level words, spectra checks and complete
  letter-pair swap factorizations; all integer arithmetic is exact.

~~~sh
cd kernel && pixi run --locked mojo run -I . tests/test_c4_third_level_coincidence_family.mojo
cd .. && python -m pytest -q tests/test_c4_third_level_coincidence_family_oracle.py
bash tools/verify_all.sh provenance
~~~

The k ranges are only finite executable **regressions**; the
word identities above prove the universal k statement.
The prior strict *reducible non-Pisot* control 10/102/211,
the real-secondary PIP packet-cycle controls and the productive
phase-zero PIP controls remain outside this family theorem.

For k=1 the substitution is exactly 01/121/012. The
previous [PR #475](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/475)
identifies two left-good edges but does not need to leave the
third pair {0,1} undecided: the common level-three occurrence
above also witnesses {0,1} (and {1,2}), even though the
earlier seam-residue exclusion remains an independently
testable structural route.

**Non-claims:** Pairwise strong coincidence is not asserted
to prove general pure discreteness in three letters. No
general all-seed productivity, strict C4, BH #139, A1′ #138,
G1 #44, #84 or PSC is proved by this family theorem. Source
proof is an exact written argument, not a Lean formalization.
Hosted exact-head CI and independent human review are
separate acceptance tasks.

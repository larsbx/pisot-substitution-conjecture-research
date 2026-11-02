# Exact Class-A M-adic parity addresses and the level-m zero-return criterion

**Status:** parameter-uniform elementary integral-algebra theorem and canonical finite-level verifier **proposed**. This is a specialized finite-place input toward [Class-A BH entry #452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452), not a proof of entry, the universal BH theorem, A1′, G1, PDS or PSC.

**Current baseline:** main includes [#447](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/447) (exact finite outgoing completeness), [#448](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/448) (conditional Lean distance), and [#450](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/450) (independent C4 actual-cut results). The one-generation inverse target and its nine affine segments are in **draft** [#451](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/451), not yet accepted here. This note introduces no dependency on its unmerged executable source.

## Exact standing model

Let k,t>=0, n=k+t+3, d=k+2t+5, A=n+d. With ordered alphabet (x,c,y) and actual minus Class-A words

    x -> x y^A x,   c -> c y^n x,   y -> x y^(n-1) c,

the incidence matrix (columns indexed by parents) is

         [ 2  1    1  ]
    M =  [ 0  1    1  ],  det M = -2,
         [ A  n  n-1 ]

and acts on integer Parikh offsets v=(p,q,r).

## Theorem 1: unique canonical binary digits at every finite level

For every v in Z^3 and integer m>=0, there exist **unique**

    b_0,...,b_(m-1) in {0,1},   u in Z^3

such that

    v = (sum_(j=0)^(m-1) M^j b_j e_x) + M^m u.

The m-bit vectors label exactly 2^m distinct cosets of M^m Z^3 in Z^3. In particular

    v in M^m Z^3  <=>  b_0=...=b_(m-1)=0.

This does **not** assert the quotient group is cyclic or identify it with Z/(2^m): the bits form a unique *transversal*, not an additive binary integer coordinate. The result is valid for every k,t,m in the stated integer domain; the executable verifier enforces a separate finite-level budget.

### Derivation

For w=(X,C,Y), the matrix image obeys X-C=2p. Conversely, when X-C is even the **unique** integral inverse is

    p = (X-C)/2,
    q = Y - A p - (n-1) C,
    r = A p + n C - Y.

Direct substitution verifies M(p,q,r)=w. Thus

    M Z^3 = { (X,C,Y) in Z^3 | X-C is even }.

For arbitrary w, let b_0 be the parity of X-C in {0,1}. Then w-b_0 e_x lies in M Z^3 and determines a unique integer u_1=M^(-1)(w-b_0 e_x). Apply the same operation to u_1, obtaining b_1 and u_2; continue m times. The recurrence w_j=b_j e_x+M w_(j+1) proves the expansion by substitution. At each stage parity forces b_j uniquely and M has trivial rational kernel, forcing the integer quotient uniquely. Conversely reconstructing from any binary word and tail produces an integer v with precisely that digit word. Equality of two cosets implies equality of their digits by inductive parity and cancellation. Since there are 2^m binary words, they exhaust the index |det(M^m)|=2^m. QED.

**No uniform m is fixed or required by the theorem.** This does not turn the inverse-limit of finite cokernels into realized nonunit overlap geometry; the arithmetic interface and the representation-space bridge remain distinct.

## Theorem 2: exact multi-level prefix zero-return filter

Let a,b be actual top/bottom letters. For *actual occurrence positions* i,j in the literal words sigma^m(a), sigma^m(b), let

    D = Parikh(sigma^m(a)[0:i]) - Parikh(sigma^m(b)[0:j]).

There exists a **unique integral** parent Parikh offset w such that the resulting level-m pair of child tiles has zero offset iff all m canonical bits of D vanish. In that case the unique offset is exactly the tail u of Theorem 1:

    M^m w = D.

The full-level child offset is M^m w-D, since bottom minus top prefixes are used. The proof is precisely Theorem 1's image-membership statement plus the literal-prefix inflation identity. **The indexed occurrence requirement cannot be replaced by an arbitrary vector D.** Once i,j really exist, both level-m child tiles begin at the same physical coordinate, so they share a positive-length interior interval; their actual hierarchical ancestors give strict overlapping parent-child occurrence edges. If a typed coincidence appears earlier, the repository's terminalized graph stops there, which already supplies a successful zero return.

This is a precise *decision test for a supplied pair of level-m prefix occurrences*, not an assertion that any admissible-looking digit or specific source eventually has such a pair. In particular, the global Class-A problem is still to prove entry from **every relevant cyclic seed descendant** into some actual zero-return predecessor; the existence of 2^m arithmetic cosets supplies no recurrence or escape mechanism by itself.


## Theorem 3: actual ordered-prefix carry criterion, without expanding sigma^m

Theorem 2 admits a second, *occurrence-level* certificate valid for every
finite m and every pair of genuine equal-depth Dumont–Thomas paths. Let the
two paths start at oriented root letters a,b, with zero-based child choices
(i_0,...,i_(m-1)) and (j_0,...,j_(m-1)) written **root-to-leaf**.
After each choice, the next parent letter is exactly the letter occurring at
that chosen index in the current parent substitution word. Every index must
exist at its level, including FIRST/RUN/LAST endpoints. Define the literal
proper-prefix differences at those parent letters as

    q_r = ab(prefix(top_parent_r,i_r))
          - ab(prefix(bottom_parent_r,j_r)).

The complete level-m proper-prefix difference is the **exact** identity

    D = M^(m-1) q_0 + M^(m-2) q_1 + ... + q_(m-1).

The quickest nonunit image-membership criterion now uses a carry recurrence
in reverse path order. Set c_0=0 and for j=0,...,m-1 require the *integral*
inversion

    c_(j+1) = M^(-1) (c_j + q_(m-1-j)).

The invertibility is tested by the parity of X-C at every stage. All stages
succeed **if and only if D belongs to M^m Z^3**, and in that case c_m
is the unique integer parent offset w with M^m w=D.

**Proof.** If q_(m-1) lies in M Z^3 then c_1=M^(-1)q_(m-1)
is integral, and D=M[D_1+c_1], where D_1 is the remaining weighted sum
q_(m-2)+M q_(m-3)+... . Repeating this factorization shows divisibility
by M^m exactly when each intermediate carry is integral; the final quotient
is c_m. Conversely any failed intermediate inversion means the corresponding
remaining term cannot lie in M Z^3, so neither can D lie in M^m Z^3.
This is repeated exact matrix inversion, not an argument from finite samples.
Actual ordered paths make the prefix factorization an identity rather than
a hypothesis about abstract residue words. QED.

**Important negative calibration:** At k=t=0 the root letters x/x and
paths top (0,0), bottom (1,0) choose FIRST on both sides at their *deepest*
level. Yet the upper-level prefix difference is (-1,0,0), whose X-C parity is
odd. The first carry succeeds, the second fails, and the full level-two
zero-return parent does not exist for this chosen pair. Thus equality of the
lowest FIRST/non-FIRST flags is necessary at that level but is **not**
sufficient for level-two hitting. Requiring raw flags to match at *every*
level is also not established as a criterion: the higher carry is affected by
lower-level image-lattice corrections. This failure is not a nonproductive
SCC or a disproof of BH.

The new canonical `kernel/psc/class_a_prefix_carry.mojo` reuses the existing
actual Class-A word/index prefix transport and the index-two inverse.
It validates the *entire* pair of paths before any membership verdict,
returns the first failed carry stage, and uniquely reconstructs the parent
when all stages pass. The accompanying native test exhausts every pair of
actual level-two paths over all three root letters at (k,t)=(0,0),(1,0)
and compares to the independent direct full prefix and power membership.
`tests/test_class_a_prefix_carry_oracle.py` builds the entire actual
sigma-squared words and checks the result against independent matrix-power
Cramer divisibility. The all-level mathematical statement does not borrow
universality from these finite experiments.

Commands (repository root and kernel, respectively):

```sh
python -m pytest -q tests/test_class_a_madic_digits_oracle.py tests/test_class_a_prefix_carry_oracle.py
cd kernel && pixi run --locked mojo run -I . tests/test_class_a_prefix_carry.mojo
```

This **does not** prove that some path pair with all successful carries
occurs among seed-reachable strict-zipper descendants, or that a selected
path can be made compatible with geometric overlaps at every intervening
level. The remaining task in #452 must impose those occurrence, geometry,
and all-descendant coverage conditions explicitly.

## Canonical implementation and independent acceptance

- `kernel/psc/class_a_madic_digits.mojo` supplies exact checked incidence multiplication, index-two inverse, per-stage parity extraction, reconstruction, congruence, and unique integral zero-parent recovery. Its finite budget is m<=64. Overflow, malformed vectors, missing levels and nonbinary reconstruction digits refuse rather than become false proof receipts.
- `kernel/tests/test_class_a_madic_digits.mojo` checks integer round trips for 16 parameter specimens, five finite levels and every triple in [-2,2]^3; enumerates all 2^m cosets at levels 1..4, rejects distinct-word collisions, checks multi-step parents and malformed inputs.
- `tests/test_class_a_madic_digits_oracle.py` uses an **independent** 3x3 matrix-power algorithm and exact Cramer-divisibility test (not the digit recurrence as its definition of the target). It checks image-power membership and integral inverse, all canonical representatives in sample chambers, and determinant index. It also independently expands actual substitution words through levels one and two for two parameter specimens, exhaustively reconstructs real proper-prefix differences at every ordered index pair, and compares the Cramer integer-parent criterion to the binary-zero test. It does not use floating point or a reduction modulo 2^m integer as a substitute for the actual quotient.

Replay from repository root:

```sh
python -m pytest -q tests/test_class_a_madic_digits_oracle.py
```

Replay canonical Mojo from `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_class_a_madic_digits.mojo
```

**Verification status at PR opening:** written derivation and source-level audit. No fresh native execution or exact-head hosted pass is claimed before CI receipts. The new tests and workflow must pass. Human review is final validation debt, not assumed completed. Existing finite-cokernel code in `kernel/psc/finite_cokernel_address.mojo` is prior internal art for generic Cramer membership; this specialization supplies the explicit Class-A binary transversal and m-level prefix inversion without duplicating the generic graph or SCC engine.

## Negative controls, nonclaims and next obligation

A locally matching deepest pair of FIRST flags can still fail a later exact carry; a one-bit nonzero residue refuses integer zero-parent recovery; two different digit words are never identified modulo M^m; the arithmetic residue alone is not a literal substitution occurrence; a word beginning in a correct residue need not arise along a seed-reachable strict graph path. No assumption of unimodularity, Euclidean-only representation, all-edge decreasing ranks, or group cyclicity is introduced.

Next: combine the nine one-step predecessor segments of draft #451 with these exact level-m residue tests to seek a **parameter-uniform, actual-occurrence entry/escape theorem**. Any proposed induction must establish coverage for *all* relevant cyclic strict-zipper descendants, not merely that a sampled residue class has representatives. Remain scoped to minus Class A until a separate complete classification/transfer and nonunit realized-overlap dictionary are proved.

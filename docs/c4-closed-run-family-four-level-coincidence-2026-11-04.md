# C4 boundary-completed run family: uniform strong coincidence by level four — 2026-11-04

**Scope:** Exact paper proof for one two-parameter family, together with
bounded canonical Mojo and independent Python word-level replays. It
**does not settle general C4, PSC, G1, BH, A1′ or pure discreteness**.
Source baseline `main@6c9811653024a3be3452b0a6a3b3e8113da31b40`
includes merged [#477](c4-asymmetric-third-level-coincidence-2026-11-04.md).
No claims are promoted in the governed ledger or Proof Bank.

## Prior work and the actual missing boundary

The merged [two-positive-run theorem](c4-asymmetric-third-level-coincidence-2026-11-04.md)
proves simultaneous strong coincidence at generation three for
`sigma=(01,1^a 2 1^b,012)`, but requires **a,b >= 1**.
That hypothesis is genuinely used: the proof removes the last
letter of `B^a` and expects a `1`, which is false when `b=0`.
For `a=0`, `B^a` is empty and the published index formula
does not describe the common occurrence.

Do not silently include either boundary in the old level-three
argument. Check both entire actual letter-image words, and
preserve the definition of strong coincidence (same next letter
after **equal prefix Parikh vectors**) rather than merely
matching physical positions. This is an exact extension of
[#477](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/477),
not a general PIP statement.

## Uniform PIP incidence for the *closed* parameter quadrant

Let `a,b` be **nonnegative integers with s=a+b>=1** and put

~~~text
sigma_{a,b}(0) = A = 01
sigma_{a,b}(1) = B = 1^a 2 1^b
sigma_{a,b}(2) = C = 012

M_s = [1  0  1]
      [1  s  1]
      [0  1  1]

M_s² = [1  1  2]
       [s+1  s²+1  s+2]
       [1  s+1  2] > 0

det(M_s) = s
chi_s(x) = x²(x−2) − s(x−1)²
disc(chi_s) = −s(4s²−13s+32) < 0.
~~~

The positive square proves primitivity. A monic cubic can
factor over Q only if it has an integer root. For `z<=2`,
`z²(z−2) − s(z−1)² < 0`; for `z>=3`, a root forces
`(z−1)² | z²(z−2)`, impossible since their gcd is 1
and `(z−1)²>1`. Hence the cubic is irreducible.

The quadratic `4s²−13s+32` is always positive, since
its own discriminant `169−512=−343` is negative.
The incidence cubic has one real root `beta_s` and
one complex conjugate pair. As `chi_s(s)=−s<0`
and `chi_s(x)` becomes positive for large x, its
unique real root has `beta_s>s`. The conjugate pair
has squared modulus `s/beta_s<1`. Thus every such
substitution is **primitive irreducible Pisot**.
It is **unimodular only when s=1**, and non-unit
for every `s>=2`.

The excluded `a=b=0` case has `det M=0`
and is **not** a member of this theorem.

## Three exact simultaneous coincidence cases

For every source letter `t=0,1,2`, the actual word
`sigma_{a,b}^{n}(t)` has the *same* Parikh prefix Q
at the same zero-based index p and the *same* letter z
immediately after it, according to this table:

| Parameter regime | n | p | Q | z |
| --- | ---: | --- | --- | ---: |
| `a=0,b>=1` | **2** | `0` | `(0,0,0)` | **0** |
| `a>=1,b>=1` | **3** | `a(s+1)+1` | `(1,as,a)` | **1** |
| `a>=1,b=0` | **4** | `a³+a²+4a+1` | `(a+1,a³+2a,a(a+1))` | **1** |

**Interior case:** the `a,b>=1` row is exactly
the uniform literal-word identity already proved
in merged [#477](c4-asymmetric-third-level-coincidence-2026-11-04.md).
It is neither rederived by finite enumeration nor
misapplied to the one-sided boundaries.

### Left boundary: a=0, b>=1

Now `B=2 1^b`. Directly expanding **all three**
second-generation images gives

~~~text
sigma²(0)=A B,
sigma²(1)=C B^b,
sigma²(2)=A B C.
~~~

Each starts with `0` (both A and C start with
zero). Hence the shared prefix is empty, with
common next letter `0` at **level 2**.
No assumption about matching nonempty prefixes
is involved; the zero-length Parikh prefix is
exactly `Q=(0,0,0)`.

### Right boundary: a>=1, b=0

The previous level-three proof fails here,
since `B=1^a2` ends in 2. A new **level-four**
explicit factorization resolves this case.

Let the second-generation letter words be

~~~text
F = sigma²(0) = A B
G = sigma²(1) = B^a C
H = sigma²(2) = A B C

|B| = a+1, |G| = a(a+1)+3 = a²+a+3.
~~~

The third-generation words are

~~~text
sigma³(0)=F G,
sigma³(1)=G^a H,
sigma³(2)=F G H.
~~~

The fourth-generation words are

~~~text
sigma⁴(0)=F G^(a+1) H,
sigma⁴(1)=(G^a H)^a (F G H),
sigma⁴(2)=sigma⁴(0) (F G H).
~~~

Set

~~~text
p=a|G|+a+1=a³+a²+4a+1.
~~~

The length-p prefix of `sigma⁴(1)` is
`G^a 0 1^a`, followed by letter **1**:
the prefix of length `a+1` in `H=A B C`
is `0 1^a`, with another 1 still remaining
in `B=1^a2`.

The length-p prefix of `sigma⁴(0)` is
`F G^(a−1) B^a 0`, followed by letter **1**:
inside the `a`th G block, `G=B^a012`,
the last two letters are `12`, and the
chosen cut lies immediately before that 1.
This formula works also at **a=1**,
where `G^(a−1)` is the empty word.

Counting occurrences in either prefix gives

~~~text
Q = (a+1, a³+2a, a(a+1)),
sum(Q)=a³+a²+4a+1=p.
~~~

Finally `sigma⁴(2)` starts with the whole
`sigma⁴(0)`, so the same Q and next
letter hold. This completes the algebraic
proof for **all a>=1**, without inferring it
from a bounded computation.

## Exact consequence for balanced pairs

Let `T=(u,v)` be any nonempty **irreducible,
noncoincident Parikh-balanced** pair. The initial
letters of `u` and `v` differ, otherwise the
common initial letter would already be a
one-letter balanced cut.

Inflate T by the generation n from the table.
Both resulting words have Parikh Q at index p,
and both next letters equal z. Thus positions
`p` and `p+1` are consecutive balanced cuts,
and their complete *actual* irreducible
factorization contains diagonal `(z,z)`
at physical interval `[p,p+1)`.

**Uniform family theorem:** For every `a,b>=0`,
`a+b>=1`, every irreducible noncoincident
balanced pair becomes productive within at
most **four full substitutions**.
There is **no nonempty fully strictly child-closed
noncoincident balanced-pair component** for
any member of this entire closed quadrant.

This statement does **not** establish general
BPA finiteness, a globally extracted strict
component from a failed seed (G1), pure
discrete spectrum, C4 for arbitrary PIP, or PSC.

## Fixed incidence does not fix word-level depth

All splittings with the same total `s=a+b`
share the complete incidence matrix and
Perron spectral data. Yet the supplied explicit
coincidence **generation and address** vary.
For `s=4` the five splittings have witnesses

| a | b | n | p | z |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 4 | 2 | 0 | 0 |
| 1 | 3 | 3 | 6 | 1 |
| 2 | 2 | 3 | 11 | 1 |
| 3 | 1 | 3 | 16 | 1 |
| 4 | 0 | 4 | 97 | 1 |

These are **exhibited** occurrences; the
table does not assert their generation or
position is the earliest possible. Incidence,
Parikh-rank and Perron-only invariants
cannot prescribe the *displayed*
word-representative witness.

## Replay, controls and acceptance

- Canonical Mojo extends
  `kernel/psc/c4_third_level_coincidence_family.mojo`
  with `closed_run_middle_family` and
  `verify_closed_run_coincidence`, a
  case-distinguished source-owned verifier.
  It preserves the previously merged strict-positive
  symmetric/asymmetric APIs and their refusal
  of zero runs. Parameters are capped by 16
  for the executable, not for the theorem.
- Canonical regression in
  `kernel/tests/test_c4_third_level_coincidence_family.mojo`
  includes both boundaries, complete actual
  two-letter swap factorization, the positive
  quadrant compatibility check, fixed-s
  witness table, and malformed/capped refusals.
- Independent Python in
  `tests/test_c4_third_level_coincidence_family_oracle.py`
  reconstructs literal second-, third- and
  fourth-generation words; the explicit
  F/G/H symbolic prefixes; entire balanced
  factorization and the exact integer
  characteristic data, including `s=1`.

**Independent development check:** the direct
formula was checked against the complete literal
three-letter words for 120 parameter cases
`0<=a,b<=10, a+b>=1`, and 360 complete
swap-balanced factorizations. This is a
bounded local exact Python cross-check,
**not a hosted exact-head canonical Mojo
or Lean result**.

~~~sh
cd kernel && pixi run --locked mojo run -I . tests/test_c4_third_level_coincidence_family.mojo
cd .. && python -m pytest -q tests/test_c4_third_level_coincidence_family_oracle.py
bash tools/verify_all.sh provenance
~~~

**Negative controls:** `a=b=0` is singular and
explicitly refused. The old asymmetric-positive
entrypoint continues to reject either zero
run, so no earlier proof silently changes
hypotheses. Fixed-s coincidences have
different exhibited levels and addresses.
The existing strict full-rank reducible
`10/102/211` example is outside this
family and remains a necessary non-PIP
countermodel. Productive PIP flat-cone
controls remain distinct.

**Status boundary:** The calculations
are an inspectable, uniform paper proof
plus bounded computational checks; their
completion does not amount to a machine-
checked PSC solution or an independently
reviewed universal theorem. Exact-head
hosted CI for the new code must pass
before recording implementation acceptance.

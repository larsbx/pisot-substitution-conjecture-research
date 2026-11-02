# C4 bilateral newborn-cut rigidity and a recurrent PIP negative — 2026-11-02

**Status:** two elementary **uniform conditional theorems** about literal
balanced-return geometry, plus an exact bounded PIP counterexample to a
*stronger but false* local alignment claim. **This does not prove C4, BH,
A1′, G1, PDS or PSC.** No strict PIP counterexample is constructed.

**Baseline:** `main@f76df185c25542f721d6041826cafdb9a0d3bed1`
(merged PR #448). C4 Issue #9 is administratively closed, not
mathematically discharged. The canonical target of #9 is a *one-step*
interior newborn right/left `Sync_±` boundary in a **supplied finite
strict child-closed PIP SCC**. Universal G1 extraction of that component
from an arbitrary global failure is a *different* open obligation.

## 1. Stop/go and existing sources

Existing exact lemmas:
[c4-prefix-difference-return-calculus](c4-prefix-difference-return-calculus.md)
already proves the asynchronous inflation formula, finite one-step
ancestry and bounded-gap returns. The
[protected legal ancestry theorem](c4-legal-ancestry-towers.md) and
[recognizable cut germs](c4-recognizable-cut-germs.md) distinguish
local legal contexts from equality of top/bottom substitution
decompositions. The [literature stop/go](c4-ordered-hub-literature-gate-2026-10-06.md)
records Martensen, Barge–Diamond and Durand–Leroy with their precise
hypothesis limits. We reuse these definitions; do not mistake this
elementary rigidity for an imported or previously unproved strong
recognizability theorem.

**Proceed:** prove the exact one-step bilateral-boundary exclusion under
full incidence rank and find a **literal** PIP obstruction to a tempting
stronger local alignment assertion before adding another finite offset
state. The canonical implementation is Mojo-first; Python is only an
independent bounded oracle. No fixed-size SCC sieve is added.

## 2. Theorem A: bilateral newborn exclusion (uniform and proved)

Let `sigma:A* -> A*` be a nonerasing substitution with an **injective**
incidence matrix `M` over `Q` (in the ternary setting,
`det(M) != 0`). Let `T=(u,v)` be a nonempty **irreducible Parikh-balanced**
pair, and let `0<t<|sigma(u)|=|sigma(v)|` be an actual zero return of
`(sigma(u),sigma(v))`.

> **Bilateral-birth rigidity.** The cut `t` cannot simultaneously be
> a boundary of a complete substituted source letter on both sides.

**Proof.** Suppose `t=|sigma(u[:i])|=|sigma(v[:j])|`. Equal Parikh
prefixes at `t` imply
`M (Parikh(u[:i])-Parikh(v[:j]))=0`. Injectivity of `M`
implies the source prefix Parikh vectors agree. Summing their
coordinates gives `i=j`. Since `T` is irreducible, equality of
Parikh prefixes at a common index occurs only for
`i=j=0` or `i=j=|u|`. These give the outer cuts, contrary
to the strict interior condition on `t`. QED.

**Scope.** This works in any finite alphabet with injective incidence;
it does *not* require Pisot, primitivity, recognizability, legality,
independence of tile lengths or unimodularity. In particular a newborn
zero-return cut may have a source-image boundary on **one** side, but
must cut through a substituted letter image on at least one side.

For the canonical asynchronous addresses `(i,r)` and `(j,s)`, the
literal identity is

```text
  0 = M E + c
  E = Parikh(u[:i]) - Parikh(v[:j])
  c = Parikh(sigma(u[i])[:r]) - Parikh(sigma(v[j])[:s]).
```

Theorem A excludes `(r,s)=(0,0)` at an interior return.
It does **not** exclude `r=0,s>0`, `r>0,s=0` or `r,s>0`.
It does **not** force `E=0` or `c != 0` at every newborn cut.
It cannot be confused with the converse to the existing inherited-cut
lemma. It applies separately to each irreducible *actual* child block
in a complete derived factorization.

## 3. Theorem B: a strict expanding component must have such a birth

Suppose further that `sigma` is primitive with Perron root `beta>1`,
and that `C` is a nonempty finite collection of normalized
irreducible balanced noncoincidence states whose **entire actual ordered
child factorization** lies again in `C`. Assume `det(M)!=0`.

> **Strict-component asynchronous-birth theorem.** Some `T in C`
> has at least two actual children after one substitution.
> Each of its interior child-boundary cuts is necessarily asynchronous
> on at least one source side.

**Proof.** Assume every state has exactly one child. Because the
factorization is complete and child-closed, repeated substitution of
any `T` produces a single normalized state in `C` at every
depth (up to physical top/bottom orientation). Its word length is
therefore bounded by `B=max_{S in C}|S|`. But the length of
`sigma^n(u)` tends to infinity for every nonempty `u`, since
the substitution is primitive and `beta>1`. Contradiction.
Thus at least one parent has two or more children. Their actual
interior boundaries are zero returns. Apply Theorem A to that
irreducible parent. QED.

This is **uniform in the cardinality of `C`**; no census, bounded
SCC-size sieve, invented packet transition or recognizability step is
used. It *locates* the remaining C4 proof interface: genuinely
asynchronous interior newborn word events are forced. It **does not**
show that any such event is in `Sync_+` or `Sync_-`. That
synchronization implication is still missing.

## 4. Theorem C: non-unit one-sided image-lattice obstruction

There is a second, **uniform word-digit necessary condition**, especially
useful when `|det M|>1`. Under the hypotheses of Theorem A, suppose
an actual newborn cut has exactly one within-image digit nonzero:
`(r,s)=(r,0)`, `r>0`, or `(0,s)`, `s>0`.
Then the inflation law becomes

```text
 M E = - Parikh(sigma(a)[:r])          (top-internal)
 M E = + Parikh(sigma(b)[:s])          (bottom-internal).
```

Since `E in Z^3`, the indicated **proper-prefix Parikh vector must lie
in the integral image lattice `M Z^3`**. The sign is irrelevant to
membership. Thus for an arbitrary substitution with nonsingular integer
incidence, a one-sided source-image cut after a prefix not in `M Z^3`
is *impossible at every parent, every depth and every strict SCC size*.
No converse (existence or synchronization) is claimed.

**Proof:** direct substitution into the exact prefix-difference
identity and integral source Parikh difference. QED. Cramer's rule
tests membership by checking that all three determinant-replacement
numerators are divisible by `det M`; this is valid without a
unimodularity assumption.

**Explicit non-unit PIP filter.** Take

```text
sigma(0)=1, sigma(1)=021, sigma(2)=001
M = [[0,1,2],[1,1,1],[0,1,0]], det M=2
char_M(x)=x^3 - x^2 - 2x - 2.
```

The characteristic polynomial has one Perron root greater than one
and two conjugates of modulus below one (this substitution is the
known non-unit PIP affine-pump fixture; the positive PIP classification
is not derived from a floating-point numerical estimate here).
For an integer column `q=(q0,q1,q2)`, direct solution gives

```text
M z = q <=> z1=q2, z2=(q0-q2)/2,
              z0=q1-q2-(q0-q2)/2.
q in M Z^3 <=> q0 = q2 (mod 2).
```

Hence the **first internal cut** of image `sigma(1)=021`
or `sigma(2)=001` has prefix column `(1,0,0)`, fails the
parity test and **cannot** be a one-sided balanced newborn cut.
Their **second internal cuts** have columns `(1,0,1)` and
`(2,0,0)`, respectively, and *pass the necessary test*.
Passing does not construct a cut. At a cut internal on **both**
sides the relevant correction is the *difference* of two
proper prefixes, so one-sided exclusions must not be
misapplied separately to each digit.

The new `proper_prefix_residue_admissible` in the canonical
Mojo module uses exact integer Cramer determinants and fails
closed on singular inputs or illegal digits. It checks only
the precise one-sided condition; a unit Pisot control passes
all its proper-prefix residue checks. This is a new exact
non-unit **necessary filter**, not BH, a good-edge word
constraint, or a guarantee of C4 synchronization.

## 5. Exact recurrent PIP counterexample to the stronger local lemma

Retire the following overstrong proposal:

> For a PIP substitution, a seed-reachable **recurrent** irreducible
> balanced-pair state whose two side-words are legal and whose left
> and right adjacent letters at a balanced newborn cut are distinct
> must give **matching source-image boundary flags**.

This is false **even on a literal, seed-reachable, noncoincident
recurrent BPA cycle**. Use the Tribonacci substitution (zero-based):

```text
sigma(0)=01, sigma(1)=02, sigma(2)=0
M = [[1,1,1],[1,0,0],[0,1,0]],
char_M(x) = x^3 - x^2 - x - 1, det(M)=1.
```

The following are **complete ordered literal** decompositions,
not synthetic quotient edges:

```text
A = (01,10)
  sigma(A)=(0102,0201)
  -> [(0,0), (102,201)]                       spans [0,1),[1,4)
B = (102,201)
  sigma(B)=(02010,00102)
  -> [(0,0), (2010,0102)]                     spans [0,1),[1,5)
C = (0102,2010)                               B's second child reversed
  sigma(C)=(0102010,0010201)
  -> [(0,0), (10,01), (20,02), (10,01)]       spans [0,1),[1,3),[3,5),[5,7)
```

Hence `A -> B -> C -> A` is an actual recurrent noncoincident
**source-state** loop; `C` and `A` are related by genuine
normalized children and occurrence ordinals. Every displayed parent
also has a `(0,0)` coincidence child: **this is productive, not a
strict closed nonproductive component**. No C4 counterexample follows.

At the interior zero-return cut `t=3` of `sigma(C)`:

```text
top literal word       0 1 0 | 2 0 1 0
bottom literal word    0 0 1 | 0 2 0 1
source address top     (index 1, within sigma(1)=02 digit 1)
source address bottom  (index 2, within sigma(1)=02 digit 0)
flags                  top is NOT image boundary; bottom IS boundary
parent prefix defect   E=(0,0,-1)
within-image forcing   c=(1,0,0)
M E + c                (0,0,0)
left adjacent letters  0 / 1 (distinct)
right adjacent letters 2 / 0 (distinct)
ordered child boundary between children ordinals 1 and 2.
```

Both parent sides `0102` and `2010` are legal factors: they occur
in `sigma^3(0)=0102010`. Thus local legality, source-state
recurrence, a genuine balanced zero return, and *immediately*
nondiagonal adjacent pairs do not couple the two supplied
`sigma`-image flags. This is a **negative control for that local
claim**, not a negative for Mossé recognizability, which compares
sufficiently long **equal** legal contexts and has no reason to
synchronize contexts of two different words.

The witness is deliberately stronger than the older productive-PIP
offset `209 <-> 429` control in *one* respect: it witnesses a full
**actual balanced-child boundary**, rather than selecting unequal
positions inside a child. It is weaker in that it does not provide a
target-avoiding strict component. Both controls must be kept.

## 6. Singular incidence counterexample (essential hypothesis)

For the existing primitive non-Pisot strict-component calibration

```text
sigma(0)=1, sigma(1)=012, sigma(2)=1,
```

the matrix is singular because its columns 0 and 2 coincide. The
irreducible balanced parent `T=(02,20)` inflates to `(11,11)` and
has an **interior bilateral source-image boundary at t=1**. This
invalidates Theorem A if injectivity is silently dropped; the canonical
Mojo checker **must refuse** the singular input, including when the
known two-state strict component is supplied separately. That
non-Pisot strict component is retained as a factorization control,
not as a positive instance of a PIP/full-rank claim.

## 7. Executable scope and replay

Canonical module:
`kernel/psc/c4_cut_alignment.mojo`.
It rebuilds literal inflated words, actual zero returns, canonical
source indices and within-image digits, source prefix Parikh defects
and the proper-prefix forcing vector. A second function rejects impossible\none-sided proper-prefix digits using exact integral-image lattice tests. It\nrejects non-irreducible parents,
a nonexistent/noninterior return, singular `M`, and inputs beyond
a documented safe machine-integer budget (image length <=64;
parent length <=4096). The mathematical theorem does **not**
require those finite executable caps.

Canonical regression:
`kernel/tests/test_c4_cut_alignment.mojo`, automatically picked up
by `kernel/run_tests.sh`; it pins all three actual A/B/C ordered
factorizations and occurrence metadata, the productive/strict
distinction, the singular refusal and malformed input failures.

An independent small standard-library Python oracle checks the same
literal word and source-address witnesses; its finite tests are not
the theorem's proof. **Preparation-time Python local replay: four
tests passed**. The Mojo compiler was unavailable locally;
**canonical Mojo checks are not reported as locally passed** and
hosted exact-head CI must be inspected before acceptance.

## 8. Completion boundary and next falsifiable C4 lemma

Theorem B supplies a **genuinely asynchronous** interior newborn
cut in every hypothetical strict PIP component. To prove C4, one
must now force `Sync_±` at **some** such actual child boundary,
using ordered hub residuals and a compatible protected legal-tower
selection. The strengthened candidate must explicitly use
strict *whole-child closure*, not merely recurrence of a productive
source SCC or agreement of separate Parikh vectors.

The first next test is to retain actual ordered adjacent child labels,
their raw signs and the `E,c,(i,r),(j,s)` data at **every**
newborn cut of an actual strict system. Ask whether the proposed
hub-phase/recognizability coupling survives the known singular
strict and productive PIP controls before making a uniform claim.
Do not extend first-child phase to all children by assumption,
infer global G1 from C4, use predecessor contraction, require
global unimodularity or independence, or import a unit-only
realization theorem into the non-unit setting.

Independent human review remains pending final validation debt.

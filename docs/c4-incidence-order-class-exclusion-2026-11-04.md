# C4 incidence-order class: all 36 sources, all 46,656 ordered systems

**Status:** Executed finite exact Python exclusion of one specified six-state
matrix template across its entire source-word ordering class. Native Mojo is
updated but not executed in this runtime; hosted exact-head acceptance and
independent mathematical review remain pending. No general C4, G1, BH, A1',
PDS or PSC status is promoted.

Continuation of PR #490 at `5a632a2e0d3fe67ec2b6cb4119450524cc1954de`.
The original one-source experiment and receipt are retained. This extension
updates the same draft rather than adding another branch to the stack.
Issue #461 remains the general research target.

## Finite result and its exact domain

Freeze

```text
M = [[1,0,1],[1,2,1],[0,1,1]],
R = M^2 = [[1,1,2],[3,5,4],[1,3,2]],
P = [R,R],       N = [[0,M],[M,0]].
```

The source substitution now varies over ALL words with incidence M:

```text
sigma(0) in {01,10},
sigma(1) in {112,121,211},
sigma(2) in {012,021,102,120,201,210}.
```

There are exactly 2*3*6=36 sources. Every source is primitive irreducible
Pisot: M^2 is positive, chi_M=x^3-4x^2+4x-2 has no possible integer root
among +/-1,+/-2, its discriminant is -44, its real Perron root beta exceeds
2, and its complex conjugates have squared modulus 2/beta<1.

Each column of N has a completely specified child MULTISET, but not an
order. The numbers of distinct orders for its six columns are
(2,3,6,2,3,6). Thus every source has exactly 1296 ordered systems and the
entire experiment has 36*1296=46,656 cases. Both source ordering and child
ordering are exhausted; no random sampling or cutoff extrapolation is used.

**Finite conclusion:** none of these cases is a literal strictly closed
system of six irreducible noncoincident balanced pairs with the prescribed
P and N. This does not exclude different P,N, additional states, different
incidence matrices, or all strict components for these 36 substitutions.

## Reused exact equation, with the varying source term retained

For each balanced state let J=(a(u)+a(v))/2, where a is the antisymmetric
scattered-two-letter count. Equal Parikh masses make J integral; exchanging
tracks leaves J unchanged. The necessary ordered-child identity is

```text
A J - J N = Omega_tau - C_sigma P,   A=wedge^2 M.
```

The previous experiment's 18x18 operator S and independently recomputed
integer inverse certificate Q are unchanged, because M and N are unchanged:

```text
det S = -596288,      SQ=QS=1694 I_18.
```

The source-order term C_sigma MUST change with sigma. The new oracle forms
it from the actual three source words on every iteration. Omitting this term
would incorrectly treat all 36 substitutions as equivalent. The accelerated
replay precomputes Q*Omega_tau and adds -Q*C_sigma*P; regression tests compare
this split against complete directly reconstructed right-hand sides.

## Census and what the 14 survivors actually mean

| Test outcome | Cases |
|---|---:|
| Forced mean-area J is nonintegral | 46,466 |
| Integral J, but no irreducible first-state word pair exists | 176 |
| First-state words exist, but their inflation contains a diagonal | 8 |
| First-state words exist and inflation is noncoincident, but its complete child row has the wrong masses | 6 |
| Unresolved necessary-condition survivors | 0 |
| Total | 46,656 |

The integral stage has 190 cases, not zero. Fourteen of them survive the
first-state word test. These are deliberately retained and replayed rather
than misreported as eliminated by integrality.

The first state always has mass (1,3,1). All 20 such words and all 400
ordered pairs are available to the independent word test. Every one of the
14 surviving cases has exactly ONE unordered irreducible word pair. Its
mean is either (1,1,1), with pair (01211,11012), or (-1,-1,-1), with pair
(11210,21011). Both physical orientations are covered: swapping the tracks
swaps every actual child pair but does not alter its mass or whether it is
a diagonal.

Complete one-step inflation of these words gives the following obstruction.
The two expected child lengths are 5 and 9, in the order prescribed by the
specific candidate row, never an arbitrary regrouping of factors.

| Source | Ordered cases surviving first-state words | Actual complete factor lengths | Failure |
|---|---:|---|---|
| 01/121/021 | 1 | 13,1 | Diagonal |
| 01/121/102 | 1 | 1,12,1 | Diagonals |
| 01/121/210 | 2 | 2,11,1 | Diagonal |
| 01/211/012 | 1 | 14 | Wrong complete child row |
| 01/211/102 | 1 | 14 | Wrong complete child row |
| 01/211/120 | 1 | 7,7 | Wrong complete child row |
| 10/112/021 | 1 | 7,7 | Wrong complete child row |
| 10/112/201 | 1 | 14 | Wrong complete child row |
| 10/112/210 | 1 | 14 | Wrong complete child row |
| 10/121/012 | 2 | 1,11,2 | Diagonal |
| 10/121/120 | 1 | 1,13 | Diagonal |
| 10/121/201 | 1 | 1,12,1 | Diagonals |

The six wrong-row cases are particularly important. No diagonal appears in
that single inflation, so this experiment does NOT label those roots
productive at depth one. Instead their uniquely determined complete
factorizations contradict the proposed child-incidence template. One may
not group or split actual irreducible factors to make N fit.

## Reproduction, independent cross-check and controls

```sh
python -m pytest -q tests/test_c4_periodic_order_lift_oracle.py tests/test_c4_incidence_order_class_oracle.py
python tests/test_c4_incidence_order_class_oracle.py
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_periodic_order_lift.mojo)
python tools/make_proof_bank.py --check
```

**Executed locally:** all 12 Python tests pass (six inherited, six new).
A separately written SymPy implementation independently reconstructed the
operator and inverse, counted word area by prefix scans, and reconstructed
all actual factors using equal prefix-count arrays. It agrees on all 36
per-source rows and the full 46,656-case totals. The committed standard
library replay does not depend on SymPy.

The original (01,121,012) regression remains exactly 1291 nonintegral and
five impossible-word cases. The extension also checks complete source and
child multisets, reversal symmetry, literal track-swap invariance, malformed
letters, wrong-incidence source refusal, and exact receipt reconstruction.
An unresolved compatible first row would be retained as unresolved, not
silently counted as a genuine realization or an exclusion.

The native driver extends the EXISTING test and inverse verifier; it does
not create a second canonical lift implementation. It directly reconstructs
the right-hand side for all 46,656 cases and uses psc.bpa.decompose on actual
source and inflated words. Fresh nested lists are explicitly transferred
by ownership. It has not been compiled in this runtime because Mojo/pixi
are absent; Python success is not native acceptance.

Receipt: `evidence/c4-incidence-order-class-2026-11-04/receipt.json`, containing
all 36 source counts and complete first-state receipts for the 14 survivors.
The exact-head workflow reconstructs and compares both the original receipt
and this extension's receipt. Generated Proof Bank checks remain enabled.

## Prior art and remaining boundary

This uses standard Sylvester disjoint-spectrum and scattered-subword
methods already discussed in the parent note: Nevanlinna (2019),
DOI 10.7153/oam-2019-13-62; Mateescu, Salomaa and Yu (2004),
DOI 10.1016/j.jcss.2003.04.001. No novelty is claimed for those methods.
The new contribution is the complete 36-source audit and its explicit
literal-row rejection of candidates that pass all preceding local tests.

Main has separately advanced through the referee-dossier repair PR #488.
This update remains on #490's research stack and neither merges nor
certifies the parent PRs #484/#486. The general strict-carrier productivity
problem in #461, global extraction, and PSC remain unproved by this result.
The next useful extension must vary P or N, or supply a uniform argument;
simply repeating this completed word-order class would add no coverage.

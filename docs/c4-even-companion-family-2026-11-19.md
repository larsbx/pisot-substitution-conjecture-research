# An unbounded family inside the even rank-two residue

**New literal theorem.** For every natural `r >= 3`, the literal substitution
`sigma_r = (1, 2, 100 2^r 1)` has no finite strict system. The proof supplies
all three letter-pair witnesses and applies the existing cut-pair theorem.
It needs no geometric or Pisot hypothesis. Every even `r >= 4` belongs to
the nilpotent, complete-square class left by #619, as established by the
separate arithmetic and eventual-range derivation below.

## Literature decision

Research base: `c0231e0fd64d9eee7f7bb798042d9966276e4cd6` (main after
#617, #618, #619 and #620). The [even-stack reduction](c4-even-stack-residue-2026-11-19.md)
is already merged; its 96 short-image controls are not a new result here.
The proposal is also integrated and verified against main
`017969364269c116aaa5873bfcba6c9f1b1ba7e5` (#621); that target-topology
change does not alter the literal family proof.

**Proposed intermediate claim.** For

```text
sigma_r: 0 -> 1, 1 -> 2, 2 -> w_r = 100 2^r 1,
```

every even `r >= 4` is an irreducible cubic Pisot substitution with
determinant two, nilpotent incidence modulo two and complete eventual range
`K_{2,2}`. Nevertheless its two periodic first-letter rays have a literal
strong coincidence at level three. Test and prove a uniform prefix witness,
rather than extrapolating the finite census to arbitrary substitutions.

| Primary source | Hypotheses and decision |
| --- | --- |
| [Barge (2015), Lemma 20 and Theorem 22](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | The rank lower bound uses odd norm in the mod-two eventual-rank step. It does not give five cohomology classes at even norm. Keep the published stack and covering results as geometric inputs. |
| [Barge–Diamond (2008), Theorem 4](https://arxiv.org/pdf/math/0702669) | The eventual-range exact sequence applies without odd norm. For nonsingular irreducible cubic incidence and connected eventual range, the rational dimension is `3 + beta_1(ER)`. A square therefore gives dimension four, without a spectral conclusion. |
| [Barge–Kellendonk–Schmieding (2012), Corollary 3 and Theorem 5](https://arxiv.org/pdf/1204.1432) | The integral eigenfunction injection and torsion-free cokernel support #619's dimension-three obstruction, but do not remove its fourth, winding class. |
| [Barge–Bruin–Jones–Sadun (2012), Theorem 6](https://www.mat.univie.ac.at/~bruin/papers/HPC.pdf) | The cited norm-independent rank-two exclusion assumes homological degree one. It is not a cubic degree-four-cohomology theorem. |

**Decision: proceed with the narrowed family.** The general parity-free
upper bound and the nilpotent/grouped-square residue are existing written
results. The family extends #619's `r = 4` control to unbounded image length.
The new formal target is the exact word witness and its equal prefix
Parikh vectors. The Thue–Morse/period-doubling control still prevents
discarding odd homoclinic winding without an additional cubic argument.
No universal exclusion or pure-discrete-spectrum claim follows from this
one family.

## Work shown

### Assumptions and hypotheses

The literal word and no-strict-system claims use only `r >= 3`; they do not
assume primitivity, Pisot type, coincidence rank, recognizability or geometric
realization. A strict system has the existing repository meaning: a finite,
nonempty set of irreducible balanced, noncoincident word pairs, closed under
all literal children. This is not a bounded search over possible systems.

The even-residue interpretation specializes to even `r >= 4`. The rational
cohomology calculation uses Barge–Diamond's published exact sequence;
the no-strict-system theorem itself does not use that calculation.

### Derivation / reduction

#### Incidence, primitivity and Pisot type

The actual column incidence matrix and its characteristic polynomial are

```text
M_r = [[0,0,2], [1,0,2], [0,1,r]],
p_r(t) = t^3 - r t^2 - 2t - 2,       det M_r = 2.
```

The rows of its third power are

```text
(2, 2r, 2r^2+4),
(2, 2r+2, 2r^2+2r+4),
(r, r^2+2, r^3+4r+2).
```

They are positive for every `r >= 1`, proving primitivity. The only possible
rational roots of the monic cubic are `1,-1,2,-2`. Their evaluations are
`-r-3`, `-r-1`, `2-4r`, `-4r-6`, respectively, none zero for `r >= 1`.
The cubic is therefore irreducible. Its discriminant is

```text
-8r^3 + 4r^2 - 72r - 76 < 0.
```

There is one real root and a nonreal conjugate pair. Since `p_r(2) < 0`,
the real root `beta` is greater than two. The product of all roots is two,
so each nonreal conjugate has squared modulus `2/beta < 1`. Thus the
substitution is irreducible cubic Pisot for every `r >= 1`.

For even `r` its reduction modulo two is the shift matrix
`[[0,0,0],[1,0,0],[0,1,0]]`, whose cube is zero. These are written uniform
arithmetic deductions. The bounded executable checks use the existing
exact PIP predicate, not floating-point eigenvalues.

#### The complete square

Both endpoint maps are `f = (1,2,1)`. Their periodic letters are precisely
`1,2`. Internal legal bigrams include `10,00,02,21`, and the legal endpoint
map has the orbits `02 -> 11 -> 22 -> 11` and `21 -> 12 -> 21`.
Consequently all four edges on the periodic letters survive, and no other
vertex is periodic. The eventual range is exactly `K_{2,2}`. It is connected
and has one independent cycle. Barge–Diamond's formula therefore gives
`dim H^1(Omega_sigma; Q) = 3 + 1 = 4`.

This description concerns this particular family. The original eventual
range of an arbitrary specimen in #619's residue need not be complete;
only its grouped image must be the square.

#### Uniform literal witness

Write `w = 100 2^r 1` and `v = 211 w^r 2`. Direct substitution gives

```text
sigma_r^3(1) = v,
sigma_r^3(2) = w 22 v^r w.
```

For `r >= 3`, the prefixes

```text
P = 211 w 10022,          Q = w 22211100
```

are followed by the same letter `2` in these two words. On the first track
the matching letter is the third `2` in the second copy of `w` within `v`;
on the second track it is the first `2` in the first `w` within the first
copy of `v`. Both prefixes have length `r+12` and Parikh vector
`(4,5,r+3)`. This proves a left strong coincidence at level three for
letters `1,2`, using actual ordered words rather than incidence alone.

The remaining unordered letter pairs are immediate consequences:

| Pair | Level | Exact reason |
| --- | --- | --- |
| `0,2` | 1 | Both images start in `1`; the prefixes are empty. |
| `1,2` | 3 | The explicit balanced prefixes above, followed by `2`. |
| `0,1` | 4 | `sigma_r^4(0)=sigma_r^3(1)` and `sigma_r^4(1)=sigma_r^3(2)`. |

Swap symmetry supplies the opposite ordered pairs. The existing
`Psc.StrictSystem.no_strictSystem_of_strongCoincidence` applies to all
finite systems, without a geometric assumption. The new
`Psc.EvenCompanion.no_strict_system` specializes it to every `r >= 3`.
The even theorem uses `r=2n+4`, with arbitrary natural `n`.

The [word module](../proof/PscVerif/PscVerif/EvenCompanionWords.lean) proves
the actual iterate decompositions, equal counts, equal lengths and the
prefix witness. The [family module](../proof/PscVerif/PscVerif/EvenCompanionFamily.lean)
uses the existing witness and strict-system definitions and proves the
exclusion. Their canonical declarations and proof bodies are extracted
byte-for-byte into `StrictSystemCore`; the full `StrictSystem` module imports
and re-exports them. This removes unrelated sector imports from the literal
proof without introducing a duplicate definition or an axiomatized notion
of strong coincidence.

### Evidence and replay

The canonical [Mojo regression](../kernel/tests/test_even_companion_family.mojo)
checks the sixteen even parameters `r=2,4,...,32` with the existing exact
PIP and eventual-range implementations. It checks 48 letter-pair witnesses
against a separate literal search. For `r >= 4` the levels in pair order
`02,12,01` are `1,3,4`. The explicit words and equal prefix counts are
also independently replayed by the Python oracle; this finite replay is
not the proof of the unbounded result.

The final source bindings, compiled axiom audit, integrity checks and
replay logs are in the accompanying evidence packet. No new hosted
acceptance result is asserted.

### Negative controls

- `r = 4` reproduces the merged `1/2/10022221` witness: index 16,
  letter 2, prefix Parikh `(4,5,7)`.
- At `r = 2`, the proposed level-three index 14 has different letters
  `1` and `2`. The formula genuinely needs its lower bound. A separate
  finite replay finds the `1,2` witness at level four, index 20, letter 2,
  and Parikh `(6,7,7)`; the `0,1` witness is at level five. This finite
  exception is not included in the unbounded Lean theorem.
- The odd parameter `r = 3` verifies the same word formula while its
  matrix is not nilpotent modulo two. The literal theorem does not need
  the parity assumption. All family matrices still have determinant two.
- Image and word caps reject before concluding; a refused search never
  becomes a negative witness or a purported strict system.

### Non-claims / remaining gaps

The arbitrary nilpotent cubic class, its odd homoclinic winding, higher
coincidence ranks, universal C4 and PSC remain open. Strong coincidence and
absence of finite strict systems are the proved literal conclusions here;
no termination of arbitrary infinite searches or pure discrete spectrum
theorem is asserted. Publication and merge require the user's approval of
the completed local changes.

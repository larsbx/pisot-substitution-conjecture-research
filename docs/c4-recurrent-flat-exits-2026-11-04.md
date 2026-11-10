# C4 recurrent flat rows and outgoing Parikh mass

**Status:** Repository-proved exit-mass lemma and exact finite negative.

[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@e1ef4b1efe70d440d36b24aebd3bb8da66b1e164`, including
[#462](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/462).

## Literature and scope

Barge–Diamond's [Theorem 1](https://doi.org/10.24033/bsmf.2433) supplies an
eventually coincident letter pair. A positive witness consists of equal
prefix Parikh vectors followed by the same letter in equal iterates.
Sirvent–Solomyak's [balanced-pair and overlap algorithms](https://citeseerx.ist.psu.edu/document?doi=ac6481cf41605ed271988fa1354fbf057680ba4e&repid=rep1&type=pdf)
distinguish recurrence from termination with coincidence.
Hollander–Solomyak's [two-letter result](https://doi.org/10.1017/S0143385702001384)
uses balanced pairs in the two-letter Pisot setting. Identifying the two
letters of a good edge by a map of alphabets does not supply a two-letter
substitution quotient. These inputs support the witness semantics and
scope separation. They do not supply a three-letter flatness theorem.
Proceed with an exit-sensitive reduction and a test of the version that
assumes recurrence and checks all outgoing rows.

## Candidate and exact intermediate lemma

**Open candidate.** Let a primitive irreducible ternary Pisot substitution
have a supplied finite SCC of actual irreducible noncoincident balanced
pairs. Require complete strict child closure and a witnessed
Barge–Diamond good edge. At each source and every child ordinal, retain the
actual factor, both physical occurrence addresses and the incoming
orientation. Require that the complementary hub occurs on exactly one
side at each initial pair, with the same hub-side residual bit (zero or
one) on every occurrence in every ordered child row. Then either a common
nonzero rational functional annihilates the Parikh masses and its line
is invariant under right multiplication by the incidence matrix, or some actual
one-step interior newborn has right pair in `Sync_+` or left pair in
`Sync_-`. Both conclusions would exclude the stipulated strict system.
This implication remains open.

**Lemma (exit mass).** For any supplied nonempty finite set of actual
irreducible balanced states, let `P` contain their masses, `N_in` count
only children that stay in the set after normalization, and let column
`E_j` sum the masses of **all other occurrences** in the full ordered
child word of parent `j`, including diagonal exits. Write
`W = im_Q(P)`, `U = im_Q(E)`. Then
```text
MP = P N_in + E,
W + MW + ... + M^k W = W + U + M U + ... + M^(k-1) U   (k >= 1).
```
Each column identity counts letters on one physical side. The two sides
of each balanced child have the same mass, so the normalization signs
have no effect. For the span identity, `W+MW = W+U` follows from
`MP - E = P N_in`. Applying `W + M(·)` and using this base identity gives
the formula by induction. The left side is the span of all root masses
and all complete generation totals through depth `k`, counting repeated
occurrences. Individual descendant masses can span a larger space at the
same depth.

If the cubic characteristic polynomial is irreducible, every proper
nonzero cumulative span strictly grows at the next step. Equality would
make that span `M`-invariant. For `r = dim W` this forces rank three by
depth `3-r`. In particular, if `r=2`, the primitive normal to `W`
has nonzero pairing with the **summed** exiting mass of at least one
actual source row, even when different exits could have cancelled.
If `E=0`, closure gives the existing invariant-plane obstruction at
rank two. Flatness and nonsynchronization of all newborns in the
recurrent rows alone do not make `E=0` or constrain it to `W`.

## Exact negative to replacing closure by recurrence

Take `0 -> 1, 1 -> 02, 2 -> 220`. Its incidence rows are
`(0,1,1), (1,0,0), (0,1,2)`, with `M^4>0` and
`chi=x^3-2x^2-x+1`. The only possible rational roots are ±1, neither
of which is a root. Exact signs isolate the three roots in
`(-1,0), (0,1), (2,3)`. The genuine good edge is `{0,2}`. At
depth four and zero-based position 3 in both images, the letter is
`2` and the preceding mass is `(1,0,2)` on both sides. The
top/bottom digit paths from 0 and 2 are `[0,1,0,1]` and
`[0,0,1,0]`.

The normalized SCC consists of `T=(0222022012,1220220220)`, reached
from swap `(01,10)) by the literal ordinal path `[0,0,0,0,0]`.
Both words occur in `sigma^7(0)` at positions 18 and 0. For
the displayed physical orientation the complete child row is

| Ordinal | Raw child | Hub residual | Parikh mass |
| --- | --- | --- | --- |
| 0 | `(1220220220,0222022012)` | 1 | `(3,1,6)` |
| 1 | `(1220220,2022012)` | 1 | `(2,1,4)` |
| 2 | `(102220,202201)` | 1 | `(2,1,3)` |

Ordinal 0 returns with swapped orientation. Its next ordinal 0 returns
in the displayed orientation, so both oriented representatives recur.
All children are noncoincident and the entire row flips the physical
hub side. The complete cut word is `[0,10,17,23]`. Both newborns
have left pair `(0,2)` and right pair `(1,2)`. The prefix map
`[1,0,2]` and suffix map `[1,2,0]` are permutations, so neither
pair synchronizes via its endpoint map. In particular the interior
good-edge witness above does not arise from iterating a prefix map.

| Right ordinal | Cut | Top source and digit | Bottom source and digit |
| --- | --- | --- | --- |
| 1 | 10 | `(4,0)` | `(4,1)` |
| 2 | 17 | `(7,0)` | `(7,1)` |

The determinant of the ordered child masses is −1. Thus no nonzero
functional can annihilate the complete row, even though the recurrent
state alone has rank one. The sum of the two exiting columns is
`e=(4,2,7)`, and `det[p,e,Me]=−1` for `p=(3,1,6)`. One
step of aggregate propagation has rank two, and two steps have rank
three. The actual ordinal path `[2,1]` reaches diagonal `(2,2)`.
A completed reachability search from the parent verifies that neither
exit returns to the SCC. The Python replay visits 18 normalized states
with diagonal terminals. Both replays cap the number of states at 64
and the state length at 32 and require a completed search. The example refutes the candidate with strict child closure
replaced by recurrence and flatness/nonsynchronization on **every**
outgoing child of the recurrent parents. It is a productive system.

## Replay and claim status

Run the canonical and independent checks from the repository root.

```sh
(cd kernel && pixi run mojo run -I . tests/test_c4_recurrent_flat_exits.mojo)
(cd kernel && pixi run mojo run -I . tests/test_c4_complete_cone_hub_audit.mojo)
(cd kernel && pixi run mojo run -I . tests/test_c4_two_generation_rank.mojo)
python -m pytest -q tests/test_c4_recurrent_flat_exits_oracle.py \
  tests/test_c4_complete_cone_hub_audit_oracle.py tests/test_c4_two_generation_rank_oracle.py
```

The reducible non-Pisot `10/102/211` strict rank-two control and the
productive irreducible Pisot `01/12/021` flat depth-two control remain
mandatory. The first isolates the spectral obstruction with no exits.
The second isolates the depth-two boundary at phase zero. The new example
isolates the recurrence versus closure boundary at phase one. The exit
mass lemma has an algebraic proof. The examples have exact executable
checks and independent Python reconstruction. The lemma has no Lean
formalization. No governed claim changes.
General C4, G1 extraction and PSC remain outside this result.

# C4 addressed coincidence to a synchronizing newborn

**Status:** Repository-proved transport lemma and exact finite replay.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

## Literature and scope

[Barge–Diamond](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
use equal-prefix coincidence witnesses. The
[Sirvent–Solomyak](https://web.math.pmf.unizg.hr/~sonja/PDS-final.pdf)
balanced-pair algorithm cuts literal inflated words at coincident
prefixes. [Akiyama–Lee](https://arxiv.org/abs/1003.2898) distinguish
overlap descent from finding a coincidence. The repository's
[target packets](target-aware-bpa-diagnostic-2026-10-02.md)
already retain both source addresses and discard split children.
Proceed with the specific converse needed for C4. A supplied coincidence
certificate cannot split, and its first diagonal gives an interior
one-step newborn even when the coincidence lies at an exterior endpoint.

## From an addressed witness to an interior cut

**Lemma.** Let `T` be an actual irreducible noncoincident balanced
pair under a nonerasing substitution. Choose one source occurrence on
each side and a common positive depth. Supply their two descendant
addresses at that depth. Suppose the addressed descendants have the
same letter and equal Parikh prefixes in the full words. Then some
literal irreducible descendant of `T` has a one-step interior newborn
with a right pair in `Sync_+` or a left pair in `Sync_-`. The parent
and cut can be read from the addressed factor path.

Every balanced factor boundary has equal prefix Parikh vectors on the
two sides. Its image is again a common cut, and a letter before or after
that cut remains on its own side through all further inflations. If
the two marked ancestors entered different factors at any intermediate
depth, an intervening inherited cut would keep their descendant positions
distinct. Equal Parikh prefixes at the endpoint of the witness imply
equal positions, by summing the coordinates. Thus the marks always
enter the same factor. Trimming the two sides to that factor subtracts
the same Parikh vector from each prefix. The trimming preserves both
the equality test and the literal next digits.

At the witness depth the equal prefixes and equal marked letters give
consecutive zero-return cuts, hence a one-letter diagonal factor.
Follow the common factor path to the **first** such diagonal. The
preceding parent is irreducible noncoincident, with length at least two.
Its nonerasing image has length at least two. Therefore the one-letter
diagonal has an adjacent interior cut in that parent image. If its
left cut is interior, the right pair at that cut is already diagonal.
Otherwise its right cut is interior and the left pair is already
diagonal. An interior cut is newborn because the parent is irreducible.
Both tests use the actual one-step parent image. The argument uses
integer prefix equalities and order only.

Consequently, productivity of **one** physically forced overlap from
[#466](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/466)
would suffice for the one-step C4 conclusion on the supplied strict
component. Strict closure keeps every parent on the extracted path
inside that component. The remaining obligation is to obtain a
coincidence witness for at least one forced overlap under the fully
strict hypotheses.

## Exact replay

The canonical checker validates every digit against its actual source
letter and consumes the complete literal cut word at each step.
An out-of-range digit, split factor, absent final diagonal or exceeded
word budget is refused. The independent oracle expands the full
untrimmed words with ancestor labels and reconstructs the responsible
parent and cut separately. The phase-zero and recurrent Pisot controls
use the physical overlap addresses from #466. The reducible strict
control and the productive finite-cone control remain in the exact-head
workflow. Bounded tests check the transport, while the proof above has
no depth or state-count bound. No governed status changes.

| Substitution | Child ordinal path | Parent | Interior cut | Test |
| --- | --- | --- | --- | --- |
| `01/12/021` | `[0,1,2]` | `(02112,21120)` | 11 | `Sync_+` |
| `1/02/220` | `[2,2,1]` | `(202201,012202)` | 4 | `Sync_+` |

The last ordinal selects the diagonal in the displayed parent's
image. The tests also pin the case where the first diagonal is at
the left end and the adjacent newborn must use `Sync_-`.

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_addressed_newborn.mojo)
python -m pytest -q tests/test_c4_addressed_newborn_oracle.py
```

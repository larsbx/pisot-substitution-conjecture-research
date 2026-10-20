# Length moments at the two open proof interfaces — literature gate

Date: 2026-10-20. Decision: **proceed with an exact interface lemma and
counter-controls; do not start another strong-coincidence census.**

The proposed claim is elementary: for an incidence matrix with irreducible
degree-d characteristic polynomial, the rows `1^T M^j`, `0 <= j < d`,
distinguish every rational Parikh defect. Apply this to (a) inflation of one
specified common-block occurrence in two fixed rays and (b) one specified
pair of prefix addresses in a boundary-hitting witness. The two existence
questions, #138 and #139, remain open. This is a change of coordinates and a
test of proposed arguments, not a new condition known to force a hit.

## Primary-source stop/go check

| Source inspected | Transfer | Boundary and decision |
| --- | --- | --- |
| Barge–Zamboni, [Central sets and substitutive dynamical systems](https://arxiv.org/html/1301.5745v1), Proposition 4.8 and section 5 | Proximal fixed points of an irreducible primitive Pisot substitution are strongly coincident; prefix addresses retain their actual occurrences. | Their proof uses finite proximal fibers. Common words at independently selected positions, or one repeated germ, do not supply proximality. Inspect the **same-position drift** before attempting a pumping lemma. |
| Akiyama–Lee, [Algorithm for determining pure pointedness of self-affine tilings](https://arxiv.org/pdf/1003.2898), introduction and overlap construction | A complete occurrence/overlap decision object can certify a particular system under its geometric hypotheses. | A coordinate identity supplies neither complete seed coverage nor a universal hit. Keep parent letters and proper-prefix choices in the verifier. |
| Minervino–Thuswaldner, [The geometry of non-unit Pisot substitutions](https://aif.centre-mersenne.org/item/10.5802/aif.2884.pdf), sections 3, 6 and 9 | Non-unit systems require the finite-place factors in geometric representation. | Exact integer-vector equality preserves those data; a scalar approximation or equality modulo a quotient does not. The proposed test uses an injective rational map, not an Archimedean truncation. |

The matrix fact is the standard cyclic-vector/Krylov argument, proved directly
in the companion note; no novelty is claimed for that linear algebra. The
new contribution is its explicit use at these repository proof interfaces,
with executable occurrence validation and controls against a shorter window.

## Scope and negative controls

The kernel checks full rank directly and refuses singular observation maps;
it does not infer PIP merely from full rank. A primitive reducible constant-
length example has nonzero defects invisible at **every** length level.
A PIP example will pin a nonzero defect invisible at the first two levels,
showing why one or two scalar observations cannot silently replace three.
Malformed addresses and a zero-offset target with unequal letters must not
receive a strong-coincidence receipt. No word expansion budget can be treated
as a nonexistence verdict.

The existing side-notes ledger excludes cycle algebra, quotient-depth sieving,
and repeated finite germs as standalone closure arguments. This contribution
does not reopen those routes or duplicate the merged endpoint-sign spike.

# P1a alternating-E transport: stop/redirect gate — 2026-10-02

**Status:** literature stop/go note with an exact finite counter-calibration.
It moves no theorem status. #84, #138, G1 and PSC remain open.

## 1. Proposed claim

`docs/p1-two-route-map-2026-10-01.md` §5 named **A-altE interior-witness
transport** the best immediate target. In the alternating-E template
(`h(c)=c`, `h(a)=b`, `h(b)=a`, `G={a,b}` Barge–Diamond good) it asks to

> show that the interior Barge–Diamond witness for `G` occurs as an
> offset-zero pair below a bad hub edge `E_a={a,c}` or `E_b={b,c}`, or derive
> a contradiction with closed nonproductivity
> (`docs/p1a-aligned-cycle-normal-form-2026-10-01.md` §5).

The first disjunct is the transport mechanism: coincidence of the hub star is
to be routed through `G` at a zero-return boundary.

## 2. Prior art and terminology

- Barge–Diamond, *Coincidence for substitutions of Pisot type*, Bull. SMF 130
  (2002): every Pisot substitution has an eventually coincident letter pair;
  strong coincidence on two letters. This is the only input the template uses.
- Arnoux–Ito, *Pisot substitutions and Rauzy fractals*, Bull. Belg. Math. Soc.
  8 (2001): the strong coincidence condition, stated for **every** pair.
- Barge–Kwapisz, *Geometric theory of unimodular Pisot substitutions*, Amer. J.
  Math. 128 (2006), and Sirvent–Solomyak, *Pure discrete spectrum for
  one-dimensional substitution systems of Pisot type*, Canad. Math. Bull. 45
  (2002): coincidence and overlap-coincidence formulations.
- Akiyama–Barge–Berthé–Lee–Siegel, *On the Pisot substitution conjecture*, in
  *Mathematics of Aperiodic Order*, Progr. Math. 309 (2015): survey of the
  equivalences.

We found no theorem making eventual coincidence of letter pairs transitive, or
transporting one good pair's witness to another pair. The transport lemma
would be such a statement in the special type-E endpoint configuration.

## 3. Exact counter-calibration

Canonical Mojo: `mojo/psc/alternating_e_exit.mojo`,
`mojo/tests/test_alternating_e_exit.mojo`. For each corpus specimen whose
endpoint map is alternating-E, the overlap closure of `(a,c,0)` and `(c,a,0)`
is built in the exact Perron field (`{b,c}` is the first child of `{a,c}`, so
both bad edges are covered). Independently reproduced by the Python overlap
oracle.

| standing 4,554-member corpus | specimens |
| --- | ---: |
| alternating-E endpoint map | 294 |
| an offset-zero `G` vertex lies below the hub star | 228 |
| **no** offset-zero `G` vertex lies below the hub star | **66** |
| a coincidence is reachable on a path avoiding offset-zero `G` | 294 |

Named witness, letters `0,1,2`: `0 -> 1`, `1 -> 02`, `2 -> 220`. Hub `2`,
`G={0,1}`. The zero-return pairs of `sigma^n(0)` against `sigma^n(2)` are
`(1,2)`, `(0,2)`, `(1,2)` for `n=1,2,3`, and at `n=4` the hub coincides with
itself, `(2,2)`. `{0,1}` never appears at offset zero.

The first offset-zero pair outside the hub star is not uniform across the 294
specimens: `cc`, `aa`, `bb`, `ab` and `ba` all occur as first exits, alone and
in combination.

## 4. What transfers and what does not

- Every corpus specimen is productive, so the transport lemma is not
  *refuted*: under closed nonproductivity its conclusion may still hold.
- What is refuted is the **unconditional mechanism**. PIP plus a good `G` does
  not force `G` to appear at offset zero below the hub star (66 specimens), and
  coincidence of the hub star never needs `G` (294 of 294). A proof whose
  argument uses only PIP, the endpoint template and the interior `G` witness
  would prove the first disjunct for these specimens, which is false.
- A valid proof must therefore use nonproductivity of the closed component
  substantively; the interior `G` witness alone is not the lever.

## 5. Decision

**Redirect.** The A-altE target is no longer "transport the `G` witness". It
is the same kind of closed-component forcing as A-fixed: show that a closed
nonproductive component containing the alternating hub star is impossible,
with the hub's self-coincidence `(c,c)` and the good-letter
self-coincidences `(a,a)`, `(b,b)` as admissible exits alongside `G`.
A-altE consequently loses its claimed advantage over A-fixed (a guaranteed
witness that can be transported); the two aligned templates should be
attacked by one closed-component argument rather than in the order of
§5 of the route map.

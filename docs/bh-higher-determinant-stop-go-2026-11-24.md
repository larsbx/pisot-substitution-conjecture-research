# Higher determinant BH source review

This continues the unpublished Class-A carrier work on the PR #655 base
`4da29580be506ee25e039fcd675c2af74f8a5fe6`. The current Class-C review
packets address both signs of the determinant-two Class-C swap-seed domain.
The target here uses a different literal substitution, with determinant
`r` that can be arbitrarily large.

## Work shown

### Assumptions and hypotheses

Take the primitive irreducible Pisot family
`sigma = (1, 0 1^k 2, 0^r 1)`. Investigate the actual overlap descendants
of the ordered seed `01/10` for `r >= 4` and `k = r, r+1, r+2`. An overlap
carries both letters and the full integral difference of the actual prefix
counts. The BH target is a path to zero integral displacement for each
required strict overlap. A typed coincidence additionally requires equal
selected letters.

Also investigate a reusable implication for literal ordered seeds. A single
bound on the physical lengths of all actual irreducible factors of all
iterates should imply a zero hit from every actual strict overlap at every
level. The construction should recover the child path from the original
marks and should require only positive, exactly scaling lengths and
expansion greater than one.

### Derivation / reduction

- Sirvent–Solomyak, Section 5 and Theorem 5.6, relate termination of the
  prefix balanced-pair algorithm to half-coincidences using bounded
  gaps. Their contract concerns a shifted fixed-point prefix seed. The
  present target uses a finite literal ordered pair, full Parikh vectors,
  and explicit ancestry of an overlap.
  [Paper](https://doi.org/10.4153/CMB-2002-062-3)
- Barge–Štimac–Williams, Corollary 2, gives a spectral application once one
  actual swap BPA terminates with coincidence. Carrier closure and a zero
  displacement should be proved before using this criterion. A zero
  displacement supplies a half-coincidence, and the published BPA criterion
  additionally needs label coincidence.
  [Paper](https://doi.org/10.3934/dcds.2013.33.579)
- Akiyama–Lee, Section 3, give a finite overlap graph under the Meyer
  hypothesis. Their finiteness argument and graph tests distinguish the
  finite graph from the existence of a coincidence exit. Here the
  existing Pisot contraction supplies physical and stable bounds on the
  integral overlap states. The remaining question is their actual zero
  exits.
  [Paper](https://arxiv.org/abs/1003.2898)
- Barge's initial-injectivity and final-constancy theorem does not apply
  directly to these literal endpoint maps, even after taking powers.
  [Paper](https://doi.org/10.3934/dcds.2016.36.1159)

The existing [bivariate carrier](c4-two-parameter-carrier-2026-11-14.md)
covers `k >= r+3`. Its word identities contain a repeat of length
`k-r-3`. The proposed residual proof must therefore use a different
partition or a direct overlap argument. The
[bilateral seam result](c4-bilateral-newborn-family-2026-11-14.md) supplies
a consequence once the forward factors are known finite.

### Evidence and replay

Proceed first with bounded exact exploratory replays in the three bands,
with finite caps and the actual ordered occurrences retained. Use them
to choose a symbolic proof target. For the bounded-factor implication,
look for a cut in the interior of the expanded common interval, then lift
the two right-hand marks back through the literal substitution. Reuse the
actual mark ancestry and the existing cut/factor interfaces. A complete
symbolic proof or a checked Lean theorem is required for a uniform claim.

### Negative controls

The parent row at `r=4,k=6` refutes extension of the existing bivariate
word identity by clipping a negative repeat. The determinant-three
`k=3` example also rules out requiring an immediate coincidence in every
balanced-pair row. Keep endpoint contact excluded by the strict overlap
predicate. A cut found outside the expanded overlap cannot serve as a
zero hit for that particular source.

### Non-claims / remaining gaps

This is a stop/go record for the residual determinant-family bands and
for a scoped bounded-gap implication. A finite exploratory replay
establishes no uniform result in `r`. The universal ternary BH, A1′,
C4 and PSC questions remain separate.

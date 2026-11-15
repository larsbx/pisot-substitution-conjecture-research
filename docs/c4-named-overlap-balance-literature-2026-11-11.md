# Named overlap balance: pre-code source check

Decision on 2026-11-11: **proceed with the finite literal-count specialization**
of the existing dual mass theorem. The baseline is main
`765bb39c83035b5ccacbc8115ecc26acc4111865` (merged #548). This note is recorded
before the new proof implementation.

## Exact target

For each of the two actual substitutions `1/021/001` and `1/012/001`,
each even power `k = 2r`, and its already constructed full or nondiagonal
finite packet domain, let `T(p,u)` count **all literal inverse occurrences**
from `p` to `u` whose endpoints lie in the domain. No target deduplication
or track-swap quotient is used. Let `v(p)` be the finite product-Haar
measure of the actual overlap and `h(p)` its strictly positive physical
interval overlap length. Derive

```text
beta^k v <= T v,       T^t h <= beta^k h,
T v = beta^k v,        (beta^k h - T^t h)(p) v(p) = 0.
```

The first inequality comes from the actual finite covers and Haar scaling
of #548. The second comes from complete physical interval subdivision,
retaining only the children inside the chosen finite domain. Finite
double counting and positivity then give the two equalities. Compose these
facts with the existing source-component loss theorem. A loss hypothesis
remains a hypothesis until an authenticated literal certificate supplies it.

## Primary sources and transferred hypotheses

1. Minervino and Thuswaldner, *The geometry of non-unit Pisot
   substitutions*, [primary preprint](https://arxiv.org/pdf/1402.2002),
   Theorem 8.3(i), equation (29). Their tile-measure inequality becomes an
   equality by pairing with Perron data. This is the closest standard
   construction. The present argument uses the repository's original
   compact matrix-adic carrier and its proved normalization; it imports no
   unproved identification with the paper's completion-field space. It
   also does not transfer positivity of tiles or strict cross-letter
   intersections from that representation.
2. Akiyama and Lee, *Algorithm for determining pure pointedness of
   self-affine tilings*, [primary preprint](https://arxiv.org/pdf/1003.2898),
   section 4, equation (4.2), Theorem 4.1. Literal digit pairs are multiple
   edges. Their spectral criterion requires a self-affine tiling and the
   Meyer property. A finite matrix or a conservative component does not
   establish those hypotheses, so no pure-point conclusion is imported.
3. Tam and Schneider, *On the core of a cone-preserving map*,
   [author PDF](https://people.math.wisc.edu/hans/paper_archive/scanned_papers/hs106.pdf),
   printed page 484, Theorem 2.1 and preceding graph conventions. Ordinary
   nonnegative-matrix conclusions depend on directed accessibility. The
   existing repository theorem uses source components for its row-to-ancestor
   convention. Reversing this orientation or treating an algebraically
   allowed component as positive geometric measure is not justified.

The finite pairing argument and source-component obstruction are already
proved in `PhysicalMass.lean`. The new contribution is their composition
with actual named sets, exact occurrence counts, and physical subdivision.
It is not a new Perron theorem or a general PSC result.

## Required controls and non-claims

- Distinct position pairs with the same endpoint remain distinct summands.
- A complete incoming cover does not imply forward closure; omitted positive
  physical children may produce a deficit, and zero-mass omissions do not.
- Strictly positive physical weights are necessary for saturation. Nonempty
  compact overlaps do not supply positive product-Haar measure.
- Power zero is an identity/conservative control, not a strict loss witness.
- A conservative source component is necessary for a surviving overlap, not
  sufficient to construct positive overlap. Source loss is not sink loss.
- Existing `OccurrenceMassStrict.full_forward_conservative` shows that a
  complete strict child-closed support alone supplies **no** positive loss.

The proof must retain the two actual period-two words, the original `H_M`,
and the full parent/position identities. It must neither turn the chosen
noncomputable finite box into an executable graph certificate nor identify
it with an archived graph without a separate refinement. Strict-root
positivity, source-loss certificate construction, universal C4, BH, A1', G1
and PSC remain separate obligations. Governed claim statuses are unchanged.

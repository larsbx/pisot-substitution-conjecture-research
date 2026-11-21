# Source decision for periodic finite differences in the literal hull

The [even rank-two reduction](c4-even-stack-residue-2026-11-19.md)
gives nilpotent incidence modulo two and a periodic pair in the unordered
stack factor with two asymptotic tails. Test what that incidence condition
forces when a finite difference is represented by two original words.
For a power `τ` whose image letter counts are all even, the proposed
endpoint is

```text
τ(u) = L u R  and  τ(v) = L v R  imply  u = v.
```

| Primary source | Scope used |
| --- | --- |
| [Lejeune–Rigo–Rosenfeld (2020), §1](https://arxiv.org/abs/2001.11732) | Scattered-subword multiplicities and binomial equivalence. Here the same coefficients are taken modulo two and used at every degree. |
| [Barge–Diamond–Swanson (2009), §2](https://arxiv.org/pdf/0804.0930) | The asymptotic tilings of interest can be represented by periodic tilings under a suitable common recentering and substitution power. In the proposed literal argument the marked common vertex is specifically the inflation centre. |
| [Barge–Diamond (2008), Theorem 4](https://arxiv.org/pdf/math/0702669) | The eventual-range graph and its cycle term retain seam data beyond the incidence cohomology. The proposed word obstruction concerns an actual finite patch and leaves the seam cycle term available. |
| [Barge (2015), Example 16 and Theorem 17](https://arxiv.org/pdf/1301.7094) | The unordered factor can have a bi-asymptotic pair. In period doubling `δ²(0)=0100` and `δ²(1)=0101`, a literal common-padding pair survives. Its matrix modulo two is not nilpotent. |

Proceed with the original-word statement. In the monoid algebra over
`𝔽₂` send a letter `a` to `1 + X_a`. The substitution on this expansion
replaces each `X_a` by a polynomial with no constant or linear term. It
therefore doubles the minimum degree of every difference. Common padding
preserves the first nonzero degree, because both padding factors have
constant term one. The expansion is injective by the inverse shift of
generators. A periodic difference supported on a bounded interval in the
original tiling gives precisely the two common-padding equations. A
one-sided finite difference starting at a common origin vertex works with
empty padding on the other side. The transfer of a finite defect from the
unordered factor to the original words is a separate question.

## Companion family beyond determinant two

The [determinant-two family](c4-even-companion-family-2026-11-19.md) uses
equal prefix counts at level three and the repository's checked exclusion
from left strong coincidence for every distinct letter pair. Test the words
`1/2/(1 0^m 2^r 1)` for positive `m < r`. The third-level comparison has two
copies of the long image on one track and a leading `2^m` on the other.
The new cut moves exactly those `m` copies of tile `2` into the long run.

[Sirvent–Solomyak (2002), §3](https://doi.org/10.4153/CMB-2002-062-3)
surveys the balanced-pair method and the additional hypotheses for a spectral
conclusion. The cited two-symbol result has a different alphabet. Here the
endpoint is the all-pair word witness, with the strict-system consequence
from the existing repository theorem. The Barge and Barge–Diamond sources
above place the even-parameter examples in the complete-square residue.
At `r = m` the designated upper position is the terminal `1` of its long
image, so the same `2` match requires `m < r`. Proceed with that guard.

# Physical overlap mass and terminal SCCs

Proceed with an exact replay on the twelve sources at PR #497 head
`49bc7e1af11b6ab04f84b79f8737500b6de3748b`. Issue #461 already gives the
conditional reduction and an 18-source calibration for a different incidence.
The experiment here is to derive the mass from literal physical endpoints,
check the effect of the track swap on multiplicities, and test the remaining
source SCCs of the inverse graph for mass loss.

- [Akiyama and Lee, §4, equation (4.2)](https://arxiv.org/pdf/1003.2898)
  uses multiplicities in forward overlap substitution. Here the forward
  physical rows are reconstructed from the inverse-prefix graph. The
  self-affine tiling and Meyer hypotheses of their spectral criterion are
  outside this certificate.
- [Minervino and Thuswaldner, Lemmas 3.1 and 3.3](https://arxiv.org/pdf/1402.2002)
  supplies non-unit Haar scaling and rational independence of the Perron
  lengths. Use the compact scaling from #497 and check the physical
  length normalization for the pinned incidence.
- [Tam and Schneider, Theorem 2.1](https://people.math.wisc.edu/hans/paper_archive/scanned_papers/hs106.pdf)
  describes the classical nonnegative eigencone. The terminal restriction
  here additionally needs a strictly positive transpose mass budget.
  Without it, a critical block can have incoming edges in the inverse
  graph. With it, an isolated conservative diagonal block can still be
  critical.

Track-swap fixed points and repeated literal edges are explicit controls.
An omitted occurrence could create spurious loss, so the inverse closure
must be authenticated before interpreting any positive deficit. This is
a source-specific replay, with no change to general PSC or C4 claims.

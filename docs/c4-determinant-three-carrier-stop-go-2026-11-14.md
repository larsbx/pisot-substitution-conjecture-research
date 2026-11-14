# Source review for the determinant-three forward carrier

The bilateral seam theorem excludes finite strict components for
`(1,0 1^k 2,0001)` with `k>=3`. This does not furnish a bound on
irreducible factors. The next question for [issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461)
is whether the actual `01/10` carrier is finite at every such parameter.

| Source | Transfer and boundary |
| --- | --- |
| [Sirvent–Solomyak, §5](https://doi.org/10.4153/CMB-2002-062-3) | Literal half-coincidences and termination govern the meaning of the bounds. A finite strict-system exclusion alone cannot replace bounded gaps. |
| [Barge–Štimac–Williams, Corollary 2](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf) | The one-swap criterion requires the complete finite irreducible-factor set and eventual coincidence of every member. A row with a diagonal and noncoincident children must still keep all children. |
| [Akiyama–Gähler–Lee, Proposition 2.2](https://dmtcs.episciences.org/2089/pdf) | The degree-three trace-at-most-two result does not cover any of these parameters. |
| [Barge, the β-substitution theorem](https://arxiv.org/abs/1505.04408) | Matching a polynomial is insufficient to identify a word substitution with a β-substitution. Here the polynomial is (X^3-kX^2-2X-3), distinct from the determinant-two family. |

The prior [determinant-two carrier](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/6bf0b9704501eb763cbb4323c3fd1f939d6f11c8/docs/c4-parameter-family-carrier-2026-11-14.md)
has exact symbolic rows for the other tail. The useful approach here is
to test revised word templates and their literal occurrence rows, with
a separate exact check where the affine alignment changes. Bounded search
may suggest a parameterization, but is insufficient to prove it.

**Decision.** Proceed with a symbolic closure test over one unbounded
parameter for the fixed determinant-three tail. Ordered rows and both
tracks' word identities must hold at every integer parameter, with no
cap in the proof. Verify the finite boundary independently. Treat a later
spectral statement via the published one-swap criterion as a separate
application. No general convergence of the balanced-pair algorithm is
assumed.

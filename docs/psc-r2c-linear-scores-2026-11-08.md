# R2C rational linear score classification on two ordered graphs

## Work shown

### Assumptions and hypotheses

Use the two complete ordered packets from the seed `(01,10)`, for Tribonacci `01,02,0` and the reducible control `1,012,1`. The score family is the rational linear functional `q` of the literal parent-prefix Parikh difference. The proposed orientation rule multiplies that score by the raw child's sign. The residual vector is `(sign − 1) (Parikh(top prefix) − Parikh(bottom prefix))`.

### Targeted literature stop/go

Proceed with the exact finite score family. Livshits's [cohomology of topological Markov chains](https://m.mathnet.ru/php/archive.phtml?jrnid=im&option_lang=eng&paperid=2373&wshow=paper) gives the standard cohomological setting. The finite calculation below uses only cancellation of vertex differences on an explicit cycle. [Sirvent–Solomyak, §§3–5](https://doi.org/10.4153/CMB-2002-062-3) ties coincidence tests to a prefix-seeded balanced pair algorithm, and [Martensen, §3](https://arxiv.org/abs/math/0309194) treats a different generalized balance for reducible substitutions. The latter hypotheses cannot promote the reducible control to a strict PIP example. Neither result identifies the required B′ average with this score family. The proposed result is the exact family classification on these two packets.

### Derivation / reduction

Write `q = (q₀,q₁,q₂)`. Every Tribonacci residual vector is zero or `2e₂`. The closed walk at occurrence rows `[5,9,1]` has total `2e₂`, so a potential forces `q₂=0`. Every control residual is zero, `2e₀`, or `2e₂`. The closed walks at rows `[3,6]` and `[5,7]` force `q₀=q₂=0`. In both cases the stated equations annihilate every residual, so the zero potential suffices. These classifications do not require a general cycle-space computation.

### Evidence and replay

The occurrence caps remain 32 states, 128 edges and 32 inflated letters per track. The Mojo residual producer replays the full packet before using its parent indices. The exact-head workflow compares every ordered vector row with Lean, which independently reconstructs the packet from literal words and proves both rational iff statements. The independent Quint model computes residual vectors from its own source reconstruction and checks the cycle rows.

### Negative controls

The Tribonacci unit coefficient of letter 2 and both obstructed unit coefficients in the reducible graph have nonzero cycle sums. Exhausted or mutated source packets cannot be used to compute vectors. The letter-0 coefficient on Tribonacci and letter-1 coefficient on the reducible control are valid zero-residual calibrations.

### Non-claims / remaining gaps

A successful potential in this family only makes the adjustment residual vanish. Ordinary scores can still be nonzero on individual edges. The B′ source and density bridges, a score family beyond this child-sign rule, and PSC closure remain open.

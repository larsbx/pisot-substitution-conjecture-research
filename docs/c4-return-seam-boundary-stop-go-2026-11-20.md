# C4 return-word boundary calculation and literature decision

## Target

The [marked-count calculation](c4-homoclinic-winding-counts-2026-11-20.md)
requires a joint seam contribution modulo four in the even-determinant
rank-two residue. Track the actual original seam cycle through Barge's
proper return-word rewrite. Test whether the image is an integral fixed
vector, which original data survive, and how the stack projection reads
its winding from the positions of twin vertices.

## Sources and hypotheses

| Source | Consequence for this step |
| --- | --- |
| [Durand, *A characterization of substitutive sequences using return words*, Proposition 19](https://arxiv.org/pdf/0807.3322) | The return substitution is obtained by factoring an inflated return word at the marker. Its flattening intertwines with the original substitution. The two-sided marker here is a legal periodic cut. |
| [Barge, *Factors of Pisot tiling spaces*, Lemmas 13–14, Theorem 17 and §4](https://arxiv.org/pdf/1301.7094) | Proper rewriting and the letter morphism to stacks give one geometric subdivision per return-word type. The unordered tile support is the intersection of the two stack tile supports. Properness and twin disjointness at all inflation levels control which sheet owns a vertex. The construction applies in the standing even case. |
| [Barge–Diamond, *Cohomology of substitution tiling spaces*, Theorem 4](https://arxiv.org/pdf/math/0702669) | The eventual-range sequence accounts for the seam contribution to cohomology. It gives the rational dimension comparison once a common power fixes the graph. The calculation below constructs and reads the corresponding integer vectors directly. |
| [Berthé et al., *Return words in tree sets*, Corollary 13](https://orbi.uliege.be/bitstream/2268/192334/1/Berthe_DeFelice_Dolce_Leroy_Perrin_Reutenauer_Rindone_JM2014.pdf) | A free-basis conclusion requires the tree hypothesis. The legal seam cycle here already violates acyclicity of the empty word's extension graph, so it supplies no injectivity of the return-word flattening. |

The Thue–Morse square at the marker `0.0` is a concrete even-count
control. The original letter count loses the signed seam combination,
while return-word counts retain it. Its unordered period-doubling factor
exhibits the odd winding in dilation degree one.

## Decision

Proceed with the integral seam-to-return comparison and a finite
stack-vertex expression. The arithmetic nilpotence of the original
incidence addresses original letter counts. The present step must
identify separately the surviving return-word terms, including the
selected marker count. The final geometric exclusion needs an
additional restriction specific to the cubic case.

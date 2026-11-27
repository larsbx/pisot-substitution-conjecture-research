# Source decision for the C4 homoclinic winding proof

The [even-determinant reduction](c4-even-stack-residue-2026-11-19.md#the-grouped-square-forces-a-homoclinic-winding-on-the-base)
uses a continuous phase on a two-sheet cover. The two asymptotic tails of a
base pair are matched by different sheets. The target is to construct the
normalized lifts, prove that their base winding is an odd integer, and
compose this with the existing grouped seam cycle calculation.

| Source | Scope used |
| --- | --- |
| [Barge (2015), Example 16, Theorem 17 and Proposition 19](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | The stack construction at coincidence rank two supplies the setting of a two-sheet factor. Example 16 identifies a bi-asymptotic pair in period doubling. The odd-norm lower bound in Theorem 22 leaves even norm open. |
| [Barge–Kellendonk–Schmieding (2012), Lemma 4 and Theorem 5](https://arxiv.org/pdf/1204.1432) | The proof uses the discreteness of roots of unity in a related eigenfunction lifting argument. The saturation theorem concerns the maximal equicontinuous factor pullback. |
| [Andress–Robinson (2016), §3.2 and Theorem 3.1](https://bpb-us-e1.wpmucdn.com/blogs.gwu.edu/dist/2/115/files/2016/03/AndressRobinsonPub-15tlli8.pdf) | Bruschlinsky's theorem identifies degree-one Čech cohomology with circle maps modulo continuous real logarithms. Here the evaluation compares two orbit paths with matching tails. |

Proceed with the local winding calculation. Use the additive circle
`ℝ/ℤ` and the covering-space lifting theorem on `ℝ`. Normalize a global
lift by comparing it on a connected half-line with the local section at
zero. For a half-turn between the two sheets at time zero the two real
lifts differ by an integer plus `1/2`, so doubling makes their difference
odd. The same-sheet case gives an even winding. A two-sheet phase path
with odd winding is also a control against deriving a contradiction from
the covering conditions alone. The identification of the four seam images
in the actual stack quotient, the tail agreement there, and the cubic
obstruction remain separate mathematical inputs or obligations.

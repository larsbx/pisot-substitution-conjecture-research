# Source review for deciding the C4 marker test

The target is the existence of a nonempty balanced prefix of two
specified periodic right rays that violates the [original marker
law](c4-original-marker-parity-2026-11-20.md). Decide that property at
all levels for each fixed source. Also check whether three-letter
prefixes can supply a uniform witness in a family with unbounded
image lengths and even determinant.

| Source | Use in this step |
| --- | --- |
| [Canterini–Siegel, *Automate des préfixes-suffixes associé à une substitution primitive*, §2](https://www.numdam.org/item/JTNB_2001__13_2_353_0.pdf) | The prefix-suffix path names a literal position through ordered image occurrences. Use synchronous paths rooted at two specified letters. |
| [Sirvent–Solomyak, *Pure Discrete Spectrum for One-dimensional Substitution Systems of Pisot Type*, Lemma 5.5](https://doi.org/10.4153/CMB-2002-062-3) | A pair of geometric intervals with both endpoints aligned has equal Parikh counts when the Perron lengths are rationally independent. |
| [Akiyama–Lee, *Algorithm for determining pure pointedness of self-affine tilings*, Lemmas 3.8–3.9](https://arxiv.org/pdf/1003.2898) | Saturated finite graphs distinguish unreachable targets from a search stopped at a chosen depth. The target here is a marker violation at a common cut, so use the repository's prefix-Parikh graph. |
| [Barge, *Factors of Pisot tiling spaces and the coincidence rank conjecture*, Lemmas 13–15 and Theorem 17](https://arxiv.org/pdf/1301.7094) | The deck involution in the rank-two stack factor supplies the setting for the previous marker law. The finite test is conditional on that setting when used as an exclusion. |

Proceed. Reuse the [equal-Parikh automaton](../kernel/psc/coincidence_formula.mojo).
The new step is a marker register whose update needs only the last
letters and the next occurrence digits. Nilpotence modulo two allows
a letter-count correction using three successive phases. On balanced
prefixes those corrections cancel. A product with the existing
automaton should decide the prescribed test without a guessed
substitution depth. Check the register algebra in Lean and use
complementary Thue–Morse words as an all-length compatibility control.

For the family, prescribe the first four letters of two images and
hold the remaining Parikh counts to a rank-one integer perturbation
of a fixed nilpotent matrix. Check the periodic seams, even
nilpotence and irreducible Pisot property for every parameter.
Proceed with that class of word orderings. The hypotheses on the
prefixes are essential to the proposed witness. This step leaves
uniform reachability across arbitrary sources open.

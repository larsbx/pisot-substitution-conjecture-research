# Plus-Class-A upper entry: source and hypothesis check

**Decision.** Prove entry into the central slice by inspecting the literal
first, last and adjacent RUN occurrences. Use positive inflation of the
distance to the overlap boundary for termination. The result concerns the
specific upper family, with full integral displacements.

The historical [lower all-source proof](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/9f0138d213357b866e7ceef0dcbfab96a667526d/docs/class-a-plus-constant-entry-2026-11-14.md)
uses center counts on long inflated common intervals. Its lower root bracket
and density constants do not transfer as stated. The
[upper central theorem](class-a-plus-upper-central-recurrence-2026-11-15.md)
supplies the correct upper lengths and accepts exactly central integral y/y
packets. Neither source supplies an upper literal boundary case split.

- Akiyama and Lee, [*Algorithm for determining pure pointedness of self-affine tilings*](https://arxiv.org/abs/1003.2898),
  Section 4, use actual descendants of inflated overlaps and distinguish
  potential overlaps. Transfer the positive-interior descendant condition.
  No finite potential-overlap graph is needed for this argument.
- Minervino and Thuswaldner, [*The geometry of non-unit Pisot substitutions*](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf),
  Sections 2.2 and 4, use literal prefix/suffix decompositions and
  compatible marked walks. Transfer the original-prefix bookkeeping with
  forward incidence only. The result does not need inverse incidence.
- Barge, [*Pure discrete spectrum for a class of one-dimensional substitution tiling systems*](https://www.aimsciences.org/article/doi/10.3934/dcds.2016.36.1159),
  uses injectivity on initial letters and constancy on final letters.
  The displayed upper words have coinciding initial x marks and two
  different final letters, so those hypotheses do not apply directly.

A direct RUN/RUN selector needs its finite gap range proved. For example,
the strict source y/c with offset (0,1,0) has no central one-edge child.
A scalar near-boundary argument must also lift each selected occurrence to
the literal full-vector update and preserve the original track orientation
when a local comparison swaps tracks.

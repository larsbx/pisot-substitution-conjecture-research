# Class-B step 2c: exact core and remaining finite gaps — stop/go

Proposed increment: reproduce the step-2b strict-core closure with the existing
exact Perron-field engine; fit proposed middle-regime rows from exact exports;
test those rows with the existing symbolic ray checker before attempting a
gap-uniform promotion. Extend the already reviewed finite-gap ray contract.

Primary sources rechecked on 2026-10-27:

- Barge–Štimac–Williams, [Pure discrete spectrum in substitution tiling spaces](https://arxiv.org/abs/1107.3598): geometric coincidence procedures for Pisot-family systems. A finite overlap computation is not by itself a universal family theorem.
- Berthé–Bourdon–Jolivet–Siegel, [A combinatorial approach to products of Pisot substitutions](https://arxiv.org/abs/1401.0704): finite combinatorial certificates for specified infinite substitution families. Its product families do not identify the present determinant-two family.
- Minervino–Thuswaldner, [The geometry of non-unit Pisot substitutions](https://www.numdam.org/articles/10.5802/aif.2884/): non-unit representation spaces have finite-prime factors. No transfer of a unimodular hypothesis or Euclidean-only realization is authorized here.

Decision: **proceed at the narrowed exact carrier/certificate scope** already
specified in the merged step-2b note. Retain its hypotheses and the separate
seed-graph/realized-overlap dictionary. No new PDS reduction is proposed.
The native engine remains canonical; Python independently decides rational
polynomial signs and reconstructs integral children. Deliberately deleted
carrier rows, invalid ranks, exhausted budgets and unstable parameter fits
must refuse. A finite fit cannot certify any unbounded parameter domain.

The first unresolved inequality or closure failure will be exported literally
if the regime certificate refuses. Historical packets remain unchanged.

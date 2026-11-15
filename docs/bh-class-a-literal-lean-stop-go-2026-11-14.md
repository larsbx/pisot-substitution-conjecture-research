# Minus-Class-A literal Lean interfaces: source and hypothesis gate

Date: November 14, 2026. Baseline: draft PR #579,
`110e7e9ef8243bc24adf80d6e8a375add586d850`, stacked on #578 and #577.

## Proposed increment and decision

**Proceed with a deductive specialization of the existing written proof.**
For the literal words `x -> x y^(n+d) x`, `c -> c y^n x`,
`y -> x y^(n-1) c`, retain `d >= 5` and `n >= d+1` explicitly.
Connect the cubic-root bracket, normalized lengths and positive-coefficient
recurrence to the existing constant-tail and original RUN descent proofs.
Formalize the literal density estimates and their finite count contradiction
as far as supported by actual word and occurrence definitions. Assemble
nested proper-prefix occurrences along composable paths, with the complete
three-coordinate identity and the repository's explicit sign convention.

The new code is Lean proof code, not a replacement executable mathematical
kernel. The canonical Mojo constructors and independent Python replay from
#579 retain their roles. No new sampled census is proposed as a source-cover
argument. All-source geometric entry, existence/identification of the Perron
root, and exclusion of half-unit ties stay explicit until discharged.

## Primary sources re-inspected before implementation

1. Kirschenhofer and Thuswaldner, *Shift Radix Systems — A Survey*, RIMS
   Kokyuroku Bessatsu B46 (2014),
   <https://www.kurims.kyoto-u.ac.jp/~kenkyubu/bessatsu/open/B46/pdf/B46_001.pdf>.
   The introduction distinguishes eventually periodic orbits from the
   finiteness property; the survey separately treats variants of the floor
   map. The literal nearest-integer sign convention must be specialized,
   not imported as an unstated shift-radix theorem.
2. Kirschenhofer, Petho, Surer and Thuswaldner, *Finite and periodic orbits
   of shift radix systems*, JTNB 22 (2010),
   <https://www.math.tugraz.at/~tichy/publications/finitev8.pdf>.
   Its contractive-orbit result concerns the stated floor map. This increment
   uses the already proved strict-nearest recurrence and supplies actual
   occurrence exits for nonzero constants; periodicity alone is not zero
   hitting.
3. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   AIF 64 (2014), 1373–1417,
   <https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf>.
   The prefix automaton retains marked prefix/letter/suffix occurrences.
   The nonunit representation framework supplies a boundary reminder, not
   an inverse-integrality hypothesis or a spectral conclusion for this
   determinant-minus-two literal family.
4. Akiyama and Lee, *Algorithm for determining pure pointedness of self-affine
   tilings*, <https://arxiv.org/abs/1003.2898>.
   Overlap coincidence has a tiling-system setting. A theorem about selected
   finite literal occurrences must retain its exact source scope and does
   not by itself discharge infinite-tiling realization or universal BH.

The append-only side-notes ledger and the pre-code gates of #577–#579 were
also read. No novelty is claimed for telescoping affine transport, finite
packing, or the distinction between periodicity and zero hitting. The
contribution sought is their checked literal specialization and connection.

## Controls and acceptance

Require explicit negative controls for invalid lower-chamber parameters,
an incomplete projected prefix identity, and attempted path composition at
different middle packets. Audit independent exact theorem types, including
missing-declaration, wrong-type and extra-premise controls; reject local
axioms and `sorryAx`. Bind all source/configuration bytes to each receipt.

Record local cached compilation, fresh source-isolated compilation and
exact-head hosted acceptance separately. The historical #579 Mathlib HTTP
403 occurred before the new theorem compiled and remains infrastructure
evidence unless a newer isolated result supersedes it. Preserve failed
attempts. Leave all governed BH/PSC and family source-coverage statuses
unchanged; independent review and merging remain with the user.

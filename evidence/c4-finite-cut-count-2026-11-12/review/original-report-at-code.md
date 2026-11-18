# Finite lower count for the original balanced cuts

This implements the finite step reviewed in the compact-neighborhood evidence
packet's `next-count-plan.md` and `next-count-interface-review.md`. Those
reviews record the source checks for the subsequent fixed-origin
cut-and-project count. This step uses finite balanced reduction, integer
Parikh vectors, and additive lengths.

For a complete reduction `red u v` of balanced words, the indices in
`Fin (red u v).length` pick the proper starts of successive factors. The
initial cut is included when a factor exists. Every factor has a nonempty
top, so ordinary prefix length strictly increases across starts. Equality
of integer Parikh vectors implies equality of ordinary prefix lengths.
This proves injectivity and identifies the cardinality with the number of
factor occurrences, including repeated factor labels.

The complete top and bottom tracks produce literal marks at each counted
start. Both prefixes are balanced by concatenation of the earlier balanced
factors. A uniform bound on the physical length of a top factor gives the
finite lower count by summing over the complete top track. Positive letter
weights place the physical coordinates in the original half-open strip.

For each named fixture and a supplied fixed strict carrier, take any
uniform physical factor bound on the carrier. Such a bound exists by
finiteness. Exact substitution scaling gives strip length
`beta ^ (12 * n) * physicalLength physicalRow T.1`. The capture theorem
from PR #558 applies to the images of these same counted vectors, with
one threshold for the carrier.

The finite set stays in integer Parikh space throughout. The analytic
upper lattice count, all-depth cylinder masses, chart covolume, and
regular outer-cover argument are open.

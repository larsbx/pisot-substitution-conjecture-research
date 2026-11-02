"""Complete literal newborn-boundary atlas for a supplied finite strict system.

This is a proof-support instrument, NOT a proof that strict PIP systems exist,
nor an inference from a finite packet SCC to strict child closure. It calls the
repository's strict DerivedSystem constructor and independently reconstructs
every ordered parent image and zero-return cut. Event addresses are physical,
on canonical parent orientation, before child normalization.

No float/eigenvalue/synthetic quotient and no promoted C4/PSC claim.
"""

from psc.bpa import (
    apply_substitution, coincidence_boundaries, prefix_endpoint_map,
    suffix_endpoint_map,
)
from psc.c4_cut_alignment import CutBirth, classify_irreducible_birth, _eventually_equal
from psc.derived_system import build_derived_system
from psc.words import Pair


struct StrictBirthEvent(Copyable, Movable):
    var parent_id: Int
    var right_ordinal: Int
    var physical_cut: Int
    var left_child_id: Int
    var right_child_id: Int
    var left_sign: Int
    var right_sign: Int
    var top_source: Int
    var bottom_source: Int
    var top_digit: Int
    var bottom_digit: Int
    var source_defect: List[Int]
    var local_correction: List[Int]
    var left_top_letter: Int
    var left_bottom_letter: Int
    var right_top_letter: Int
    var right_bottom_letter: Int

    def __init__(
        out self,
        parent_id: Int,
        right_ordinal: Int,
        physical_cut: Int,
        left_child_id: Int,
        right_child_id: Int,
        left_sign: Int,
        right_sign: Int,
        birth: CutBirth,
        left_top_letter: Int,
        left_bottom_letter: Int,
        right_top_letter: Int,
        right_bottom_letter: Int,
    ):
        self.parent_id = parent_id
        self.right_ordinal = right_ordinal
        self.physical_cut = physical_cut
        self.left_child_id = left_child_id
        self.right_child_id = right_child_id
        self.left_sign = left_sign
        self.right_sign = right_sign
        self.top_source = birth.top_source
        self.bottom_source = birth.bottom_source
        self.top_digit = birth.top_digit
        self.bottom_digit = birth.bottom_digit
        self.source_defect = birth.source_defect.copy()
        self.local_correction = birth.local_correction.copy()
        self.left_top_letter = left_top_letter
        self.left_bottom_letter = left_bottom_letter
        self.right_top_letter = right_top_letter
        self.right_bottom_letter = right_bottom_letter


def strict_birth_atlas(
    sigma: List[List[Int]],
    states: List[Pair],
    birth_cap: Int = 10000,
) raises -> List[StrictBirthEvent]:
    """All ordered interior born cuts of all fully validated strict parents.

    Reconstructs original words through canonical finite balanced-pair rules
    on EVERY parent, and refuses before a complete result if any cap is hit.
    The cap is an implementation budget, not part of the mathematical lemma.
    """
    if birth_cap <= 0 or len(states) == 0 or len(states) > 2000:
        raise Error("strict atlas input or resource cap invalid")
    var ds = build_derived_system(sigma, states)
    var right_map = prefix_endpoint_map(sigma)
    var left_map = suffix_endpoint_map(sigma)
    var result = List[StrictBirthEvent]()
    for parent_id in range(ds.size()):
        var parent = ds.states[parent_id].copy()
        var top = apply_substitution(sigma, parent.u)
        var bottom = apply_substitution(sigma, parent.v)
        var cuts = coincidence_boundaries(top, bottom)
        if len(cuts) != len(ds.images[parent_id]) + 1:
            raise Error("derived image misses an actual ordered factor")
        if len(ds.child_signs[parent_id]) != len(ds.images[parent_id]):
            raise Error("derived child sign count mismatch")
        for k in range(1, len(cuts) - 1):
            if len(result) >= birth_cap:
                raise Error("strict born-cut budget exhausted")
            var cut = cuts[k]
            if cut <= 0 or cut >= len(top):
                raise Error("strict born-cut lies outside parent interior")
            # Literal source address/correction and zero-return checks.
            var birth = classify_irreducible_birth(sigma, parent, cut)
            var left_top = top[cut - 1]
            var left_bottom = bottom[cut - 1]
            var right_top = top[cut]
            var right_bottom = bottom[cut]
            if _eventually_equal(left_map, left_top, left_bottom):
                raise Error("claimed strict system has synchronizing left newborn")
            if _eventually_equal(right_map, right_top, right_bottom):
                raise Error("claimed strict system has synchronizing right newborn")
            result.append(StrictBirthEvent(
                parent_id, k, cut,
                ds.images[parent_id][k - 1], ds.images[parent_id][k],
                ds.child_signs[parent_id][k - 1], ds.child_signs[parent_id][k],
                birth,
                left_top, left_bottom, right_top, right_bottom,
            ))
    return result^

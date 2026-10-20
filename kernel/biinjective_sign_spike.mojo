"""Exploratory bi-injective *non-Pisot-inclusive* short-word substitution scan.

Universe: every sigma over {0,1,2} with each image of length 1..3 and
injective first and last letter maps. This domain includes substitutions
with reducible incidence characteristic polynomials and non-Pisot spectra.
Primitive ones are screened with the upstream exact integer kernel.

Incomplete BPA graphs from either the state or state-length cap are NOT
counted as evidence that Branch B is absent. The question is whether
a Branch-B witness in the bi-injective world needs an arithmetic exclusion.

Replay:
  cd kernel
  pixi run mojo run -I . biinjective_sign_spike.mojo
"""

from finite_linear_algebra.integer_matrix import is_primitive
from finite_linear_algebra.mat3 import Mat3
from psc.bounded_bpa import BUDGET_LENGTH, BUDGET_STATES, build_bounded
from psc.bpa import recurrent_noncoincident_sccs, substitution_incidence
from psc.carrier import profile_component
from psc.corpus import image_words, substitution_of
from psc.endpoint_core import prefix_endpoint_map, suffix_endpoint_map
from psc.endpoint_sign_spike import (
    BRANCH_A, BRANCH_B, BRANCH_C, audit_closed_component, injective
)
from psc.symmetry import substitution_key
from substitution_dynamics.substitution import Substitution


comptime MAX_BPA_STATES = 160
comptime MAX_STATE_LENGTH = 80


def has_integer_root_of_monic_cubic(m: Mat3) -> Bool:
    """Degree three: rational root theorem, integral monic polynomial.

    A cubic over Q is reducible iff it has a rational root. Monicity
    forces every rational root to be integral. The small fixed image
    domain bounds the constant coefficient and the direct root scan.
    """
    var c = m.charpoly()  # c0+c1*x+c2*x^2+x^3
    var bound = abs(c[0])
    for root in range(-bound, bound + 1):
        if root * root * root + c[2] * root * root + c[1] * root + c[0] == 0:
            return True
    return False


def main() raises:
    var words = image_words()
    var domain = 0
    var primitive = 0
    var complete = 0
    var capped_states = 0
    var capped_lengths = 0
    var closed = 0
    var a_count = 0
    var b_count = 0
    var c_count = 0
    var b_reducible = 0
    var b_irreducible = 0
    var b_max_size = 0
    print(
        "BIINJECTIVE_SIGN_SPIKE_START max_image_length=3 state_cap=",
        MAX_BPA_STATES, " length_cap=", MAX_STATE_LENGTH,
    )
    for i in range(len(words)):
        for j in range(len(words)):
            for k in range(len(words)):
                var sigma = substitution_of(words, i, j, k)
                if not injective(prefix_endpoint_map(sigma)):
                    continue
                if not injective(suffix_endpoint_map(sigma)):
                    continue
                domain += 1
                var mat = Mat3(substitution_incidence(sigma))
                if not is_primitive(mat.e, 3):
                    continue
                primitive += 1
                var bounded = build_bounded(
                    Substitution.checked(sigma), MAX_BPA_STATES, MAX_STATE_LENGTH
                )
                if not bounded.complete():
                    if bounded.exhausted == BUDGET_STATES:
                        capped_states += 1
                    elif bounded.exhausted == BUDGET_LENGTH:
                        capped_lengths += 1
                    else:
                        raise Error("unknown bounded-BPA refusal cause")
                    continue
                complete += 1
                var graph = bounded.graph
                var comps = recurrent_noncoincident_sccs(graph)
                for ci in range(len(comps)):
                    if not profile_component(graph, comps[ci]).is_sink():
                        continue
                    closed += 1
                    var info = audit_closed_component(sigma, graph, comps[ci])
                    if info.branch == BRANCH_A:
                        a_count += 1
                    elif info.branch == BRANCH_C:
                        c_count += 1
                    elif info.branch == BRANCH_B:
                        b_count += 1
                        if info.states > b_max_size:
                            b_max_size = info.states
                        if has_integer_root_of_monic_cubic(mat):
                            b_reducible += 1
                        else:
                            b_irreducible += 1
                        print(
                            "BIINJECTIVE_BRANCH_B_WITNESS sigma=", substitution_key(sigma),
                            " image_indices=", i, j, k,
                            " SCC=", ci, " size=", info.states,
                            " occurrences=", info.occurrences,
                            " incidence_charpoly=", mat.charpoly(),
                            " charpoly_reducible=", has_integer_root_of_monic_cubic(mat),
                            " endpoint_diagonal=", info.has_endpoint_diagonal,
                        )
                    else:
                        raise Error("unclassified closed SCC")
    print(
        "BIINJECTIVE_SIGN_SPIKE_RESULT eligible=", domain,
        " primitive=", primitive, " complete=", complete,
        " capped_states=", capped_states, " capped_lengths=", capped_lengths,
        " closed=", closed, " A=", a_count, " B=", b_count, " C=", c_count,
        " B_reducible=", b_reducible, " B_irreducible=", b_irreducible,
        " B_max_size=", b_max_size,
    )
    if domain != 2958 or primitive != 2064:
        raise Error("enumerated finite-map domain/primitivity counts changed")
    if complete + capped_states + capped_lengths != primitive:
        raise Error("bounded exploration omitted a primitive specimen")
    if closed != a_count + b_count + c_count:
        raise Error("closed SCC branch tally mismatch")
    if b_count != b_reducible + b_irreducible:
        raise Error("characteristic-polynomial classification mismatch")
    print("BIINJECTIVE_SIGN_SPIKE_COMPLETE finite_evidence_only=1")

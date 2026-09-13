"""Rational-interval margin audit for the finite seed-patch overlap graph.

The audit is deliberately downstream of exact graph construction. It asks how
much of the retained geometry can be certified by one fixed rational enclosure
of the Perron root, while checking every ambiguous margin against the exact
Sturm--Tarski oracle.

A reported positive lower margin is global for the audited finite graph only
when *every* retained overlap margin is interval-certified. No finite margin is
promoted to a uniform theorem over all substitutions or all realizable balanced
pairs.
"""

from psc.overlap_seed_patch import build_seed_overlap_graph, build_seed_overlap_tables
from psc.perron_field3 import CubicElt, cubic_add_checked, cubic_sub_checked, sign_at_perron
from psc.perron_interval import cubic_perron_interval
from psc.rational_interval import CheckedRat


struct OverlapIntervalMarginAudit(ImplicitlyCopyable, Copyable, Movable):
    var state_count: Int
    var margin_count: Int
    var interval_certified_count: Int
    var fallback_count: Int
    var has_uniform_interval_lower_margin: Bool
    var minimum_interval_lower_margin: CheckedRat

    def __init__(
        out self,
        state_count: Int,
        margin_count: Int,
        interval_certified_count: Int,
        fallback_count: Int,
        has_uniform_interval_lower_margin: Bool,
        minimum_interval_lower_margin: CheckedRat,
    ):
        self.state_count = state_count
        self.margin_count = margin_count
        self.interval_certified_count = interval_certified_count
        self.fallback_count = fallback_count
        self.has_uniform_interval_lower_margin = has_uniform_interval_lower_margin
        self.minimum_interval_lower_margin = minimum_interval_lower_margin


def audit_seed_overlap_interval_margins(
    sigma: List[List[Int]],
    refinements: Int = 10,
    max_states: Int = 20000,
) raises -> OverlapIntervalMarginAudit:
    """Audit both strict positive margins of every retained overlap state.

    For state ``(i,j,t)``, the graph contract is exactly

    ```text
    t + ell_j > 0,
    ell_i - t > 0.
    ```

    Each expression is first evaluated by rational interval extension. If the
    interval does not prove positivity, the exact Perron sign oracle must still
    prove positivity or the graph/audit is internally inconsistent.
    """
    if refinements < 0:
        raise Error("overlap interval audit refinement count must be nonnegative")
    var graph = build_seed_overlap_graph(sigma, max_states)
    if graph.capped:
        raise Error("overlap interval margin audit is undefined for a capped graph")
    var tables = build_seed_overlap_tables(sigma)

    var interval_certified = 0
    var fallback = 0
    var has_minimum = False
    var minimum = CheckedRat(0, 1)

    for i in range(graph.size()):
        var state = graph.states[i]
        var right_margin = cubic_add_checked(
            state.shift, tables.lengths.at(state.bottom)
        )
        var left_margin = cubic_sub_checked(
            tables.lengths.at(state.top), state.shift
        )
        var margins: List[CubicElt] = [right_margin, left_margin]
        for j in range(2):
            var margin = margins[j]
            var box = cubic_perron_interval(tables.field, margin, refinements)
            var boxed_sign = box.strict_sign()
            if boxed_sign > 0:
                interval_certified += 1
                if not has_minimum or box.lo.compare(minimum) < 0:
                    minimum = box.lo
                    has_minimum = True
            elif boxed_sign < 0:
                raise Error("rational interval contradicts retained overlap positivity")
            else:
                var exact_sign = sign_at_perron(tables.field, margin)
                if exact_sign <= 0:
                    raise Error("retained overlap state failed exact positive-margin audit")
                fallback += 1

    var margin_count = 2 * graph.size()
    if interval_certified + fallback != margin_count:
        raise Error("overlap interval margin accounting failed")
    var uniform = fallback == 0 and has_minimum
    if uniform and minimum.sign() <= 0:
        raise Error("uniform rational interval lower margin is not positive")
    return OverlapIntervalMarginAudit(
        graph.size(),
        margin_count,
        interval_certified,
        fallback,
        uniform,
        minimum,
    )

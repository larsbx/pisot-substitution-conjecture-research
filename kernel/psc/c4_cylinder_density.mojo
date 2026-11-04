"""Bounded literal strict-cut densities for the finite-cylinder criterion.

The all-column condition is a finite combinatorial certificate: every parent
has a descendant carrying the requested unordered first-letter pair after
exactly t steps. Together with complete strict child closure it gives
delta >= 1/(beta**t * Lmax), in the stated physical-length normalization.

No supplied graph, empirical frequency, or unsupported Perron vector is a
density input. The named-chart entry point rebuilds all literal children and
authenticates its rational beta upper bound. The uniform entry point is a
separate combinatorial control; it does not authorize Pisot geometry.
"""

from finite_exact.rat_q import Q
from psc.derived_system import DerivedSystem, build_derived_system
from psc.exact import eval_int_poly_at_q, q_int, require_q
from psc.words import Pair, parikh


comptime DENSITY_STATE_CAP = 128
comptime DENSITY_WORD_CAP = 256
comptime DENSITY_IMAGE_CAP = 64
comptime DENSITY_INFLATED_CAP = 16384
comptime DENSITY_DEPTH_CAP = 32


def density_chart_name() -> String:
    return String("ell0=1;W=(x0-a*x1,x2-b*x1);haar=probability")


def _validate_words(sigma: List[List[Int]], states: List[Pair]) raises:
    # Check every index before reaching the alphabet-3 BPA routines, whose
    # malformed-input guard aborts rather than returning a rejected result.
    if len(sigma) != 3:
        raise Error("strict density requires a three-letter substitution")
    for letter in range(3):
        if len(sigma[letter]) == 0 or len(sigma[letter]) > DENSITY_IMAGE_CAP:
            raise Error("strict density image cap or erasing image")
        for position in range(len(sigma[letter])):
            if sigma[letter][position] < 0 or sigma[letter][position] >= 3:
                raise Error("strict density substitution letter outside 0..2")
    if len(states) == 0 or len(states) > DENSITY_STATE_CAP:
        raise Error("strict density state count cap")
    for state_id in range(len(states)):
        var length = len(states[state_id].u)
        if length == 0 or length != len(states[state_id].v) or length > DENSITY_WORD_CAP:
            raise Error("strict density word shape or length cap")
        var top_length = 0
        var bottom_length = 0
        for position in range(length):
            var top = states[state_id].u[position]
            var bottom = states[state_id].v[position]
            if top < 0 or top >= 3 or bottom < 0 or bottom >= 3:
                raise Error("strict density state letter outside 0..2")
            top_length += len(sigma[top])
            bottom_length += len(sigma[bottom])
        if top_length > DENSITY_INFLATED_CAP or bottom_length > DENSITY_INFLATED_CAP:
            raise Error("strict density inflated word cap")


def literal_strict_cut_system(
    sigma: List[List[Int]], states: List[Pair]
) raises -> DerivedSystem:
    """Recompute every child, including multiplicity and flipped orientation.

    The returned collection is balanced, irreducible as words, noncoincident,
    and closed under its full literal child factorization. We do not label it
    an SCC: graph strong connectivity is unnecessary for the all-column lemma.
    """
    _validate_words(sigma, states)
    return build_derived_system(sigma, states)


def all_column_target_cover(
    images: List[List[Int]], target: List[Bool], steps: Int
) raises -> Bool:
    """Boolean support of h*N**steps; a graph check, not a density premise.

    Exact common length matters. Cumulative reachability would incorrectly
    accept a singleton target on a period-two cycle.
    """
    if steps < 0 or steps > DENSITY_DEPTH_CAP:
        raise Error("strict density depth cap")
    var size = len(images)
    if size == 0 or size > DENSITY_STATE_CAP or len(target) != size:
        raise Error("strict density cover graph shape")
    for source in range(size):
        if len(images[source]) == 0 or len(images[source]) > DENSITY_INFLATED_CAP:
            raise Error("strict density cover child row cap")
        for occurrence in range(len(images[source])):
            var child = images[source][occurrence]
            if child < 0 or child >= size:
                raise Error("strict density cover child outside graph")
    var reached = target.copy()
    for _ in range(steps):
        var next = List[Bool]()
        for source in range(size):
            var found = False
            for occurrence in range(len(images[source])):
                if reached[images[source][occurrence]]:
                    found = True
                    break
            next.append(found)
        reached = next^
    for source in range(size):
        if not reached[source]:
            return False
    return True


def all_column_pair_cover(
    system: DerivedSystem, left: Int, right: Int, steps: Int
) raises:
    """Require the target pair in every source at exactly the stated depth."""
    if left < 0 or left >= right or right >= 3:
        raise Error("strict density unordered pair domain")
    if len(system.states) != len(system.images):
        raise Error("strict density system shape")
    var target = List[Bool]()
    for state_id in range(len(system.states)):
        if len(system.states[state_id].u) == 0 or len(system.states[state_id].v) == 0:
            raise Error("strict density target on empty word")
        var a = system.states[state_id].u[0]
        var b = system.states[state_id].v[0]
        target.append((a == left and b == right) or (a == right and b == left))
    if not all_column_target_cover(system.images, target, steps):
        raise Error("no common-depth target cover of every literal source")


def _inverse_growth_length(beta_hi: Q, steps: Int, length_hi: Q) raises -> Q:
    var denominator = require_q(length_hi, "strict density physical length")
    if not Q.zero().lt(denominator):
        raise Error("strict density physical length must be positive")
    for _ in range(steps):
        denominator = require_q(denominator.mul(beta_hi), "strict density denominator")
    return require_q(Q.one().div(denominator), "strict density reciprocal")


def uniform_strict_cut_density(
    sigma: List[List[Int]], states: List[Pair], left: Int, right: Int, steps: Int
) raises -> Q:
    """Exact ell=(1,1,1) control; does not supply a Pisot chart or covolume."""
    var system = literal_strict_cut_system(sigma, states)
    var expansion = len(sigma[0])
    if expansion < 2 or len(sigma[1]) != expansion or len(sigma[2]) != expansion:
        raise Error("uniform density requires common image length at least two")
    all_column_pair_cover(system, left, right, steps)
    var max_length = 0
    for state_id in range(system.size()):
        if system.block_lengths[state_id] > max_length:
            max_length = system.block_lengths[state_id]
    return _inverse_growth_length(q_int(expansion), steps, q_int(max_length))


def named_density_beta_upper(beta_hi: Q) raises -> Q:
    """Authenticate an upper bound for the unique root beta in (2,5/2).

    chi'=3*x*x-2*x-2 is positive for x>2, and chi(2)<0<chi(5/2).
    Thus a positive exact chi(beta_hi) in this interval is an upper bound.
    """
    var bound = require_q(beta_hi, "strict density beta upper")
    if not q_int(2).lt(bound) or not bound.le(Q(5, 2)):
        raise Error("strict density beta upper outside supported bracket")
    var value = eval_int_poly_at_q([-2, -2, -1, 1], bound)
    if not Q.zero().lt(value):
        raise Error("strict density beta upper is below the Perron root")
    return bound^


def named_density_substitution(sigma: List[List[Int]]) raises:
    """Bind the chart to the two literal productive non-unit controls."""
    if len(sigma) != 3:
        raise Error("unsupported density substitution")
    if sigma[0] != [1] or sigma[2] != [0, 0, 1]:
        raise Error("unsupported density substitution")
    if sigma[1] != [0, 2, 1] and sigma[1] != [0, 1, 2]:
        raise Error("unsupported density substitution")


def named_density_length_upper(states: List[Pair], beta_hi: Q) raises -> Q:
    """Physical maximum from actual words in ell=(1,beta,beta^2-beta-1).

    This is only a length calculation. It does not assert strictness or child
    closure, which the density entry point validates independently.
    """
    var upper = named_density_beta_upper(beta_hi)
    if len(states) == 0 or len(states) > DENSITY_STATE_CAP:
        raise Error("strict density length state count cap")
    # x^2-x-1 increases for x>2, so this rational is an upper for ell_2.
    var ell2_hi = require_q(upper.square().sub(upper).sub(Q.one()), "strict density ell2")
    var maximum = Q.zero()
    for state_id in range(len(states)):
        if len(states[state_id].u) == 0 or len(states[state_id].u) > DENSITY_WORD_CAP:
            raise Error("strict density length word cap")
        for position in range(len(states[state_id].u)):
            if states[state_id].u[position] < 0 or states[state_id].u[position] >= 3:
                raise Error("strict density length letter outside 0..2")
        var counts = parikh(states[state_id].u)
        var length = require_q(
            q_int(counts[0]).add(upper.mul(q_int(counts[1]))).add(ell2_hi.mul(q_int(counts[2]))),
            "strict density state physical length",
        )
        if maximum.lt(length):
            maximum = length.copy()
    return maximum^


def verify_named_chart_density(
    sigma: List[List[Int]], states: List[Pair], left: Int, right: Int,
    steps: Int, beta_hi: Q, proposed_lower: Q, normalization: String,
) raises -> Q:
    """Return the certified lower bound only after all word/chart premises.

    No genuine strict system is supplied for either supported control. Both
    have strong-coincidence witnesses. An arithmetic inequality alone must not
    be presented as an accepted instance of equation (11).
    """
    if normalization != density_chart_name():
        raise Error("incompatible strict density physical/Haar normalization")
    named_density_substitution(sigma)
    var upper = named_density_beta_upper(beta_hi)
    var claim = require_q(proposed_lower, "strict density proposed lower")
    # Every strict balanced block has at least two symbols, and ell_i>=1.
    if not Q.zero().lt(claim) or not claim.le(Q(1, 2)):
        raise Error("strict density claim outside possible physical range")
    var system = literal_strict_cut_system(sigma, states)
    all_column_pair_cover(system, left, right, steps)
    var length_hi = named_density_length_upper(system.states, upper)
    var certified = _inverse_growth_length(upper, steps, length_hi)
    if not claim.le(certified):
        raise Error("unsupported strict density magnitude")
    return certified^

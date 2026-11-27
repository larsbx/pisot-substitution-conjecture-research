"""Exact ternary legality and residue filters for two-sided hub phases."""

from psc.bpa import sigma3, substitution_incidence
from psc.c4_cut_alignment import _det3, _integral_column_lift, _prefix_counts


def legal_bigrams(sigma: List[List[Int]]) -> List[Bool]:
    """All bigrams of finite iterates of a single letter, indexed by 3*a+b."""
    var substitution = sigma3(sigma)
    var first = substitution.prefix_endpoint_map()
    var last = substitution.suffix_endpoint_map()
    var legal = List[Bool]()
    for _ in range(9):
        legal.append(False)
    for a in range(3):
        for i in range(len(sigma[a]) - 1):
            legal[3 * sigma[a][i] + sigma[a][i + 1]] = True

    var changed = True
    while changed:
        changed = False
        for a in range(3):
            for b in range(3):
                if legal[3 * a + b]:
                    var next = 3 * last[a] + first[b]
                    if not legal[next]:
                        legal[next] = True
                        changed = True
    return legal^


def _hub_pairs(endpoint: List[Int], hub: Int, top_has_hub: Bool, phase: Int) -> List[Int]:
    var out = List[Int]()
    for leaf in range(3):
        if leaf == hub:
            continue
        var a = hub if top_has_hub else leaf
        var b = leaf if top_has_hub else hub
        var pair = 3 * a + b
        var viable = True
        var expected_on_top = top_has_hub
        # At most six distinct ordered noncoincident pairs per hub side.
        for _ in range(13):
            var missing_hub = a != hub and b != hub
            var wrong_side = phase >= 0 and (a != hub if expected_on_top else b != hub)
            if a == b or missing_hub or wrong_side:
                viable = False
                break
            a = endpoint[a]
            b = endpoint[b]
            expected_on_top = expected_on_top != (phase == 1)
        if viable:
            out.append(pair)
    return out^


def phase_zero_legal_seams(sigma: List[List[Int]], left_hub: Int,
                           right_hub: Int, right_on_top: Bool) raises -> List[Int]:
    """Possible paired seams, indexed by 9*terminal+initial.

    Left hub is on top. An empty list rules out the proposed right
    track. Surviving entries only attest to compatible legal bigrams.
    """
    if left_hub < 0 or left_hub >= 3 or right_hub < 0 or right_hub >= 3:
        raise Error("seam hub lies outside 0..2")
    var substitution = sigma3(sigma)
    var initial = _hub_pairs(substitution.prefix_endpoint_map(), left_hub, True, 0)
    var terminal = _hub_pairs(substitution.suffix_endpoint_map(), right_hub, right_on_top, 0)
    return _legal_seams(terminal, initial, legal_bigrams(sigma))


def _legal_seams(
    terminal: List[Int], initial: List[Int], legal: List[Bool],
) -> List[Int]:
    var seams = List[Int]()
    for i in range(len(terminal)):
        for j in range(len(initial)):
            var top = 3 * (terminal[i] // 3) + initial[j] // 3
            var bottom = 3 * (terminal[i] % 3) + initial[j] % 3
            if legal[top] and legal[bottom]:
                seams.append(9 * terminal[i] + initial[j])
    return seams^

def _preceding_matches(sigma: List[List[Int]], legal: List[Bool],
                       image: Int, digit: Int, wanted: Int) -> Bool:
    if digit > 0:
        return sigma[image][digit - 1] == wanted
    for a in range(3):
        if legal[3 * a + image] and sigma[a][len(sigma[a]) - 1] == wanted:
            return True
    return False


def phase_zero_birth_seams(sigma: List[List[Int]], left_hub: Int,
                           right_hub: Int, right_on_top: Bool) raises -> List[Int]:
    """Local legal newborn overapproximation with exact integer residues."""
    return _birth_seams(sigma, left_hub, right_hub, right_on_top, 0)


def phase_one_birth_seams(sigma: List[List[Int]], left_hub: Int,
                          right_hub: Int, right_on_top: Bool) raises -> List[Int]:
    """Candidate newborns when both hubs flip at each actual child.

    Use child order with the left hub on top. The complementary coincidence
    witnesses are supplied by the caller's mathematical application.
    """
    return _birth_seams(sigma, left_hub, right_hub, right_on_top, 1)


def strict_birth_seams(sigma: List[List[Int]], left_hub: Int,
                       right_hub: Int, right_on_top: Bool) raises -> List[Int]:
    """Local candidates without a hub-phase restriction.

    Orient the seam so the right factor starts with the left hub on top.
    right_on_top then selects the terminal hub's track on the left factor.
    """
    return _birth_seams(sigma, left_hub, right_hub, right_on_top, -1)


def _birth_seams(
    sigma: List[List[Int]], left_hub: Int, right_hub: Int,
    right_on_top: Bool, phase: Int,
) raises -> List[Int]:
    if len(sigma) != 3:
        raise Error("newborn seam test requires ternary substitution")
    if left_hub < 0 or left_hub >= 3 or right_hub < 0 or right_hub >= 3:
        raise Error("seam hub lies outside 0..2")
    for a in range(3):
        if len(sigma[a]) == 0 or len(sigma[a]) > 64:
            raise Error("image outside checked seam arithmetic budget")
        for j in range(len(sigma[a])):
            if sigma[a][j] < 0 or sigma[a][j] >= 3:
                raise Error("newborn seam test has a letter outside 0..2")
    var substitution = sigma3(sigma)
    var f = substitution.prefix_endpoint_map()
    var g = substitution.suffix_endpoint_map()
    var legal = legal_bigrams(sigma)
    var allowed = _legal_seams(_hub_pairs(g, right_hub, right_on_top, phase),
                               _hub_pairs(f, left_hub, True, phase), legal)
    var m = substitution_incidence(sigma)
    var det = _det3(m)
    if det == 0:
        raise Error("newborn seam test requires nonsingular incidence")

    # Children in the output have their left hub on top. For phase one
    # the parent of such a newborn has its left hub on the bottom.
    var flip = phase == 1
    var first = _hub_pairs(f, left_hub, not flip, phase)
    var last = _hub_pairs(g, right_hub, right_on_top != flip, phase)
    if phase < 0:
        first.extend(_hub_pairs(f, left_hub, False, phase))
        last.extend(_hub_pairs(g, right_hub, not right_on_top, phase))
    var births = List[Int]()
    for index in range(len(allowed)):
        var seam = allowed[index]
        var top_left = seam // 27
        var bottom_left = (seam // 9) % 3
        var top_right = (seam % 9) // 3
        var bottom_right = seam % 3
        var possible = False
        for a in range(3):
            for r in range(len(sigma[a])):
                if sigma[a][r] != top_right or not _preceding_matches(sigma, legal, a, r, top_left):
                    continue
                var p = _prefix_counts(sigma[a], r)
                for b in range(3):
                    for s in range(len(sigma[b])):
                        if r == 0 and s == 0:
                            continue
                        if sigma[b][s] != bottom_right or not _preceding_matches(sigma, legal, b, s, bottom_left):
                            continue
                        var q = _prefix_counts(sigma[b], s)
                        var correction: List[Int] = [p[0] - q[0], p[1] - q[1], p[2] - q[2]]
                        if p == q and (3 * a + b) not in first:
                            continue
                        var same_tail = True
                        for k in range(3):
                            if correction[k] != m[3 * k + a] - m[3 * k + b]:
                                same_tail = False
                        if same_tail and (3 * a + b) not in last:
                            continue
                        if _integral_column_lift(m, det, correction):
                            possible = True
        if possible:
            births.append(seam)
    return births^


def phase_zero_reachable_seams(sigma: List[List[Int]], left_hub: Int,
                               right_hub: Int, right_on_top: Bool) raises -> List[Int]:
    """Forward endpoint closure of the necessary local newborn labels."""
    var reached = phase_zero_birth_seams(sigma, left_hub, right_hub, right_on_top)
    var substitution = sigma3(sigma)
    var first = substitution.prefix_endpoint_map()
    var last = substitution.suffix_endpoint_map()
    var head = 0
    while head < len(reached):
        var seam = reached[head]
        head += 1
        var terminal = 3 * last[seam // 27] + last[(seam // 9) % 3]
        var initial = 3 * first[(seam % 9) // 3] + first[seam % 3]
        var next = 9 * terminal + initial
        if next not in reached:
            reached.append(next)
    return reached^

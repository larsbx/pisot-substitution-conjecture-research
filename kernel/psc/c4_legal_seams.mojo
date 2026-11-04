"""Exact ternary letter-language test for two-sided phase-zero cuts."""

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


def _hub_pairs(endpoint: List[Int], hub: Int, top_has_hub: Bool) -> List[Int]:
    var out = List[Int]()
    for leaf in range(3):
        if leaf == hub:
            continue
        var a = hub if top_has_hub else leaf
        var b = leaf if top_has_hub else hub
        var pair = 3 * a + b
        var viable = True
        # At most six distinct ordered noncoincident pairs can occur.
        for _ in range(7):
            if a == b or (a != hub if top_has_hub else b != hub):
                viable = False
                break
            a = endpoint[a]
            b = endpoint[b]
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
    var initial = _hub_pairs(substitution.prefix_endpoint_map(), left_hub, True)
    var terminal = _hub_pairs(substitution.suffix_endpoint_map(), right_hub, right_on_top)
    var legal = legal_bigrams(sigma)
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
    for a in range(len(sigma)):
        if len(sigma[a]) > 64:
            raise Error("image outside checked seam arithmetic budget")
    var allowed = phase_zero_legal_seams(sigma, left_hub, right_hub, right_on_top)
    var m = substitution_incidence(sigma)
    var det = _det3(m)
    if det == 0:
        raise Error("newborn seam test requires nonsingular incidence")
    var substitution = sigma3(sigma)
    var first = _hub_pairs(substitution.prefix_endpoint_map(), left_hub, True)
    var last = _hub_pairs(substitution.suffix_endpoint_map(), right_hub, right_on_top)
    var legal = legal_bigrams(sigma)
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

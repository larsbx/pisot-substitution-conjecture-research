"""Exact ternary letter-language test for two-sided phase-zero cuts."""

from psc.bpa import sigma3


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

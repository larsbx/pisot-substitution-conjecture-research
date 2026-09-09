"""Exact seven-type classifier for endpoint maps on a three-letter alphabet.

Type ids match docs/c4-endpoint-core-program.md:
  0=A  1=B  2=C  3=D  4=E  5=F  6=G

This is a finite combinatorial classifier only.  It makes no Pisot claim.
"""


def prefix_endpoint_map(sigma: List[List[Int]]) -> List[Int]:
    var out = List[Int]()
    for a in range(3):
        out.append(sigma[a][0])
    return out^


def suffix_endpoint_map(sigma: List[List[Int]]) -> List[Int]:
    var out = List[Int]()
    for a in range(3):
        out.append(sigma[a][len(sigma[a]) - 1])
    return out^


def endpoint_type(h: List[Int]) -> Int:
    """Return the canonical functional-graph type id A..G as 0..6."""
    var fixed = 0
    for a in range(3):
        if h[a] == a:
            fixed += 1

    if fixed == 3:
        return 3  # D: three fixed points
    if fixed == 2:
        return 2  # C: two fixed points plus one leaf

    var has_two_cycle = False
    for a in range(3):
        for b in range(a + 1, 3):
            if h[a] == b and h[b] == a:
                has_two_cycle = True

    if fixed == 0:
        if has_two_cycle:
            return 5  # F: 2-cycle plus one leaf
        return 6      # G: 3-cycle

    # Exactly one fixed point remains.
    if has_two_cycle:
        return 4      # E: one fixed point plus a 2-cycle

    var seen: List[Bool] = [False, False, False]
    var image_size = 0
    for a in range(3):
        if not seen[h[a]]:
            seen[h[a]] = True
            image_size += 1
    if image_size == 1:
        return 0      # A: constant map
    return 1          # B: tail of length two into the fixed point


def endpoint_type_name(t: Int) -> String:
    if t == 0:
        return "A"
    if t == 1:
        return "B"
    if t == 2:
        return "C"
    if t == 3:
        return "D"
    if t == 4:
        return "E"
    if t == 5:
        return "F"
    return "G"

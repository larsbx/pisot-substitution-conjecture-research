"""Bounded exact typed coordinates and legal occurrence maps; no tail proof."""
from class_b_top_layer_profile import top_layer_member, in_open_top_layer


def prefix(plus: Bool, gap: Int, q: Int, parent: Int, index: Int) raises -> List[Int]:
    if gap < 1 or gap > 5 or q < 1 or q > 48 or parent < 0 or parent > 2:
        raise Error("outside bounded pilot domain")
    var t = top_layer_member(plus, gap - 1, q)
    if not in_open_top_layer(plus, t[0], q):
        raise Error("outside top layer")
    var m = t[0] if parent == 0 else (t[1] if parent == 1 else t[2])
    if index < 0 or index > m + 1:
        raise Error("illegal proper-prefix occurrence index")
    if index == 0:
        return [0, 0, 0]
    return [1 if parent == 0 else 0, 0 if parent == 0 else 1, index - 1]


def child_coordinates(plus: Bool, gap: Int, q: Int, s: Int, d: Int, k: Int,
                      top: Int, bottom: Int, i: Int, j: Int) raises -> List[Int]:
    """Returns [s',d',k'] for an actual legal indexed occurrence pair.
    Does not test real overlap or seed reachability."""
    if s < -20000 or s > 20000 or d < -20000 or d > 20000 or k < -20000 or k > 20000:
        raise Error("coordinate budget exhausted")
    var a = prefix(plus, gap, q, top, i)
    var b = prefix(plus, gap, q, bottom, j)
    var dx = b[0] - a[0]
    var dc = b[1] - a[1]
    var dy = b[2] - a[2]
    var eps = 1 if plus else -1
    return [(q + 4 + eps) * s - gap * k - eps * d + 3 * dx + dc + dy,
            -2 * s + dc - 3 * dx, s - k + dx]

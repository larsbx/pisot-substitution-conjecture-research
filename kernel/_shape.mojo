from odd_letter_family_certificate import cover_shape, NO_DELTA, Y, Z
def show(name: String, l1: List[Int], l2: List[Int], s: Int, d: Int, tail: Bool) raises:
    var c = cover_shape(l1, l2, s, d, 4, tail, 4)
    print(name, " s", s, " delta", d, "+" if tail else "", ": regions", c.regions, " certified", c.certified, " (line", c.line_certified, ")  cut", c.cut, " decided", c.decided, " OPEN", c.open, " max level", c.max_level, flush=True)
def main() raises:
    var zy = List[Int]([Z, Y])
    show("zy | yz", zy, List[Int]([Y, Z]), -1, -1, False)
    show("zy | yz", zy, List[Int]([Y, Z]), -1, -2, False)
    show("zy | yz", zy, List[Int]([Y, Z]), -1, -3, False)
    show("zy | yz", zy, List[Int]([Y, Z]), -1, -4, True)
    show("zy | zyz", zy, List[Int]([Z, Y, Z]), 1, 4, True)

"""Finite comparisons only: typed intervals for direction (1,3,-6)."""
from psc.class_a_gap_dataset import typed_intervals


def read_intervals(path: String) raises -> List[List[Int]]:
    var text: String
    with open(path, "r") as f:
        text = f.read()
    var lines = text.splitlines()
    if len(lines) < 2:
        raise Error("missing member")
    var h = lines[0].split(" ")
    if len(h) != 4 or String(h[0]) != "M":
        raise Error("invalid member header")
    if Int(h[1]) < 1 or Int(h[1]) > 48 or Int(h[2]) < 1 or Int(h[2]) > 20000 or Int(h[3]) < 0 or Int(h[3]) > 20000:
        raise Error("member outside explicit finite budget")
    var labels = List[List[Int]]()
    var deepest = 0
    for line in lines[1:]:
        var p = line.split(" ")
        if String(p[0]) == "R":
            continue  # Derived rows are never trusted by this reader.
        if len(p) != 7 or String(p[0]) != "V":
            raise Error("invalid vertex")
        var t = Int(p[1])
        var b = Int(p[2])
        var k = Int(p[3])
        var c = Int(p[4])
        var y = Int(p[5])
        var depth = Int(p[6])
        if k < -20000 or k > 20000 or c < -20000 or c > 20000 or y < -20000 or y > 20000:
            raise Error("offset coordinate budget exhausted")
        if t < 0 or t > 2 or b < 0 or b > 2 or depth < 0:
            raise Error("invalid vertex type/depth")
        if (k == 0 and c == 0 and y == 0) != (depth == 0):
            raise Error("invalid target depth")
        deepest = max(deepest, depth)
        labels.append([t, b, 3 * k + c + y, c - 3 * k, k])
    if len(labels) != Int(h[2]) or deepest != Int(h[3]):
        raise Error("summary mismatch")
    return typed_intervals(labels^)


def affine_equal(a: List[List[Int]], b: List[List[Int]], c: List[List[Int]], step: Int) -> Bool:
    """a,b consecutive l-values, c at a+step; equality of every interval.
    This is a finite identity check, never an infinite-ray certificate."""
    if step < 2 or step > 48 or len(a) != len(b) or len(a) != len(c):
        return False
    for i in range(len(a)):
        for j in range(4):
            if a[i][j] != b[i][j] or a[i][j] != c[i][j]:
                return False
        for j in range(4, 6):
            if c[i][j] != a[i][j] + step * (b[i][j] - a[i][j]):
                return False
    return True


def tail_partition_ok(a: List[List[Int]], b: List[List[Int]]) -> Bool:
    """Only interval nonemptiness/disjointness for all integer l>=base.
    Does not establish graph equality or closure on the infinite tail."""
    if len(a) == 0 or len(a) != len(b):
        return False
    for i in range(len(a)):
        for j in range(4):
            if a[i][j] != b[i][j]:
                return False
        if a[i][5] < a[i][4] or b[i][5] - b[i][4] < a[i][5] - a[i][4]:
            return False
        if i > 0:
            var same = True
            for j in range(4):
                if a[i - 1][j] != a[i][j]:
                    same = False
            if same:
                var gap_a = a[i][4] - a[i - 1][5]
                var gap_b = b[i][4] - b[i - 1][5]
                if gap_a < 2 or gap_b < gap_a:
                    return False
    return True

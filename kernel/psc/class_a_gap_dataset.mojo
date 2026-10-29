"""Resumable exact label datasets for the class-A lines `(n+d, n, n+eps)`.

A *member record* is the complete canonical swap-seed graph of one member,
built under the 20,000-state cap. A capped graph or a vertex without a finite
offset-zero descendant raises. The record stores the label set losslessly as
its maximal typed k-intervals `(top, bottom, s, y, k_lo, k_hi)` (a label is
`(top, bottom, k, c, y)` with `s = k + c + y`), plus the vertex count and the
largest first-hit depth. Edges are not stored. Enumerating them costs about
80 times the graph itself, and a row fit does not read them.

A dataset file holds one line `(d, eps)`. It starts with a header, then
appends one block per member:

    # class-A gap labels v1 d=D eps=E
    M n vertices max_depth rows
    R top bottom s y k_lo k_hi        (rows times)

`extend_dataset` computes the members that are not yet in the file on
`parallel_fold` workers. It folds their blocks in increasing `n` and appends
each batch with a single write. The file is therefore byte-identical at any
worker count, and an interrupted run resumes where it stopped. `load_dataset`
refuses a truncated or malformed file instead of guessing. The records are
finite observations; nothing here is uniform in `n` or `d`.
"""
from std.collections import Dict
from std.os.path import exists
from parallel_fold.map_fold import parallel_map_fold
from psc.class_a_line import ALine
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables, first_left_aligned_depths,
)
from psc.vertex_coincidence import length_matrix, offset_vector

comptime STATE_CAP = 20000


def header(d: Int, eps: Int) -> String:
    return "# class-A gap labels v1 d=" + String(d) + " eps=" + String(eps) + "\n"


def _less(a: List[Int], b: List[Int]) -> Bool:
    for i in range(len(a)):
        if a[i] != b[i]:
            return a[i] < b[i]
    return False


def typed_intervals(var labels: List[List[Int]]) raises -> List[List[Int]]:
    """Maximal typed k-intervals of `[top, bottom, s, y, k]` labels, in lexicographic order."""
    # Insertion sort keeps this dependency-free; a member has a few hundred labels.
    for i in range(1, len(labels)):
        var x = labels[i].copy()
        var j = i
        while j > 0 and _less(x, labels[j - 1]):
            labels[j] = labels[j - 1].copy()
            j -= 1
        labels[j] = x^
    var out = List[List[Int]]()
    for x in labels:
        var last = len(out) - 1
        if last >= 0 and out[last][0] == x[0] and out[last][1] == x[1] and out[last][2] == x[2] and out[last][3] == x[3]:
            if out[last][5] == x[4]:
                raise Error("duplicate typed label")
            if out[last][5] + 1 == x[4]:
                out[last][5] = x[4]
                continue
        out.append([x[0], x[1], x[2], x[3], x[4], x[4]])
    return out^


def member_block(d: Int, eps: Int, n: Int) raises -> String:
    """The dataset block of member `n`; raises on a capped or non-hitting graph."""
    return substitution_block(ALine(d, eps, n % d).member(n), n)


def substitution_block(sigma: List[List[Int]], n: Int) raises -> String:
    """The dataset block of one substitution, recorded under parameter `n`;
    raises on a non-PIP input, a capped graph or a non-hitting vertex."""
    var tables = build_seed_overlap_tables_screened(sigma)
    var g = build_seed_overlap_graph_from_tables(tables, STATE_CAP)
    if g.capped:
        raise Error("STATE_BUDGET_EXHAUSTED: no label record")
    var depth = 0
    for x in first_left_aligned_depths(g):
        if x < 0:
            raise Error("complete graph has a vertex without an offset-zero descendant")
        depth = max(depth, x)
    var lm = length_matrix(tables)
    var labels = List[List[Int]]()
    for v in g.states:
        var w = offset_vector(lm, v.shift)
        labels.append([v.top, v.bottom, w[0] + w[1] + w[2], w[2], w[0]])
    var rows = typed_intervals(labels^)
    var out = "M " + String(n) + " " + String(g.size()) + " " + String(depth) + " " + String(len(rows)) + "\n"
    for r in rows:
        out += "R " + String(r[0]) + " " + String(r[1]) + " " + String(r[2]) + " " + String(r[3]) + " " + String(r[4]) + " " + String(r[5]) + "\n"
    return out^


struct Blocks(Copyable, Movable):
    """Concatenated member blocks; `failed` is the least failing position, or -1."""
    var text: String
    var failed: Int

    def __init__(out self):
        self.text = String()
        self.failed = -1


def _join(a: Blocks, b: Blocks) -> Blocks:
    var out = Blocks()
    out.text = a.text + b.text
    out.failed = a.failed if a.failed >= 0 else b.failed
    return out^


struct MemberRecord(Copyable, Movable):
    var n: Int
    var vertices: Int
    var depth: Int
    var rows: List[List[Int]]

    def __init__(out self, n: Int, vertices: Int, depth: Int):
        self.n = n
        self.vertices = vertices
        self.depth = depth
        self.rows = List[List[Int]]()


def load_dataset(path: String, d: Int, eps: Int) raises -> List[MemberRecord]:
    """Every complete member block, in file order; refuses a foreign header,
    a truncated block, a malformed line, a repeated member, or a row count
    that disagrees with the vertex count."""
    var out = List[MemberRecord]()
    if not exists(path):
        return out^
    var text: String
    with open(path, "r") as f:
        text = f.read()
    var lines = text.splitlines()
    if len(lines) == 0 or String(lines[0]) + "\n" != header(d, eps):
        raise Error("dataset header does not match d=" + String(d) + " eps=" + String(eps) + ": " + path)
    var seen = Dict[Int, Int]()
    var i = 1
    while i < len(lines):
        var m = lines[i].split(" ")
        if len(m) != 5 or String(m[0]) != "M":
            raise Error("malformed member line " + String(i + 1) + " in " + path)
        var rec = MemberRecord(Int(m[1]), Int(m[2]), Int(m[3]))
        var count = Int(m[4])
        if rec.n in seen:
            raise Error("repeated member n=" + String(rec.n) + " in " + path)
        seen[rec.n] = 1
        if i + count > len(lines) - 1:
            raise Error("truncated member block n=" + String(rec.n) + " in " + path)
        var size = 0
        for j in range(i + 1, i + 1 + count):
            var r = lines[j].split(" ")
            if len(r) != 7 or String(r[0]) != "R":
                raise Error("malformed row line " + String(j + 1) + " in " + path)
            var row = List[Int]()
            for t in range(1, 7):
                row.append(Int(r[t]))
            size += row[5] - row[4] + 1
            rec.rows.append(row^)
        if size != rec.vertices:
            raise Error("row lengths disagree with the vertex count at n=" + String(rec.n))
        out.append(rec^)
        i += 1 + count
    return out^


def members(d: Int, eps: Int, l_min: Int, l_max: Int) -> List[Int]:
    """Every `n = d l + r` with `l_min <= l <= l_max` in the line's domain, increasing."""
    var out = List[Int]()
    for n in range(d * l_min, d * (l_max + 1)):
        try:
            ALine(d, eps, n % d).check_domain(n)
            out.append(n)
        except:
            pass
    return out^


def extend_dataset(path: String, d: Int, eps: Int, wanted: List[Int], workers: Int, batch: Int) raises -> Int:
    """Append the blocks of every wanted member not yet recorded; returns how many were added."""
    if batch < 1:
        raise Error("batch size must be at least 1")
    ALine(d, eps, 0).check()
    var done = Dict[Int, Int]()
    for rec in load_dataset(path, d, eps):
        done[rec.n] = 1
    if not exists(path):
        with open(path, "w") as f:
            f.write(header(d, eps))
    var pending = List[Int]()
    for n in wanted:
        if n not in done:
            pending.append(n)
    var start = 0
    while start < len(pending):
        var chunk = List[Int]()
        for i in range(start, min(start + batch, len(pending))):
            chunk.append(pending[i])

        def one(i: Int) {chunk, d, eps} -> Blocks:
            var out = Blocks()
            try:
                out.text = member_block(d, eps, chunk[i])
            except:
                out.failed = i
            return out^

        var folded = parallel_map_fold(one, _join, Blocks(), len(chunk), workers)
        if folded.failed >= 0:
            # Replay the failure sequentially so the original error surfaces;
            # completed members of earlier batches stay recorded.
            _ = member_block(d, eps, chunk[folded.failed])
            raise Error("member worker failure did not replay")
        with open(path, "a") as f:
            f.write(folded.text)
        print("D_GAP_PROGRESS d=" + String(d), "eps=" + String(eps), "recorded", len(done) + start + len(chunk),
              "of", len(done) + len(pending), "last_n", chunk[len(chunk) - 1])
        start += len(chunk)
    return len(pending)

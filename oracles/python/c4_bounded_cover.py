"""Independent integer oracle for bounded literal inverse-history inventories.

Canonical implementation: kernel/psc/c4_bounded_cover.mojo.  Unlike that
adjugate-based implementation, this oracle rescans word prefixes and solves
each candidate by Cramer's rule with a permutation-definition determinant.
No native implementation, historical graph, floating arithmetic, or supplied
summary is used to generate the expected inventory.  Geometry is conditional;
the finite compact-group controls expose missing hypotheses explicitly.
"""

from collections import Counter
from dataclasses import dataclass
from itertools import permutations, product, zip_longest
from pathlib import Path
import argparse
import hashlib
import json
import subprocess


SCHEMA = "c4-bounded-cover-v1"
ROOT = Path(__file__).resolve().parents[2]
LIMITS = (6, 27, 64, 4096, 20000, 200000, 100000)
SOURCES = (
    "kernel/psc/c4_bounded_cover.mojo",
    "kernel/c4_bounded_cover.mojo",
    "kernel/tests/test_c4_bounded_cover.mojo",
    "oracles/python/c4_bounded_cover.py",
    "tests/test_c4_bounded_cover_oracle.py",
    "proof/PscVerif/PscVerif/OccurrenceCover.lean",
    "kernel/pixi.toml", "kernel/pixi.lock",
)


class InvalidCertificate(ValueError):
    """Incomplete or altered finite evidence cannot authorize a conclusion."""


def require(condition, message):
    # These guards, including packet authentication, survive python -O.
    if not condition:
        raise InvalidCertificate(message)


def integer(x):
    return type(x) is int


def determinant(matrix):
    """Leibniz definition, independently of the native cofactor routine."""
    require(len(matrix) == 3 and all(len(row) == 3 for row in matrix), "matrix shape")
    require(all(integer(x) for row in matrix for x in row), "integer matrix")
    total = 0
    for perm in permutations(range(3)):
        inversions = sum(perm[i] > perm[j] for i in range(3) for j in range(i + 1, 3))
        term = (-1) ** inversions
        for row in range(3):
            term *= matrix[row][perm[row]]
        total += term
    return total


def mv(matrix, vector):
    return tuple(sum(a * b for a, b in zip(row, vector)) for row in matrix)


def mm(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(3))
                       for j in range(3)) for i in range(3))


IDENTITY = ((1, 0, 0), (0, 1, 0), (0, 0, 1))


def incidence(words):
    return tuple(tuple(word.count(c) for word in words) for c in range(3))


def inverse_integer(matrix, rhs):
    require(len(rhs) == 3 and all(integer(x) for x in rhs), "integer inverse rhs")
    det = determinant(matrix)
    require(det != 0, "singular incidence: finite inverse enumeration unavailable")
    numerators = []
    for column in range(3):
        replaced = tuple(tuple(rhs[i] if j == column else matrix[i][j]
                               for j in range(3)) for i in range(3))
        numerators.append(determinant(replaced))
    if any(n % det for n in numerators):
        return None
    answer = tuple(n // det for n in numerators)
    require(mv(matrix, answer) == tuple(rhs), "inverse fails original equation")
    return answer


def digits(words):
    # Rescan the complete prefix at each position; native code accumulates it.
    return tuple((c, a, i, *(word[:i].count(k) for k in range(3)))
                 for a, word in enumerate(words) for i, c in enumerate(word))


def fixture(index):
    roots = ((0, 1, 0, 0, 0), (1, 0, 0, 0, 0))
    if index in (0, 1):
        words = ((0, 0), (1, 1), (2, 2))
        if index == 1:
            roots = ((0, 0, 0, 0, 0),)
        return words, roots, roots, 3
    if index == 2:
        return ((0, 1), (1,), (2,)), roots, roots, 2
    if index == 3:
        source = ((1, 1), (2, 1, 0), (1, 0))
        words = tuple(tuple(c for a in word for c in source[a]) for word in source)
        return words, roots, roots, 2
    raise InvalidCertificate("unknown fixture")


@dataclass(frozen=True)
class Inventory:
    words: tuple
    roots: tuple
    domain: tuple
    depth: int
    matrix: tuple
    digits: tuple
    nodes: tuple
    candidates: tuple

    def summary(self):
        leaves = tuple(n for n in self.nodes if n[2] == self.depth)
        endpoint_counts = Counter(n[5:10] for n in leaves)
        return (len(self.nodes), len(self.candidates),
                sum(c[3] == 0 for c in self.candidates),
                sum(n[16] == 0 for n in self.nodes), len(leaves),
                sum(n[17] for n in leaves),
                sum(count - 1 for count in endpoint_counts.values()),
                len({n[5:10] for n in self.nodes}))


def construct(words, roots, domain, depth, *, state_cap=4096,
              history_cap=20000, candidate_cap=200000, coordinate_bound=64,
              word_cap=100000):
    """All integral paths through the declared depth, including domain exits."""
    require(integer(depth) and 0 <= depth <= LIMITS[0], "depth budget exhausted")
    require(len(words) == 3, "three literal images required")
    require(all(1 <= len(w) <= LIMITS[1] and all(integer(c) and 0 <= c < 3 for c in w)
                for w in words), "literal image domain")
    bounds = ((state_cap, LIMITS[3]), (history_cap, LIMITS[4]),
              (candidate_cap, LIMITS[5]), (coordinate_bound, LIMITS[2]),
              (word_cap, LIMITS[6]))
    require(all(integer(n) and 1 <= n <= cap for n, cap in bounds), "invalid resource budget")
    require(roots and len(set(roots)) == len(roots), "empty or duplicate roots")
    require(len(set(domain)) == len(domain), "duplicate domain states")
    require(len(domain) <= state_cap, "state budget exhausted")
    for packet in roots + domain:
        require(len(packet) == 5 and all(integer(x) for x in packet), "integer packet")
        require(all(0 <= x < 3 for x in packet[:2]), "packet letters")
        require(all(abs(x) <= coordinate_bound for x in packet[2:]), "coordinate budget exhausted")
    matrix = incidence(words)
    require(determinant(matrix) != 0, "singular incidence: finite inverse enumeration unavailable")
    # Canonical word-budget semantics cover every source image, even letters
    # absent from these root histories. Refuse before constructing a huge word.
    for a in range(3):
        inflated_word(words, a, depth, word_cap)
    inventory = digits(words)
    powers = [IDENTITY]
    for _ in range(depth):
        powers.append(mm(powers[-1], matrix))
    nodes, candidates, states = [], [], set()
    for root, packet in enumerate(roots):
        inside = int(packet in domain)
        nodes.append((root, -1, 0, -1, -1, *packet, 0, 0, 0, 0, 0, 0, inside, inside))
        states.add(packet)
    require(len(nodes) <= history_cap, "history budget exhausted")
    require(len(states) <= state_cap, "state budget exhausted")
    cursor = 0
    while cursor < len(nodes):
        node = nodes[cursor]
        root, _, level = node[:3]
        packet = node[5:10]
        if level < depth:
            for ti, top in enumerate(inventory):
                if top[0] != packet[0]:
                    continue
                for bi, bottom in enumerate(inventory):
                    if bottom[0] != packet[1]:
                        continue
                    require(len(candidates) < candidate_cap, "candidate budget exhausted")
                    rhs = tuple(packet[2+k] + bottom[3+k] - top[3+k] for k in range(3))
                    residual = inverse_integer(matrix, rhs)
                    if residual is None:
                        candidates.append((cursor, ti, bi, 0, -1))
                        continue
                    require(all(abs(x) <= coordinate_bound for x in residual),
                            "coordinate budget exhausted")
                    target = (top[1], bottom[1], *residual)
                    inside = int(target in domain)
                    t_increment = mv(powers[level], top[3:])
                    b_increment = mv(powers[level], bottom[3:])
                    t_address = tuple(node[10+k] + t_increment[k] for k in range(3))
                    b_address = tuple(node[13+k] + b_increment[k] for k in range(3))
                    require(len(nodes) < history_cap, "history budget exhausted")
                    states.add(target)
                    require(len(states) <= state_cap, "state budget exhausted")
                    target_id = len(nodes)
                    nodes.append((root, cursor, level+1, ti, bi, *target,
                                  *t_address, *b_address, inside, node[17] * inside))
                    candidates.append((cursor, ti, bi, 1 if inside else 2, target_id))
        cursor += 1
    value = Inventory(tuple(words), tuple(roots), tuple(domain), depth, matrix,
                      inventory, tuple(nodes), tuple(candidates))
    check_addresses(value)
    return value


def inflated_word(words, letter, depth, word_cap=100000):
    word = (letter,)
    for _ in range(depth):
        require(sum(len(words[a]) for a in word) <= word_cap, "iterated word budget exhausted")
        word = tuple(c for a in word for c in words[a])
    return word


def path(value, index):
    result = []
    while True:
        require(integer(index) and 0 <= index < len(value.nodes), "history node index")
        n = value.nodes[index]
        require(len(n) == 18 and all(integer(x) for x in n), "integer history record")
        if n[1] == -1:
            require(n[2] == 0 and n[3:5] == (-1, -1), "invalid root history")
            break
        require(0 <= n[1] < index, "history predecessor must be strictly earlier")
        require(value.nodes[n[1]][2] + 1 == n[2], "history depth mismatch")
        result.append((n[3], n[4]))
        index = n[1]
    return tuple(reversed(result))


def check_addresses(value):
    """Check composed vectors against literal expanded words, not a recurrence."""
    seen = set()
    for i, n in enumerate(value.nodes):
        identity = (n[0], path(value, i))
        require(0 <= n[0] < len(value.roots), "history root index")
        require(identity not in seen, "duplicate literal history")
        seen.add(identity)
        root = value.roots[n[0]]
        for track, start in ((0, 10), (1, 13)):
            word = inflated_word(value.words, n[5+track], n[2])
            address = n[start:start+3]
            position = sum(address)
            require(0 <= position < len(word), "literal address outside iterate")
            require(word[position] == root[track], "literal address selects wrong letter")
            require(tuple(word[:position].count(c) for c in range(3)) == address,
                    "composed prefix differs from literal iterate")
        power = IDENTITY
        for _ in range(n[2]):
            power = mm(power, value.matrix)
        image = mv(power, n[7:10])
        require(tuple(image[k] + n[10+k] - n[13+k] for k in range(3)) == root[2:],
                "powered address equation")


def reference(index):
    return construct(*fixture(index))


def core_lines(index, value):
    yield "fixture " + " ".join(map(str, (index, value.depth, determinant(value.matrix))))
    for a, word in enumerate(value.words):
        yield "image " + " ".join(map(str, (index, a, len(word), *word)))
    for label, packets in (("root", value.roots), ("domain", value.domain)):
        for r, packet in enumerate(packets):
            yield label + " " + " ".join(map(str, (index, r, *packet)))
    for i, digit in enumerate(value.digits):
        yield "digit " + " ".join(map(str, (index, i, *digit)))
    for i, node in enumerate(value.nodes):
        yield "node " + " ".join(map(str, (index, i, *node)))
    for candidate in value.candidates:
        yield "candidate " + " ".join(map(str, (index, *candidate)))
    yield "summary " + " ".join(map(str, (index, *value.summary())))


def geometric_controls():
    """Finite compact groups and exact integer sets; never interval-as-Haar."""
    g = frozenset(range(3))
    star = lambda z: sum(z) % 3
    a = lambda x: (2*x) % 3
    words, _, _, _ = fixture(0)
    matrix = incidence(words)
    require({a(x) for x in g} == g, "finite action not injective")
    require(all(a(star(z)) == star(mv(matrix, z)) for z in product(range(3), repeat=3)),
            "finite action does not commute")
    all_digits = digits(words)
    for c in range(3):
        tile_union = {((a(x) + star(d[3:])) % 3)
                      for d in all_digits if d[0] == c for x in g}
        require(tile_union == g, "finite tile equation")
    # p=(0,1,e2): every paired cylinder is all G, but every inverse rhs
    # has an odd third coordinate. The full integral inverse union is empty.
    packet = (0, 1, 0, 0, 1)
    pairs = [(p, q) for p in all_digits if p[0] == packet[0]
             for q in all_digits if q[0] == packet[1]]
    admitted = 0
    for p, q in pairs:
        rhs = tuple(packet[2+k]+q[3+k]-p[3+k] for k in range(3))
        admitted += inverse_integer(matrix, rhs) is not None
        first = {(a(x)+star(p[3:])) % 3 for x in g}
        second = {(a(x)+star(tuple(packet[2+k]+q[3+k] for k in range(3)))) % 3 for x in g}
        require(first & second == g, "paired compact control not full")
    require(admitted == 0, "unexpected integral incoming occurrence")
    # Identity substitution: range reflection is immediate, yet overlap is
    # full G for every integral translation, regardless of physical strip.
    require(inverse_integer(IDENTITY, (2, 0, 0)) == (2, 0, 0), "identity reflection")
    physical_mass = max(0, min(1, 1-2) - max(0, -2))
    compact_overlap = g & frozenset((x+2) % 3 for x in g)
    require(physical_mass == 0 and compact_overlap == g, "physical/compact separation")
    false_box = frozenset((0,))
    box_overlap = false_box & frozenset((x+1) % 3 for x in false_box)
    require(not box_overlap and g & frozenset((x+1) % 3 for x in g) == g,
            "undersized enclosure control")
    # Closed integer enclosures touching at their endpoints intersect.
    left, right = frozenset((0, 1)), frozenset((1, 2))
    require(left & right == {1}, "boundary contact must be retained")
    # Actual redundancy: s=01/1/2, A=id, star=0, K=G.  Incidence is
    # unimodular, so reflection holds. Both incoming literal pieces are G.
    triangular = ((0, 1), (1,), (2,))
    p = (0, 1, 0, 0, 0)
    redundant = construct(triangular, (p,), (p,), 1)
    require(len(redundant.nodes) == 3 and redundant.summary()[5] == 1,
            "actual redundant occurrence inventory")
    require({n[5:10] for n in redundant.nodes[1:]}
            == {p, (0, 0, 1, -1, 0)}, "actual redundant ancestor identities")
    require(abs(determinant(incidence(triangular))) == 1,
            "redundancy control requires integral range reflection")
    # Internal completeness without cover: a three-cycle, identity internal
    # action, star=sum mod3 and full tiles. Represent root and its swap, but
    # the unique literal incoming ancestor lies outside this finite domain.
    cyclic = ((1,), (2,), (0,))
    swapped = (1, 0, 0, 0, 0)
    incomplete = construct(cyclic, (p,), (p, swapped), 1)
    require(incomplete.summary()[4:6] == (1, 0), "internal-completeness control")
    require(incomplete.nodes[1][5:10] == (2, 0, 0, 0, 0), "cyclic incoming ancestor")
    require(determinant(incidence(cyclic)) == 1, "cyclic incidence range")
    require(all(star(mv(incidence(cyclic), z)) == star(z)
                for z in product(range(3), repeat=3)), "cyclic commutation")
    # Mandatory literal inverse-closed, forward-leaking domain. Physical
    # mass here is explicitly a calibration, never a compact measure.
    leak = reference(0)
    full_mass = retained_mass = positive_exits = 0
    for root in leak.roots:
        for ti in range(2):
            for bi in range(2):
                top_prefix = tuple(ti * int(k == root[0]) for k in range(3))
                bottom_prefix = tuple(bi * int(k == root[1]) for k in range(3))
                delta = tuple(top_prefix[k] - bottom_prefix[k] for k in range(3))
                child = (root[0], root[1], *delta)
                displacement = sum(delta)
                mass = max(0, min(1, 1-displacement) - max(0, -displacement))
                full_mass += mass
                retained_mass += mass if child in leak.domain else 0
                positive_exits += int(mass > 0 and child not in leak.domain)
    require((full_mass, retained_mass, positive_exits) == (4, 2, 2), "forward leak")
    # A genuinely omitted point cannot be recovered from an internal graph.
    pieces2 = (frozenset((0,)), frozenset((1,)))
    require(pieces2[0] | pieces2[1] != pieces2[0], "missing piece control")
    return {"missing_reflection": (3, 0, 4),
            "physical_not_compact": (physical_mass, len(compact_overlap)),
            "false_enclosure": (len(box_overlap), len(g)),
            "boundary_contact": (1,), "redundant_occurrence": (2, 1),
            "missing_piece": (2, 1), "internally_complete_not_cover": (3, 1, 0),
            "forward_leak": (full_mass, retained_mass, positive_exits)}


def validate_native(text):
    """Authenticate the entire ordered packet, including every repeated path."""
    require(isinstance(text, str) and text.endswith("\n"), "packet must end with newline")
    lines = text.splitlines()
    require(lines and lines[0] == "schema " + SCHEMA, "schema mismatch")
    require(len(lines) > 1 and lines[1] == "limits " + " ".join(map(str, LIMITS)), "budget mismatch")
    expected = ["schema " + SCHEMA, "limits " + " ".join(map(str, LIMITS))]
    summaries = []
    for i in range(4):
        value = reference(i)
        expected.extend(core_lines(i, value))
        summaries.append(value.summary())
    # Both mathematical controls and textual control receipts are checked.
    controls = geometric_controls()
    core_count = len(expected)
    require(lines[:core_count] == expected, next(
        (f"inventory differs at line {i+1}: expected {e!r}, got {a!r}"
         for i, (e, a) in enumerate(zip_longest(expected, lines[:core_count])) if e != a),
        "inventory length mismatch"))
    totals = (4, sum(s[0] for s in summaries), sum(s[1] for s in summaries), sum(s[4] for s in summaries))
    require(lines[-1] == "total " + " ".join(map(str, totals)), "total mismatch")
    # No unknown, duplicated, or silently ignored records are admitted.
    seen = set()
    for line in lines[core_count:-1]:
        parts = line.split()
        require(len(parts) >= 3 and parts[0] == "control", "unexpected packet record")
        name = parts[1]
        require(name in controls and name not in seen, "unknown or duplicate control")
        require(line == "control " + name + " " + " ".join(map(str, controls[name])),
                "control mismatch: " + name)
        seen.add(name)
    require(seen == set(controls), "missing finite control")
    return {"schema": SCHEMA, "scope": "bounded literal inventories; conditional geometry",
            "fixtures": [{"fixture": i, "summary": list(s)} for i, s in enumerate(summaries)],
            "controls": {k: list(v) for k, v in controls.items()},
            "native_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "bytes": len(text.encode()), "lines": len(lines),
            "no_governed_claim_promoted": True}


def receipt_source():
    return {"git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
            "git_tree": subprocess.check_output(["git", "rev-parse", "HEAD^{tree}"], cwd=ROOT, text=True).strip(),
            "worktree_dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).strip()),
            "sources": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in SOURCES}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = validate_native(args.native.read_text())
    result.update(receipt_source())
    rendered = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()

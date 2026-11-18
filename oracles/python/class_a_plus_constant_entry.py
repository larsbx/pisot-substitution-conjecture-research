"""Independent literal-word replay for the plus-Class-A constant chamber.

Canonical executable constructors are Mojo. This oracle reuses the unchanged
Fraction/Perron arithmetic and actual-prefix checker, with a new validated
literal family binding. Its finite samples do not supply the all-source or
all-parameter quantifiers of the accompanying written proof.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import re
import runpy

HERE = Path(__file__).resolve().parent
BASE = runpy.run_path(str(HERE / "class_a_central_entry.py"))
ParentGeometry = BASE["Geometry"]
add, scale = BASE["add"], BASE["scale"]
central = BASE["central"]
literal_child, reverse = BASE["literal_child"], BASE["reverse"]
original_prefix_certificate = BASE["original_prefix_certificate"]
P_VALUES, Q_VALUES = BASE["P_VALUES"], BASE["Q_VALUES"]
MEMBERS = tuple(dict.fromkeys((n, d) for d in (5, 7, 11) for n in
    (max(6, d-4), d-1, d, d+1, d+4, 2*d-2, 2*d-1, 4*d, 12*d, 24*d)
    if n >= 6 and d <= n+4))
SMALL_MEMBERS = tuple((n, n+4) for n in range(1, 6))


def parameters(n, d):
    if type(n) is not int or type(d) is not int or n < 6 or not 5 <= d <= n+4:
        raise ValueError("outside n>=6,5<=d<=n+4 plus-Class-A constant chamber")
    return n, d


def _literal_parameters(n, d):
    if type(n) is not int or type(d) is not int or n < 1 or not 5 <= d <= n+4:
        raise ValueError("outside the declared plus literal-word domain")


class LiteralGeometry(ParentGeometry):
    """Exact plus words; no negative parameters passed to a minus binder."""
    def __init__(self, n, d):
        _literal_parameters(n, d)
        self.n, self.d, self.eps = n, d, 1
        self.words = ((0,) + (2,)*(n+d) + (0,),
                      (1,) + (2,)*n + (0,),
                      (0,) + (2,)*(n+1) + (1,))
        self.chi = (-2, n-d+5, -(n+4))
        self.lo, self.hi = Fraction(n+3), Fraction(n+4)
        if not self.polynomial(self.lo) < 0 < self.polynomial(self.hi):
            raise ValueError("literal plus cubic does not bracket its Perron root")
        self.lengths = ((1, d-2, 1), (1, -2, 1), (0, -1, 1))
        self.prefixes = []
        for word in self.words:
            counts, prefixes = [0, 0, 0], []
            for letter in word:
                prefixes.append(tuple(counts))
                counts[letter] += 1
            self.prefixes.append(tuple(prefixes))
        self.cache = {}
        bind_geometry(self)


class Geometry(LiteralGeometry):
    def __init__(self, n, d):
        parameters(n, d)
        super().__init__(n, d)


class SmallGeometry(LiteralGeometry):
    def __init__(self, n, d):
        if (n, d) not in SMALL_MEMBERS:
            raise ValueError("outside the five declared small seam members")
        super().__init__(n, d)


def bind_geometry(g):
    _literal_parameters(g.n, g.d)
    n, d = g.n, g.d
    expected_words = ((0,) + (2,)*(n+d) + (0,), (1,) + (2,)*n + (0,),
                      (0,) + (2,)*(n+1) + (1,))
    if (g.eps != 1 or g.words != expected_words or
        g.chi != (-2, n-d+5, -(n+4)) or
        g.lengths != ((1, d-2, 1), (1, -2, 1), (0, -1, 1))):
        raise ValueError("foreign plus literal word, field or length binding")
    for a, word in enumerate(g.words):
        counts, prefixes = [0, 0, 0], []
        for letter in word:
            prefixes.append(tuple(counts)); counts[letter] += 1
        if g.prefixes[a] != tuple(prefixes):
            raise ValueError("foreign original prefix cache")
        length = tuple(sum(g.lengths[b][q] for b in word) for q in range(3))
        if length != g.times_beta(g.lengths[a]) or g.sign(g.lengths[a]) <= 0:
            raise ValueError("literal image and positive Perron lengths disagree")


def original_prefix_certificate(g, source, path, typed=False):
    bind_geometry(g)
    return BASE["original_prefix_certificate"](g, source, path, typed)


def cycle_addresses(n, d, height, flip=False):
    parameters(n, d)
    if type(height) is not int or height < 1 or 2*d*height > n+2:
        raise ValueError("constant height outside its exact central interval")
    addresses = []
    for H in range(height, 0, -1):
        gap = d*(H-1)+2
        addresses.extend(((d*H+2, 1), (1, n+4-d*H),
                          (1+max(gap, 0), 1+max(-gap, 0))))
    return [(j, i) for i, j in addresses] if flip else addresses


def nearest_run(g, source):
    """Exhaust all legal RUN gaps; independently count the selected prefixes.

    The canonical selector uses an exact binary search. This oracle scans
    the whole integer gap interval using cached literal-prefix geometry,
    then rebuilds the chosen incidence and prefix counts from actual words.
    """
    parameters(g.n, g.d)
    bind_geometry(g)
    if (len(source) != 5 or any(type(value) is not int for value in source)
            or not central(g, source)):
        raise ValueError("nearest RUN requires a central y/y source")
    choices = []
    for gap in range(-g.n, g.n+1):
        i, j = 1+max(gap, 0), 1+max(-gap, 0)
        child = g.child(source, i, j)
        if central(g, child):
            choices.append((i, j, child))
    if len(choices) != 1:
        raise ValueError("nearest actual RUN child must exist uniquely")
    i, j, child = choices[0]
    if literal_child(g, source, i, j) != child:
        raise ValueError("selected original RUN prefix counts disagree")
    return choices[0]


def cycle_escape(g, height, flip=False):
    source = (2, 2, height, -height, 0)
    if flip:
        source = reverse(source)
    if not central(g, source):
        raise ValueError("constant source is not central")
    return BASE["replay"](g, source, cycle_addresses(g.n, g.d, height, flip))


def central_escape(g, source, step_cap=10000):
    parameters(g.n, g.d)
    bind_geometry(g)
    if (len(source) != 5 or any(type(value) is not int for value in source)
            or not central(g, source) or step_cap < 0):
        raise ValueError("outside central constructor domain")
    result, seen, w = [], set(), source
    while w[2:] != (0, 0, 0):
        if w in seen:
            raise AssertionError("nearest RUN reached an unclassified nonconstant cycle")
        seen.add(w)
        p, q, r = w[2:]
        if p and q == -p and r == 0:
            tail = cycle_escape(g, abs(p), p < 0)
            if len(result)+len(tail) > step_cap:
                raise ValueError("central step cap exhausted; no verdict")
            return result + tail
        if len(result) >= step_cap:
            raise ValueError("central step cap exhausted; no verdict")
        edge = nearest_run(g, w)
        result.append(edge)
        w = edge[2]
    return result


def entry_escape(g, source, state_cap=10000, pair_cap=20000000,
                 step_cap=10000, typed=False):
    """Independent literal Cartesian BFS; caps refuse any conclusion."""
    parameters(g.n, g.d)
    bind_geometry(g)
    if (state_cap < 1 or pair_cap < 1 or step_cap < 0
            or len(source) != 5 or any(type(v) is not int for v in source)
            or source[0] not in range(3) or source[1] not in range(3)
            or not g.interior(source)):
        raise ValueError("outside entry constructor domain")
    states, parent, addresses = [source], [-1], [None]
    ids, queue, scanned = {source: 0}, deque([0]), 0
    found = None

    def terminal(w):
        return w[2:] == (0, 0, 0) and (not typed or w[0] == w[1])

    while queue:
        index = queue.popleft()
        w = states[index]
        if terminal(w) or central(g, w):
            found = index
            break
        scanned += len(g.words[w[0]])*len(g.words[w[1]])
        if scanned > pair_cap:
            raise ValueError("literal-pair cap exhausted; no verdict")
        for i, j, child in g.edges(w):
            if child in ids:
                continue
            if len(states) >= state_cap:
                raise ValueError("entry state cap exhausted; no verdict")
            ids[child] = len(states)
            queue.append(len(states))
            states.append(child)
            parent.append(index)
            addresses.append((i, j))
    if found is None:
        raise AssertionError("finite actual closure missed the proved central target")
    selected, cursor = [], found
    while parent[cursor] != -1:
        selected.append((*addresses[cursor], states[cursor]))
        cursor = parent[cursor]
    selected.reverse()
    if len(selected) > step_cap:
        raise ValueError("entry path cap exhausted; no verdict")
    if not terminal(states[found]):
        selected += central_escape(g, states[found], step_cap-len(selected))
    return selected


def one_level_density(g):
    """Nine actual block inequalities, packing bounds and a strict gap."""
    parameters(g.n, g.d)
    bind_geometry(g)
    K = 2 if g.sign(add(g.lengths[0], scale(g.lengths[2], -2))) < 0 else 3
    if (g.sign(add(g.lengths[0], scale(g.lengths[2], -K))) >= 0 or
        g.sign(add(g.lengths[1], scale(g.lengths[2], -1))) >= 0):
        raise ValueError("tile packing bound failed")
    rows = []
    for a, word in enumerate(g.words):
        counts = Counter(word)
        margins = (
            add(scale(g.lengths[1], counts[2]), scale(g.lengths[a], -g.n)),
            add(scale(g.lengths[a], 4), scale(g.lengths[1], -K*counts[0])),
            add(g.lengths[a], scale(g.lengths[1], -counts[1])),
        )
        if any(g.sign(m) < 0 for m in margins):
            raise ValueError("literal weighted density inequality failed")
        rows.append(dict(parent=a, counts=[counts[i] for i in range(3)],
                         scaled_margin_polynomials=[list(m) for m in margins]))
    gap = add(scale(g.lengths[2], 9*(g.n-5)), scale(g.times_beta(g.lengths[1]), -1))
    if g.sign(gap) <= 0:
        raise ValueError("literal density gap is not greater than one ninth")
    return dict(rows=rows, packing_constant=K, strict_gap_polynomial=list(gap),
                inequalities=12)


def central_sources(g):
    # The same explicit search interval is safe for 1<Lx<3 and 0<Lc<1:
    # |Lx-2|<1 and |Lc-1|<1/(n+3). No minus parameters are passed.
    return BASE["central_sources"](g)


def swap_sources(g):
    """Reconstruct actual ab/ba intersections; plus c/y middle is y/y."""
    return runpy.run_path(str(HERE / "class_a_x_productivity.py"))["swap_sources"](g)


def entry_sources(n, d):
    g = Geometry(n, d)
    nine, _ = swap_sources(g)
    sources = [w for source in nine for w in (source, reverse(source))]
    sources.append((0, 0, -1, -5, 6))
    if len(sources) != 19 or not all(g.interior(w) for w in sources):
        raise ValueError("the literal plus entry fixture set is not strict/distinct")
    return sources


def expected_native_keys(geometries):
    expected = set()
    for n, d in MEMBERS:
        g = geometries[(n, d)]
        expected.update(("PLUS_CENTRAL_PATH", n, d, *w) for w in central_sources(g))
        for H in range(1, min(12,(n+2)//(2*d))+1):
            source = (2, 2, H, -H, 0)
            expected.update(("PLUS_CONSTANT_PATH", n, d, *w)
                            for w in (source, reverse(source)))
        expected.update(("PLUS_ENTRY_PATH", n, d, *w) for w in entry_sources(n, d))
        expected.update(("PLUS_TYPED_ENTRY_PATH", n, d, a, b, 0, 0, 0)
                        for a in range(3) for b in range(3) if a != b)
    return expected


def check_native_log(path):
    """Require every expected source, every literal edge and exact receipts."""
    geometries, seen, certificates = {}, set(), []
    summaries, contracts = {}, set()
    for line in Path(path).read_text().splitlines():
        if line.startswith(("PLUS_CENTRAL_PATH ", "PLUS_CONSTANT_PATH ",
                            "PLUS_ENTRY_PATH ", "PLUS_TYPED_ENTRY_PATH ")):
            tag, *fields = line.split()
            values = list(map(int, fields))
            if len(values) < 8:
                raise ValueError("short native path header")
            n, d, a, b, p, q, r, length, *tail = values
            if length < 0 or len(tail) != 7*length:
                raise ValueError("malformed native ordered-occurrence transcript")
            key = (tag, n, d, a, b, p, q, r)
            if key in seen:
                raise ValueError("duplicate native source row")
            seen.add(key)
            if (n, d) not in geometries:
                geometries[(n, d)] = Geometry(n, d)
            g = geometries[(n, d)]
            source = (a, b, p, q, r)
            if tag == "PLUS_CENTRAL_PATH":
                expected = central_escape(g, source)
            elif tag == "PLUS_CONSTANT_PATH":
                if source != (2, 2, p, -p, 0) or not p:
                    raise ValueError("native constant source has the wrong full offset")
                expected = cycle_escape(g, abs(p), p < 0)
            else:
                expected = entry_escape(g, source, typed=tag == "PLUS_TYPED_ENTRY_PATH")
            native = [(tail[i], tail[i+1], tuple(tail[i+2:i+7]))
                      for i in range(0, len(tail), 7)]
            if native != expected:
                raise ValueError("native/oracle original path mismatch")
            certificate = original_prefix_certificate(
                g, source, native, typed=tag == "PLUS_TYPED_ENTRY_PATH")
            certificates.append(dict(kind=tag, n=n, d=d, source=list(source), **certificate))
        elif line.startswith("CLASS_A_PLUS_") and "_PASS " in line:
            tag, fields_text = line.split(" ", 1)
            if tag in summaries:
                raise ValueError("duplicate native completion receipt")
            if not re.fullmatch(r"\w+=\s*\d+(?:\s+\w+=\s*\d+)*", fields_text.strip()):
                raise ValueError("malformed native completion fields")
            fields = re.findall(r"(\w+)=\s*(\d+)", fields_text)
            if len({key for key, _ in fields}) != len(fields):
                raise ValueError("duplicate native completion field")
            summaries[tag] = {key: int(value) for key, value in fields}
        elif line.startswith("contract-receipt: "):
            if line in contracts:
                raise ValueError("duplicate native contract receipt")
            contracts.add(line)
        elif line.strip():
            raise ValueError("unexpected native path-log output")
    if set(geometries) != set(MEMBERS) or seen != expected_native_keys(geometries):
        raise ValueError("native path source set is incomplete or contains an extra source")
    _check_receipts(summaries, contracts, certificates)
    return dict(paths=len(certificates),
                native_log_sha256=sha256(Path(path).read_bytes()).hexdigest(),
                checked_edges=sum(c["depth"] for c in certificates),
                members=sorted(geometries), maximum_depth=max(c["depth"] for c in certificates),
                original_prefix_certificates=certificates,
                literal_one_level_density={f"{n},{d}": one_level_density(g)
                                           for (n, d), g in geometries.items()},
                native_receipts=summaries)


def _check_receipts(summaries, contracts, certificates):
    central_records = [c for c in certificates if c["kind"] in
                       ("PLUS_CENTRAL_PATH", "PLUS_CONSTANT_PATH")]
    entry_records = [c for c in certificates if c["kind"] == "PLUS_ENTRY_PATH"]
    typed_records = [c for c in certificates if c["kind"] == "PLUS_TYPED_ENTRY_PATH"]
    required = {
        "CLASS_A_PLUS_CONSTANT_ENTRY_PASS": dict(members=25, central_paths=875, cycle_paths=132,
            checked_edges=sum(c["depth"] for c in central_records),
            max_path=max(c["depth"] for c in central_records)),
        "CLASS_A_PLUS_ENTRY_SEARCH_PASS": dict(members=25, paths=475,
            checked_edges=sum(c["depth"] for c in entry_records),
            max_path=max(c["depth"] for c in entry_records), density_inequalities=300, refusals=8),
        "CLASS_A_PLUS_TYPED_ENTRY_PASS": dict(members=25, paths=150,
            checked_edges=sum(c["depth"] for c in typed_records),
            max_path=max(c["depth"] for c in typed_records)),
    }
    expected_contracts = {
        "contract-receipt: plus-Class-A n>=6,5<=d<=n+4 exact central nearest RUN selector and "
        "three-RUN constant-height descent; original ordinal and full Parikh replay, first "
        "integral-zero typed endpoint, checked pair/path bounds; word/field/prefix-cache mismatch, "
        "noncentral, altered-edge, cap and overflow refusals; finite fixtures do not supply "
        "the written all-strict-source density or recurrence proof",
        "contract-receipt: ClassAPlusActualConstantEntry; n>=6,5<=d<=n+4; original full-offset paths; caps refuse",
        "contract-receipt: ClassAPlusTypedCoincidenceEntry; mixed-letter integral zero is nonterminal",
    }
    if contracts != expected_contracts:
        raise ValueError("missing or unexpected native terminal contract receipt")
    if summaries != required:
        raise ValueError("native success counters do not match the complete original path records")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--native-log", required=True)
    args = parser.parse_args()
    print(json.dumps(check_native_log(args.native_log), sort_keys=True, indent=2))

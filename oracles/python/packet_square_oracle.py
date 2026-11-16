"""Independent Python oracle for the packet-square-v1 export.

Canonical implementation (AGENTS.md: Mojo first): `kernel/psc/packet_square_export.mojo`,
driver `kernel/packet_square_export.mojo`, regression test
`kernel/tests/test_packet_square_export.mojo`, regeneration `kernel/check_packet_square.sh`,
evidence `evidence/packet-square-2026-11-10/`. Acceptance of an exported table is decided by
the Lean checker `Psc.PacketCertificate.Table.check`
(`proof/PscVerif/PscVerif/PacketCertificate.lean`), one `decide +kernel` per committed data
module. This file decides neither; it is a second computation, written independently in
another language, that a reader can run without Mojo or Lean (the plain `pytest` job of
`.github/workflows/ci.yml` collects its test). Scope and literature decision:
`docs/packet-square-stop-go-2026-11-10.md`.

Independence. Nothing here imports `kernel/` or reads a Lean file as a definition. No Mojo
cache (`child_at`, `adj`, `expansions`, `split_count`) is read: every row is derived from
`sigma` and the definitions below, on literal words, with Python `int` only (no float, no
randomness). The one import is the exact PIP screen of the Python reference layer
(`reference/psc_research/pip_screen.py`, itself an independent oracle of
`kernel/psc/pisot.mojo`), used for the header's `pip` field only.

Definitions used (zero-based letters 0, 1, 2; a *state* is a pair of words):

* `balanced_cuts(T, B)`: every `k` with `Parikh(T[:k]) == Parikh(B[:k])`, by one running
  difference vector; a *block* is a pair whose only balanced cuts are `0` and its length.
* the literal ordered factorisation of a state `(u, v)`: the blocks between consecutive
  balanced cuts of `(sigma(u), sigma(v))`, in order (ordinal = position in that order); a
  state is listed in normalised orientation (`u <= v` lexicographically); the factor
  orientation is `+1` iff the raw block is normalised.
* the states: the breadth-first closure of the normalised swap seeds `(ab, ba)`, `a < b`,
  under the factorisation, children in ordinal order, coincidences terminal.
* a packet: an occurrence pair `(state, orientation, top, bottom, factor)`; a root has
  `factor = -1`, orientation `+1`, at every position pair of every noncoincident state
  (row-major); its digit star: for `d < |sigma(a)|`, `e < |sigma(b)|` (row-major) the two
  inflated positions `ti`, `bi` of the oriented block either lie in one block `k` of the
  factorisation (a *child*: the block read in its own words, orientation = packet orientation
  times factor orientation, local positions `ti - lo`, `bi - lo`) or in two (a *split*,
  recorded with both ordinals). `residual` is the prefix defect `Parikh(T[:top]) -
  Parikh(B[:bottom])` of the oriented block; `interior` is "local positions `(0, 0)` in a block
  of ordinal `> 0`"; `success` is "interior, the block is a coincidence, and its letter is the
  target if there is one". Packets are interned in breadth-first order; the birth of a non-root
  packet is the first `(source, d, e)` that produced it (the exporter's rule; the Lean
  `birthOK` accepts any earlier packet whose star holds the child).

What the oracle checks (each a function below, each used by `tests/test_packet_square_oracle.py`):

1. `rebuild` / `compare_rebuild`: every committed JSONL file is rebuilt from `sigma` alone
   (`render`) and its bytes are compared with the rebuilt bytes, final newline and line
   endings included; on a difference the first differing row is named. `check_digests`:
   `SHA256SUMS` lists exactly the four files, with their digests.
2. `audit` / `verify`: a table is checked clause by clause at the layers of the exporter and
   the Lean checker (L0 JSON shape, rows, counts and budget; L1 PIP record; L2 states; L3
   literal factorisation; L4 literal packet rows; L5 full digit stars; L6 roots, keys, key
   order, reachability from the roots and births; L7 hub bits). The L0 shape is exact: every
   row has the key list of its record type in schema order, every integer field and entry is
   a JSON integer (never a float or a boolean), every flag a boolean, every hub bit 0, 1 or
   null. The budget row must admit the table (states, the longest state, packets and child
   entries within their caps); a different admissible budget row is accepted, the committed
   default one is pinned by item 1. Where the exporter and the checker differ, the stricter
   rule: L2 also requires every state to be reachable from the seeds; L7 accepts either no
   hub rows or all of them, one per noncoincident state and hub, in order. The L5 star
   equation makes the packet set a *fixed point* (it contains the roots and is closed under
   the literal transition); the L6 breadth-first search makes it the *least* one.
   Negative-control generators (`forged_mirror`, `drop_split`, `side_swap`, ...) produce
   tables that must be refused.
3. `transport_law`: on every child entry, the residual of the destination row, computed from
   its own listed words, equals `M r + lambda` with `r` the residual of the source row, `M`
   the incidence matrix (`M[i][j]` = number of `i` in `sigma(j)`) and `lambda` the prefix
   defect of the two digits; on every digit pair, split or not, the asynchronous form
   `Parikh(sigma(T)[:ti]) - Parikh(sigma(B)[:bi]) = M r + lambda`. `split_account`: every
   expandable packet has exactly `|sigma(a)| * |sigma(b)|` entries, children plus splits.
4. `compare_with_archive`: the v1 rows agree with the archived `target-aware-bpa-v1` dumps
   (`evidence/target-aware-bpa-2026-10-02/`) on states, factors, packets and edges, and the
   v1 birth is the archive's first incoming edge.
5. `absolute_replay`: from each normalised swap seed `(ab, ba)`, up to a stated level, every
   absolute pair reached by retained edges in `(sigma^n(ab), sigma^n(ba))` reads as a listed
   packet, and the listed row's state, orientation, positions, factor, addresses, letters,
   residual, interior and success fields are those of the absolute words (the residual is the
   absolute prefix defect); its `birth` field is not compared, since it names the first
   incoming entry of the table, not the parent of this pair. The packet's star entry for every
   digit pair is the absolute outcome. The pairs reached at level `n` are exactly the pairs
   inside the noncoincident blocks of the level-`n` factorisation plus the single pair of
   each coincidence block whose parent block is noncoincident; the packets read are exactly
   those within the level bound of the seed roots. The same readings, recomputed from the
   absolute words alone (`frame_readings`, no packet or star row read), must agree. The
   swapped frame `(ba, ab)` is replayed too, from its words alone: its iterates are the side
   swap of those of `(ab, ba)`, with the same cuts, and the check is that its reading of every
   pair `(Q, P)` is the mirror (`_mirror`: orientation and residual negated; positions,
   addresses and letters exchanged) of the normalised reading of `(P, Q)`. These mirrored readings need not be listed packets: the table lists roots in
   orientation `+1` only (the normalised roots), so the twelve mirrored root readings are
   never listed, and the count of distinct mirrored readings that are listed is reported as
   an observation. Bounded and finite; a level bound is a budget, not a verdict.
6. `parse_lean_module` / `compare_lean_module` / `check_lean_template`: the committed Lean
   data modules (`PscVerif/PacketSquareData/*.lean`, or the flat `PacketSquareData*.lean`
   layout) are parsed and compared field by field with the JSONL, and the text is checked
   against a template rendered here from the JSONL: every line outside the module
   docstring's free paragraph must equal the template (the leading comment with its
   Command, Rows and PIP lines, the import, namespace, `open`, the two declaration
   docstrings, every line of the table body including its two `--` comment lines, the
   theorem and `end`), so an extra declaration, option, instance, import, `open` or comment
   is refused. The free paragraph may hold any text without a comment delimiter `/-` or
   `-/`; its prose is not compared here. The byte comparison of the whole module with the
   Mojo emitter's output is `kernel/check_packet_square.sh`, not this oracle.

Fail-closed behaviour: a refused table, a malformed file (not JSON, not an object, a missing
field) or a malformed Lean module raises `InvalidPacketSquare` naming its layer; an exhausted
budget raises `BudgetExhausted` (inconclusive, never a verdict). Replay:
`python3 oracles/python/packet_square_oracle.py` and `python3 -m pytest -q -p no:cacheprovider
tests/test_packet_square_oracle.py`. The command line exits 0 and prints its pass line only
when every check passed on the four fixtures and all four Lean data modules were compared;
1 on any refusal, inconclusive budget or malformed input, and (default) when a Lean data
module is missing; 2, with an INCOMPLETE line and never the pass line, when
`--allow-missing-lean` is given (for use before the modules are committed) and a module is
missing while every other check passed. `--evidence` and `--lean-root` name other
directories (the negative controls of the test use copies).

Non-claims. This is finite, executable evidence about four committed tables, not a proof.
It does not prove the Mojo engine or the Lean checker correct, says nothing about states
outside the tables or about levels beyond the stated bound, uses no Pisot, unimodularity,
legality or recognizability hypothesis, and does not advance, prove or close C4, G1, #84,
#138, #139 or PSC. The PIP field is recorded, never a filter: `1/012/1` is not Pisot.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import defaultdict, deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT / "reference") not in sys.path:
    sys.path.insert(0, str(ROOT / "reference"))
from psc_research.pip_screen import charpoly, irreducible, mat, pisot, primitive  # noqa: E402

SCHEMA = "packet-square-v1"
STATUS = "finite-certificate-input"
EVIDENCE = ROOT / "evidence/packet-square-2026-11-10"
ARCHIVE = ROOT / "evidence/target-aware-bpa-2026-10-02"
LEAN_ROOT = ROOT / "proof/PscVerif"
DEFAULT_BUDGET = {"bpa_states": 20000, "bpa_length": 10000, "packets": 200000, "edges": 2000000}
# file stem -> (sigma, Lean module suffix)
FIXTURES = {
    "tribonacci": ("01/02/0", "Tribonacci"),
    "real-secondary": ("1/02/202", "RealSecondary"),
    "non-pisot-strict": ("1/012/1", "NonPisot"),
    "gf-actual": ("1/2/021", "GfActual"),
}
ARCHIVED = ("real-secondary", "non-pisot-strict", "gf-actual")
LAYERS = ("L0", "L1", "L2", "L3", "L4", "L5", "L6", "L7")
RECORDS = ("budget", "header", "state", "factor", "packet", "star", "key_order", "hub", "summary")


class InvalidPacketSquare(ValueError):
    """A refused table or input; `layer` names the first failing layer."""

    def __init__(self, layer, reason):
        super().__init__(f"{layer}: {reason}")
        self.layer = layer
        self.reason = reason


class BudgetExhausted(RuntimeError):
    """A cap was reached. Inconclusive: an exhausted budget is not a verdict."""


def require(condition, layer, reason):
    if not condition:
        raise InvalidPacketSquare(layer, reason)


def fail_closed(layer):
    """A lookup that fails on a malformed table refuses at `layer`; it never passes."""
    def wrap(fn):
        def run(*args, **kwargs):
            try:
                return fn(*args, **kwargs)
            except (KeyError, IndexError, TypeError, ValueError, AttributeError) as e:
                if isinstance(e, InvalidPacketSquare):
                    raise
                raise InvalidPacketSquare(layer, f"malformed input in {fn.__name__}: {e!r}") from e
        run.__name__, run.__doc__ = fn.__name__, fn.__doc__
        return run
    return wrap


# ---------------------------------------------------------------------------
# Literal words
# ---------------------------------------------------------------------------


def parse_sigma(text):
    """`1/02/202` -> ((1,), (0, 2), (2, 0, 2)); three nonempty words over 0, 1, 2."""
    words = text.split("/")
    require(len(words) == 3 and all(words) and all(c in "012" for w in words for c in w),
            "L0", f"sigma {text!r} is not three nonempty words over 0, 1, 2")
    return tuple(tuple(int(c) for c in w) for w in words)


def check_sigma(sigma):
    sigma = tuple(tuple(w) for w in sigma)
    require(len(sigma) == 3 and all(0 < len(w) <= 256 for w in sigma)
            and all(type(a) is int and 0 <= a < 3 for w in sigma for a in w),
            "L0", "sigma must be three nonempty words over 0, 1, 2 of length at most 256")
    return sigma


def sigma_text(sigma):
    return "/".join("".join(map(str, w)) for w in sigma)


def inflate(sigma, word):
    return tuple(x for a in word for x in sigma[a])


def image_starts(sigma, word):
    out = [0]
    for a in word:
        out.append(out[-1] + len(sigma[a]))
    return out


def defect(top, bottom, i, j):
    """Prefix defect Parikh(top[:i]) - Parikh(bottom[:j]) (both prefixes from position 0)."""
    out = [0, 0, 0]
    for a in top[:i]:
        out[a] += 1
    for b in bottom[:j]:
        out[b] -= 1
    return tuple(out)


def balanced_cuts(top, bottom):
    """Every k with Parikh(top[:k]) == Parikh(bottom[:k]), by one running difference."""
    require(len(top) == len(bottom), "L2", "a balanced pair has two words of one length")
    diff, unequal, out = [0, 0, 0], 0, [0]
    for k in range(len(top)):
        for letter, step in ((top[k], 1), (bottom[k], -1)):
            before = diff[letter] != 0
            diff[letter] += step
            unequal += (diff[letter] != 0) - before
        if unequal == 0:
            out.append(k + 1)
    return out


def normalise(pair):
    u, v = pair
    return (u, v) if u <= v else (v, u)


def orient(pair, sign):
    require(sign in (1, -1), "L4", "orientation outside {-1, 1}")
    return pair if sign == 1 else (pair[1], pair[0])


def is_block(pair):
    u, v = pair
    return len(u) == len(v) > 0 and balanced_cuts(u, v) == [0, len(u)]


def incidence(sigma):
    """M[i][j] = number of letters i in sigma(j)."""
    return tuple(tuple(sigma[j].count(i) for j in range(3)) for i in range(3))


def act(m, r):
    return tuple(sum(m[i][j] * r[j] for j in range(3)) for i in range(3))


def add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def transpose(m):
    return tuple(tuple(m[j][i] for j in range(3)) for i in range(3))


def factorisation(sigma, pair):
    """Inflated words and their balanced cuts; refused unless the inflation is balanced."""
    top, bottom = inflate(sigma, pair[0]), inflate(sigma, pair[1])
    cuts = balanced_cuts(top, bottom)
    require(cuts[-1] == len(top), "L3", "inflated state is not balanced")
    return top, bottom, cuts


def literal_star(sigma, block, top, bottom):
    """The full digit star of the occurrence pair `(block, top, bottom)`.

    One entry per digit pair, row-major: `("split", d, e, kTop, kBot)` or
    `("child", d, e, k, lo, hi, ti, bi)` with `ti`, `bi` the inflated positions and
    `[lo, hi)` the span of block `k` of the literal factorisation.
    """
    T, B = block
    TT, BB, cuts = factorisation(sigma, block)
    owner = [0] * len(TT)
    for k in range(len(cuts) - 1):
        for x in range(cuts[k], cuts[k + 1]):
            owner[x] = k
    st, sb = image_starts(sigma, T), image_starts(sigma, B)
    entries = []
    for d in range(len(sigma[T[top]])):
        for e in range(len(sigma[B[bottom]])):
            ti, bi = st[top] + d, sb[bottom] + e
            kt, kb = owner[ti], owner[bi]
            if kt != kb:
                entries.append(("split", d, e, kt, kb))
            else:
                entries.append(("child", d, e, kt, cuts[kt], cuts[kt + 1], ti, bi))
    return TT, BB, entries


def cut_address(sigma, word, g):
    """(source occurrence, digit) of the inflated position `g` of `word`."""
    starts = image_starts(sigma, word)
    for i in range(len(word)):
        if starts[i] <= g < starts[i + 1]:
            return i, g - starts[i]
    raise InvalidPacketSquare("L4", "inflated position outside the image")


def pip_status(sigma):
    """Primitive, irreducible characteristic cubic, Pisot Perron root (exact reference screen)."""
    m = mat({i + 1: tuple(a + 1 for a in w) for i, w in enumerate(sigma)})
    t, u, d = charpoly(m)
    return primitive(m) and irreducible(t, u, d) and pisot(t, u, d)


def hub_side(pair, hub):
    """0 if the top first letter is the hub, 1 if the bottom one is, None otherwise."""
    u, v = pair
    if u[0] == v[0]:
        return None
    if u[0] == hub:
        return 0
    if v[0] == hub:
        return 1
    return None


def hub_bit(parent, child, orientation, hub):
    a, b = hub_side(parent, hub), hub_side(child, hub)
    if a is None or b is None:
        return None
    return a ^ b ^ int(orientation == -1)


def key_tuple(p):
    """Packet identity in key-order significance: (state, sign bit, top, bottom, factor + 1)."""
    return (p["state"], 1 if p["orientation"] == 1 else 0, p["occurrences"][0],
            p["occurrences"][1], p["factor_edge"] + 1)


def packet_key(p):
    return (p["state"], p["orientation"], p["occurrences"][0], p["occurrences"][1],
            p["factor_edge"])


# ---------------------------------------------------------------------------
# Item 1: rebuild every row from sigma alone
# ---------------------------------------------------------------------------


def bpa_closure(sigma, state_cap, length_cap):
    """Breadth-first closure of the normalised swap seeds; coincidences are terminal."""
    queue = deque(normalise(((a, b), (b, a))) for a in range(3) for b in range(a + 1, 3))
    states, index = [], {}
    while queue:
        state = queue.popleft()
        if state in index:
            continue
        if len(states) >= state_cap:
            raise BudgetExhausted("BPA state budget exhausted: inconclusive")
        if len(state[0]) > length_cap:
            raise BudgetExhausted("BPA length budget exhausted: inconclusive")
        index[state] = len(states)
        states.append(state)
        if state[0] == state[1]:
            continue
        top, bottom, cuts = factorisation(sigma, state)
        for lo, hi in zip(cuts, cuts[1:]):
            queue.append(normalise((top[lo:hi], bottom[lo:hi])))
    return states


def packet_row(pid, state, sign, occurrences, factor, top_address, bottom_address, letters,
               residual, interior, success, birth):
    return {"record": "packet", "id": pid, "state": state, "orientation": sign,
            "occurrences": list(occurrences), "factor_edge": factor, "top_address": top_address,
            "bottom_address": bottom_address, "target_letters": list(letters),
            "residual": list(residual), "interior": interior, "success": success, "birth": birth}


CARRIED = ("top_address", "bottom_address", "target_letters", "residual", "interior", "success")


def rebuild(sigma, target=None, budget=None, hub_rows=True):
    """The packet-square-v1 rows of `sigma`, in schema order, computed from literal words."""
    sigma = check_sigma(sigma)
    require(target is None or target in (0, 1, 2), "L0", "target must be None or a letter")
    budget = dict(DEFAULT_BUDGET if budget is None else budget)
    require(sorted(budget) == sorted(DEFAULT_BUDGET) and all(
        type(x) is int and x > 0 for x in budget.values()), "L0", "budgets must be positive")
    states = bpa_closure(sigma, budget["bpa_states"], budget["bpa_length"])
    index = {state: i for i, state in enumerate(states)}

    factors, factor_of = [], {}
    for s, state in enumerate(states):
        if state[0] == state[1]:
            continue
        top, bottom, cuts = factorisation(sigma, state)
        for k, (lo, hi) in enumerate(zip(cuts, cuts[1:])):
            raw = (top[lo:hi], bottom[lo:hi])
            norm = normalise(raw)
            require(norm in index, "L2", "a literal block is not a listed state")
            factor_of[s, k] = len(factors)
            factors.append({"record": "factor", "id": len(factors), "parent": s, "ordinal": k,
                            "child": index[norm], "orientation": 1 if raw == norm else -1,
                            "span": [lo, hi, len(top)]})

    packets, stars, ids = [], [], {}
    edges = splits = 0

    def intern(row):
        key = packet_key(row)
        if key in ids:
            old = packets[ids[key]]
            require(all(old[f] == row[f] for f in CARRIED), "L6",
                    "one packet key carries two occurrence pairs")
            return ids[key]
        if len(packets) >= budget["packets"]:
            raise BudgetExhausted("packet cap exhausted: inconclusive")
        row["id"] = ids[key] = len(packets)
        packets.append(row)
        return row["id"]

    for s, (u, v) in enumerate(states):
        if u == v:
            continue
        for P in range(len(u)):
            for Q in range(len(v)):
                intern(packet_row(None, s, 1, (P, Q), -1, None, None, (u[P], v[Q]),
                                  defect(u, v, P, Q), False, False, None))
    head = 0
    while head < len(packets):
        p = packets[head]
        state = states[p["state"]]
        expanded = state[0] != state[1] and not p["success"]
        entries = []
        if expanded:
            P, Q = p["occurrences"]
            TT, BB, star = literal_star(sigma, orient(state, p["orientation"]), P, Q)
            for entry in star:
                if entry[0] == "split":
                    entries.append(list(entry))
                    splits += 1
                    continue
                _, d, e, k, lo, hi, ti, bi = entry
                raw = (TT[lo:hi], BB[lo:hi])
                norm = normalise(raw)
                fid = factor_of[p["state"], k]
                sign = p["orientation"] * factors[fid]["orientation"]
                require(orient(norm, sign) == raw, "L3", "factor orientation disagrees with words")
                lt, lb = ti - lo, bi - lo
                interior = lt == 0 and lb == 0 and k > 0
                success = interior and raw[0] == raw[1] and (target is None or raw[0][0] == target)
                if edges >= budget["edges"]:
                    raise BudgetExhausted("packet edge cap exhausted: inconclusive")
                j = intern(packet_row(None, index[norm], sign, (lt, lb), fid, [P, d, ti, lt],
                                      [Q, e, bi, lb], (raw[0][lt], raw[1][lb]),
                                      defect(raw[0], raw[1], lt, lb), interior, success,
                                      [head, d, e]))
                entries.append(["child", d, e, j])
                edges += 1
        stars.append({"record": "star", "packet": head, "expanded": expanded, "entries": entries})
        head += 1

    order = sorted(range(len(packets)), key=lambda i: key_tuple(packets[i]))
    require(all(key_tuple(packets[a]) != key_tuple(packets[b]) for a, b in zip(order, order[1:])),
            "L6", "two packets share one key")
    hubs = []
    if hub_rows:
        for s, state in enumerate(states):
            if state[0] == state[1]:
                continue
            fids = [f["id"] for f in factors if f["parent"] == s]
            for hub in range(3):
                bits = [hub_bit(state, states[factors[f]["child"]], factors[f]["orientation"], hub)
                        for f in fids]
                hubs.append({"record": "hub", "state": s, "hub": hub, "factors": fids,
                             "bits": bits})
    roots = sum(p["factor_edge"] == -1 for p in packets)
    rows = [{"record": "budget", **budget}]
    rows.append({"record": "header", "schema": SCHEMA, "status": STATUS,
                 "sigma": [list(w) for w in sigma], "letters": [0, 1, 2], "target": target,
                 "synchronize_right": False, "pip": pip_status(sigma), "states": len(states),
                 "factors": len(factors), "packets": len(packets), "edges": edges,
                 "split_descendants": splits, "roots": roots, "hub_rows": len(hubs)})
    rows += [{"record": "state", "id": s, "top": list(u), "bottom": list(v), "coincidence": u == v}
             for s, (u, v) in enumerate(states)]
    rows += factors + packets + stars
    rows.append({"record": "key_order", "packets": order})
    rows += hubs
    rows.append({"record": "summary", "packets": len(packets), "edges": edges,
                 "split_descendants": splits, "part_b": "open", "C4": "unchanged",
                 "G1": "unchanged", "PSC": "unchanged"})
    return rows


def render(rows):
    """Compact JSON lines, keys in row order, as the exporter prints them."""
    return [json.dumps(row, separators=(",", ":"), ensure_ascii=False) for row in rows]


def load_rows(path):
    """The JSON value of every line of `path`; a line that is not JSON refuses at L0."""
    try:
        text = Path(path).read_bytes().decode("utf-8")
    except UnicodeDecodeError as e:
        raise InvalidPacketSquare("L0", f"{Path(path).name} is not UTF-8: {e}") from e
    rows = []
    for k, line in enumerate(text.splitlines()):
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError as e:
            raise InvalidPacketSquare("L0", f"{Path(path).name}: line {k + 1} is not JSON: {e}") \
                from e
    return rows


def fixture_path(name, directory=None):
    require(name in FIXTURES, "L0", f"unknown fixture {name!r}")
    return Path(EVIDENCE if directory is None else directory) / f"{name}.jsonl"


def compare_rebuild(name, directory=None):
    """Rebuild the file of fixture `name` from its sigma and compare the bytes; returns the
    row count. On a difference the first differing row is named (a carriage return or a
    missing final newline is a difference)."""
    sigma = parse_sigma(FIXTURES[name][0])
    data = fixture_path(name, directory).read_bytes()
    rebuilt = render(rebuild(sigma))
    expected = ("\n".join(rebuilt) + "\n").encode()
    if data == expected:
        return len(rebuilt)
    got, want = data.split(b"\n"), expected.split(b"\n")
    for k, (a, b) in enumerate(zip(got, want)):
        require(a == b, "L0", f"{name}: row {k + 1} differs from the rebuild:\n"
                f"{a.decode(errors='replace')!r}\n{b.decode(errors='replace')!r}")
    raise InvalidPacketSquare("L0", f"{name}: the bytes differ from the rebuild after the common "
                              f"rows ({len(got) - 1} newline-terminated rows committed, "
                              f"{len(rebuilt)} rebuilt; a missing final newline or trailing "
                              "bytes)")


def check_digests(directory=None):
    """SHA256SUMS lists exactly the committed JSONL files, with their digests."""
    directory = Path(EVIDENCE if directory is None else directory)
    listed = {}
    for line in (directory / "SHA256SUMS").read_text().splitlines():
        fields = line.split()
        require(len(fields) == 2, "L0", f"SHA256SUMS line {line!r}")
        digest, name = fields
        listed[name] = digest
    present = sorted(p.name for p in directory.glob("*.jsonl"))
    require(sorted(listed) == present == sorted(f"{n}.jsonl" for n in FIXTURES), "L0",
            "SHA256SUMS does not list exactly the four fixtures")
    for name, digest in listed.items():
        require(hashlib.sha256((directory / name).read_bytes()).hexdigest() == digest, "L0",
                f"{name}: digest differs from SHA256SUMS")
    return listed


# ---------------------------------------------------------------------------
# Item 2: audit a table clause by clause (fixed point and reachability included)
# ---------------------------------------------------------------------------


class Table:
    """The records of one table, in file order (no checks beyond what reading them needs: a
    row that is not an object, a missing field or an unreadable sigma refuses at L0)."""

    @fail_closed("L0")
    def __init__(self, rows):
        by = defaultdict(list)
        for row in rows:
            by[row.get("record")].append(row)
        self.rows = rows
        self.by = by
        self.budget = by["budget"][0] if by["budget"] else {}
        self.header = by["header"][0] if by["header"] else {}
        self.summary = by["summary"][0] if by["summary"] else {}
        self.sigma = tuple(tuple(w) for w in self.header.get("sigma", ()))
        self.target = self.header.get("target")
        self.states = [(tuple(r["top"]), tuple(r["bottom"])) for r in by["state"]]
        self.factors = by["factor"]
        self.packets = by["packet"]
        self.stars = by["star"]
        self.key_order = by["key_order"][0]["packets"] if by["key_order"] else []
        self.hubs = by["hub"]


# The exact JSON shape of every record type: its keys in schema order and the type of each
# value. `int` is a JSON integer (a Python `int` that is not a `bool`); a length of None is
# any length.
_INT, _BOOL, _STR = ("int",), ("bool",), ("str",)


def _ints(n=None):
    return ("ints", n)


def _opt(kind):
    return ("opt", kind)


SHAPES = {
    "budget": (("record", _STR), ("bpa_states", _INT), ("bpa_length", _INT),
               ("packets", _INT), ("edges", _INT)),
    "header": (("record", _STR), ("schema", _STR), ("status", _STR), ("sigma", ("sigma",)),
               ("letters", _ints()), ("target", _opt(_INT)), ("synchronize_right", _BOOL),
               ("pip", _BOOL), ("states", _INT), ("factors", _INT), ("packets", _INT),
               ("edges", _INT), ("split_descendants", _INT), ("roots", _INT),
               ("hub_rows", _INT)),
    "state": (("record", _STR), ("id", _INT), ("top", _ints()), ("bottom", _ints()),
              ("coincidence", _BOOL)),
    "factor": (("record", _STR), ("id", _INT), ("parent", _INT), ("ordinal", _INT),
               ("child", _INT), ("orientation", _INT), ("span", _ints(3))),
    "packet": (("record", _STR), ("id", _INT), ("state", _INT), ("orientation", _INT),
               ("occurrences", _ints(2)), ("factor_edge", _INT),
               ("top_address", _opt(_ints(4))), ("bottom_address", _opt(_ints(4))),
               ("target_letters", _ints(2)), ("residual", _ints(3)), ("interior", _BOOL),
               ("success", _BOOL), ("birth", _opt(_ints(3)))),
    "star": (("record", _STR), ("packet", _INT), ("expanded", _BOOL), ("entries", ("entries",))),
    "key_order": (("record", _STR), ("packets", _ints())),
    "hub": (("record", _STR), ("state", _INT), ("hub", _INT), ("factors", _ints()),
            ("bits", ("bits",))),
    "summary": (("record", _STR), ("packets", _INT), ("edges", _INT),
                ("split_descendants", _INT), ("part_b", _STR), ("C4", _STR), ("G1", _STR),
                ("PSC", _STR)),
}


def _is_int(x):
    return type(x) is int


def _has_kind(x, kind):
    tag = kind[0]
    if tag == "int":
        return _is_int(x)
    if tag == "bool":
        return type(x) is bool
    if tag == "str":
        return type(x) is str
    if tag == "opt":
        return x is None or _has_kind(x, kind[1])
    if tag == "ints":
        return type(x) is list and (kind[1] is None or len(x) == kind[1]) and all(
            map(_is_int, x))
    if tag == "sigma":
        return type(x) is list and len(x) == 3 and all(_has_kind(w, _ints()) for w in x)
    if tag == "entries":
        return type(x) is list and all(
            type(e) is list and len(e) >= 1 and (
                (e[0] == "child" and len(e) == 4) or (e[0] == "split" and len(e) == 5))
            and type(e[0]) is str and all(map(_is_int, e[1:])) for e in x)
    if tag == "bits":
        return type(x) is list and all(b is None or (_is_int(b) and b in (0, 1)) for b in x)
    raise AssertionError(f"unknown shape kind {kind!r}")


def shape_failures(rows):
    """Every row whose JSON shape is not exactly that of its record type (L0)."""
    out = []
    if type(rows) is not list:
        return ["the table is not a list of rows"]
    for k, row in enumerate(rows):
        if type(row) is not dict:
            out.append(f"row {k + 1} is not a JSON object")
            continue
        shape = SHAPES.get(row.get("record"))
        if shape is None:
            out.append(f"row {k + 1}: unknown record {row.get('record')!r}")
            continue
        keys = [key for key, _ in shape]
        if list(row) != keys:
            out.append(f"row {k + 1} ({row['record']}): keys {list(row)} are not {keys}")
            continue
        for key, kind in shape:
            if not _has_kind(row[key], kind):
                out.append(f"row {k + 1} ({row['record']}): field {key} = {row[key]!r} is not "
                           f"of JSON type {kind!r}")
    return out


def _layer_l0(t, fail):
    for reason in shape_failures(t.rows):
        fail(reason)
    kinds = [row.get("record") for row in t.rows]
    ranks = [RECORDS.index(k) if k in RECORDS else -1 for k in kinds]
    if -1 in ranks or ranks != sorted(ranks):
        fail("records are not in schema order")
    for once in ("budget", "header", "key_order", "summary"):
        if kinds.count(once) != 1:
            fail(f"expected exactly one {once} row")
    if kinds and kinds[0] != "budget":
        fail("the first row is not the budget row")
    if sorted(k for k in t.budget if k != "record") != sorted(DEFAULT_BUDGET) or not all(
            type(t.budget[k]) is int and t.budget[k] > 0 for k in DEFAULT_BUDGET):
        fail("budget row malformed")
    h = t.header
    if (h.get("schema"), h.get("status"), h.get("letters"), h.get("synchronize_right")) != (
            SCHEMA, STATUS, [0, 1, 2], False):
        fail("header schema, status, letters or synchronize_right")
    if h.get("target") not in (None, 0, 1, 2):
        fail("header target is neither null nor a letter")
    try:
        check_sigma(t.sigma)
    except InvalidPacketSquare as e:
        fail(e.reason)
    for kind, rows, field in (("state", t.by["state"], "id"), ("factor", t.factors, "id"),
                              ("packet", t.packets, "id"), ("star", t.stars, "packet")):
        if [r[field] for r in rows] != list(range(len(rows))):
            fail(f"{kind} rows are not numbered 0, 1, ...")
    children = sum(e[0] == "child" for s in t.stars for e in s["entries"])
    splits = sum(e[0] == "split" for s in t.stars for e in s["entries"])
    counts = {"states": len(t.states), "factors": len(t.factors), "packets": len(t.packets),
              "edges": children, "split_descendants": splits,
              "roots": sum(p["factor_edge"] == -1 for p in t.packets), "hub_rows": len(t.hubs)}
    for field, value in counts.items():
        if h.get(field) != value:
            fail(f"header {field} = {h.get(field)}, rows give {value}")
    s = t.summary
    if (s.get("packets"), s.get("edges"), s.get("split_descendants")) != (
            counts["packets"], counts["edges"], counts["split_descendants"]):
        fail("summary counts differ from the rows")
    if (s.get("part_b"), s.get("C4"), s.get("G1"), s.get("PSC")) != (
            "open", "unchanged", "unchanged", "unchanged"):
        fail("summary status fields")
    # The budget row must admit the table: the exporter refuses before it exceeds a cap (a
    # state is added only below the state cap and only if its length is within the length
    # cap; a packet or a child entry only below its cap).
    b = t.budget
    longest = max((len(u) for u, _ in t.states), default=0)
    for cap, used in (("bpa_states", len(t.states)), ("bpa_length", longest),
                      ("packets", len(t.packets)), ("edges", children)):
        if _is_int(b.get(cap)) and used > b[cap]:
            fail(f"budget {cap} = {b[cap]} does not admit the table ({used})")


def _layer_l1(t, fail):
    if t.header.get("pip") is not pip_status(t.sigma):
        fail("header pip differs from the exact PIP screen of sigma")


def _layer_l2(t, fail):
    # Stricter than the Lean `statesOK`/`seedsOK`, as the exporter is: every state must also be
    # reachable from the seeds (the Lean checker accepts an extra listed block: `fibExtra`).
    index = {}
    for s, (row, state) in enumerate(zip(t.by["state"], t.states)):
        if not is_block(state):
            fail(f"state {s} is not an irreducible balanced pair")
        if normalise(state) != state:
            fail(f"state {s} is not in normalised orientation")
        if row["coincidence"] is not (state[0] == state[1]):
            fail(f"state {s} coincidence flag")
        if state in index:
            fail(f"state {s} repeats state {index[state]}")
        index.setdefault(state, s)
    reached = [False] * len(t.states)
    queue = deque()
    for a in range(3):
        for b in range(a + 1, 3):
            seed = ((a, b), (b, a))
            if seed not in index:
                fail(f"the normalised seed {seed} is not listed")
            elif not reached[index[seed]]:
                reached[index[seed]] = True
                queue.append(index[seed])
    while queue:
        s = queue.popleft()
        state = t.states[s]
        if state[0] == state[1]:
            continue
        top, bottom, cuts = factorisation(t.sigma, state)
        for lo, hi in zip(cuts, cuts[1:]):
            child = normalise((top[lo:hi], bottom[lo:hi]))
            if child not in index:
                fail(f"state {s}: literal child {child} is not listed (not child-closed)")
            elif not reached[index[child]]:
                reached[index[child]] = True
                queue.append(index[child])
    if not all(reached):
        fail("states unreachable from the swap seeds")


def _literal_factor_rows(t, s, index):
    state = t.states[s]
    if state[0] == state[1]:
        return []
    top, bottom, cuts = factorisation(t.sigma, state)
    out = []
    for k, (lo, hi) in enumerate(zip(cuts, cuts[1:])):
        raw = (top[lo:hi], bottom[lo:hi])
        out.append((s, k, index.get(normalise(raw)), 1 if raw == normalise(raw) else -1,
                    [lo, hi, len(top)]))
    return out


def _layer_l3(t, fail):
    index = {state: s for s, state in enumerate(t.states)}
    if any(not 0 <= f["parent"] < len(t.states) for f in t.factors):
        fail("factor parent outside the states")
    for s in range(len(t.states)):
        listed = [(f["parent"], f["ordinal"], f["child"], f["orientation"], f["span"])
                  for f in t.factors if f["parent"] == s]
        if listed != _literal_factor_rows(t, s, index):
            fail(f"state {s}: factor rows differ from the literal ordered factorisation")


def _decode(t, p):
    """(oriented block, parent oriented block, factor row) of a packet row, or a refusal."""
    require(0 <= p["state"] < len(t.states), "L4", f"packet {p['id']}: state outside the table")
    block = orient(t.states[p["state"]], p["orientation"])
    if p["factor_edge"] == -1:
        return block, None, None
    require(0 <= p["factor_edge"] < len(t.factors), "L4", f"packet {p['id']}: factor outside")
    f = t.factors[p["factor_edge"]]
    require(f["child"] == p["state"], "L4", f"packet {p['id']}: factor child is not its state")
    parent = orient(t.states[f["parent"]], p["orientation"] * f["orientation"])
    return block, parent, f


def _layer_l4(t, fail):
    for p in t.packets:
        try:
            block, parent, f = _decode(t, p)
        except InvalidPacketSquare as e:
            fail(e.reason)
            continue
        P, Q = p["occurrences"]
        if not (0 <= P < len(block[0]) and 0 <= Q < len(block[1])):
            fail(f"packet {p['id']}: position outside its block")
            continue
        if p["target_letters"] != [block[0][P], block[1][Q]]:
            fail(f"packet {p['id']}: letters are not the letters at its positions")
        if p["residual"] != list(defect(block[0], block[1], P, Q)):
            fail(f"packet {p['id']}: residual is not the prefix defect of its block")
        if f is None:
            if (p["orientation"], p["top_address"], p["bottom_address"], p["interior"],
                    p["success"]) != (1, None, None, False, False):
                fail(f"packet {p['id']}: root fields")
            continue
        top, bottom, cuts = factorisation(t.sigma, parent)
        k = f["ordinal"]
        if not 0 <= k < len(cuts) - 1 or (top[cuts[k]:cuts[k + 1]],
                                          bottom[cuts[k]:cuts[k + 1]]) != block:
            fail(f"packet {p['id']}: block {k} of its parent is not its oriented state")
            continue
        lo = cuts[k]
        for side, field, word, pos in ((0, "top_address", parent[0], P),
                                       (1, "bottom_address", parent[1], Q)):
            g = lo + pos
            if p[field] != [*cut_address(t.sigma, word, g), g, pos]:
                fail(f"packet {p['id']}: {field} is not the cut address of its position")
        interior = P == 0 and Q == 0 and k > 0
        success = interior and block[0] == block[1] and (
            t.target is None or block[0][0] == t.target)
        if p["interior"] is not interior or p["success"] is not success:
            fail(f"packet {p['id']}: interior or success bit")


def _resolve(t):
    ids = defaultdict(list)
    for p in t.packets:
        ids[packet_key(p)].append(p["id"])
    return ids


def expected_star(t, p, ids, factor_of):
    """The literal star of packet row `p`, destinations resolved through the table's keys."""
    state = t.states[p["state"]]
    if state[0] == state[1] or p["success"]:
        return False, []
    P, Q = p["occurrences"]
    TT, BB, star = literal_star(t.sigma, orient(state, p["orientation"]), P, Q)
    index = {s: i for i, s in enumerate(t.states)}
    out = []
    for entry in star:
        if entry[0] == "split":
            out.append(list(entry))
            continue
        _, d, e, k, lo, hi, ti, bi = entry
        fid = factor_of.get((p["state"], k))
        require(fid is not None, "L5", f"packet {p['id']}: no factor row for ordinal {k}")
        raw = (TT[lo:hi], BB[lo:hi])
        key = (index.get(normalise(raw)), p["orientation"] * t.factors[fid]["orientation"],
               ti - lo, bi - lo, fid)
        found = ids.get(key, [])
        require(len(found) == 1, "L5", f"packet {p['id']}: literal child {key} is "
                + ("not listed (the table is not closed)" if not found else "listed twice"))
        out.append(["child", d, e, found[0]])
    return True, out


def _layer_l5(t, fail):
    if len(t.stars) != len(t.packets):
        fail("one star row per packet")
    ids = _resolve(t)
    factor_of = {}
    for f in t.factors:
        factor_of.setdefault((f["parent"], f["ordinal"]), f["id"])
    for p, star in zip(t.packets, t.stars):
        try:
            expanded, entries = expected_star(t, p, ids, factor_of)
        except InvalidPacketSquare as e:
            fail(e.reason)
            continue
        if star["expanded"] is not expanded:
            fail(f"packet {p['id']}: expanded flag")
        if star["entries"] != entries:
            fail(f"packet {p['id']}: star differs from the literal digit star")


def unreachable(t):
    """Packets not reached from a root row by child entries (breadth-first)."""
    succ = defaultdict(list)
    for star in t.stars:
        for e in star["entries"]:
            if e[0] == "child":
                succ[star["packet"]].append(e[3])
    reached = {p["id"] for p in t.packets if p["factor_edge"] == -1}
    frontier = deque(reached)
    while frontier:
        for j in succ[frontier.popleft()]:
            if j not in reached:
                reached.add(j)
                frontier.append(j)
    return sorted({p["id"] for p in t.packets} - reached)


def _layer_l6(t, fail):
    want = [(s, 1, P, Q) for s, (u, v) in enumerate(t.states) if u != v
            for P in range(len(u)) for Q in range(len(v))]
    roots = [(p["state"], p["orientation"], *p["occurrences"]) for p in t.packets
             if p["factor_edge"] == -1]
    if roots != want:
        fail("root rows are not every position pair of every noncoincident state, in order")
    keys = [key_tuple(p) for p in t.packets]
    if len(set(keys)) != len(keys):
        fail("two packets share one key")
    order = t.key_order
    if sorted(order) != list(range(len(t.packets))):
        fail("key order is not a permutation of the packet ids")
    elif any(keys[a] >= keys[b] for a, b in zip(order, order[1:])):
        fail("keys do not strictly increase along the key order")
    lost = unreachable(t)
    if lost:
        fail(f"{len(lost)} packets unreachable from every root (first {lost[:5]})")
    # Births: an earlier packet whose star holds the child entry (the Lean `birthOK`; the
    # rebuild pins the stricter exporter rule "first incoming entry"). By induction on the id
    # this alone implies reachability; the search above is the direct form of that condition.
    for p in t.packets:
        i, birth = p["id"], p["birth"]
        if p["factor_edge"] == -1:
            if birth is not None:
                fail(f"packet {i}: a root has a birth")
            continue
        if birth is None or len(birth) != 3:
            fail(f"packet {i}: a non-root packet has no birth")
            continue
        j, d, e = birth
        if not 0 <= j < i or ["child", d, e, i] not in t.stars[j]["entries"]:
            fail(f"packet {i}: birth {birth} is not an earlier packet's star entry")


def _layer_l7(t, fail):
    # All or none: no hub rows (an export without `--hub-rows`), or exactly one per
    # noncoincident state and hub letter, in order (the Lean checker checks the listed rows).
    noncoincident = [s for s, (u, v) in enumerate(t.states) if u != v]
    want = [(s, hub) for s in noncoincident for hub in range(3)] if t.hubs else []
    if [(r["state"], r["hub"]) for r in t.hubs] != want:
        fail("hub rows are neither absent nor one per noncoincident state and hub, in order")
    for r in t.hubs:
        s, hub = r["state"], r["hub"]
        if not 0 <= s < len(t.states) or hub not in (0, 1, 2):
            fail("hub row outside the states or letters")
            continue
        fids = [f["id"] for f in t.factors if f["parent"] == s]
        bits = [hub_bit(t.states[s], t.states[t.factors[f]["child"]],
                        t.factors[f]["orientation"], hub) for f in fids]
        if r["factors"] != fids or r["bits"] != bits:
            fail(f"hub row ({s}, {hub}): bits differ from the literal hub bits (null = undefined)")


CHECKS = dict(zip(LAYERS, (_layer_l0, _layer_l1, _layer_l2, _layer_l3, _layer_l4, _layer_l5,
                           _layer_l6, _layer_l7)))


def audit(rows):
    """Every failure of every layer, as {layer: [reasons]}; an empty dict accepts.

    Rows that cannot be read as a table (not a list of objects, a missing field, an
    unreadable sigma) refuse at L0 with their JSON-shape failures; no later layer runs.
    """
    try:
        t = Table(rows)
    except InvalidPacketSquare as e:
        shape = shape_failures(rows)
        return {"L0": shape + [e.reason] if shape else [e.reason]}
    failures = defaultdict(list)
    for layer, check in CHECKS.items():
        def fail(reason, layer=layer):
            failures[layer].append(reason)
        try:
            check(t, fail)
        except (InvalidPacketSquare, KeyError, IndexError, TypeError, ValueError,
                AttributeError) as e:
            fail(f"malformed table: {e!r}")
    return dict(failures)


def verify(rows):
    """Accept a table or raise at its first failing layer; returns the header counts."""
    failures = audit(rows)
    for layer in LAYERS:
        if layer in failures:
            reasons = failures[layer]
            more = f" (and {len(reasons) - 3} more)" if len(reasons) > 3 else ""
            raise InvalidPacketSquare(layer, "; ".join(reasons[:3]) + more)
    h = Table(rows).header
    return {k: h[k] for k in ("states", "factors", "packets", "edges", "split_descendants",
                              "roots", "hub_rows")}


# ---------------------------------------------------------------------------
# Item 3: the residual transport law and the split account
# ---------------------------------------------------------------------------


@fail_closed("L4")
def transport_law(rows, matrix=None, forcing=True):
    """Check r' = M r + lambda on every child entry, from the listed words of both rows.

    Returns (children checked, splits checked, violations). `r` is the prefix defect of the
    source row's oriented state at its positions and `r'` that of the destination row, each
    computed from its own listed words; `lambda` is the prefix defect of the two digits.
    The asynchronous form (measured from cut 0 of the inflated source) is checked on every
    digit pair, splits included. `matrix` / `forcing=False` are negative-control variants.
    """
    t = Table(rows)
    require(len(t.stars) == len(t.packets) > 0, "L5", "one star row per packet")
    m = incidence(t.sigma) if matrix is None else matrix
    children = splits = 0
    violations = []
    for p, star in zip(t.packets, t.stars):
        state = t.states[p["state"]]
        if not star["expanded"]:
            continue
        block = orient(state, p["orientation"])
        P, Q = p["occurrences"]
        r = defect(block[0], block[1], P, Q)
        require(list(r) == p["residual"], "L4", f"packet {p['id']}: residual field")
        TT, BB, _ = literal_star(t.sigma, block, P, Q)
        a, b = block[0][P], block[1][Q]
        st, sb = image_starts(t.sigma, block[0]), image_starts(t.sigma, block[1])
        for entry in star["entries"]:
            d, e = entry[1], entry[2]
            lam = defect(t.sigma[a], t.sigma[b], d, e) if forcing else (0, 0, 0)
            predicted = add(act(m, r), lam)
            if defect(TT, BB, st[P] + d, sb[Q] + e) != predicted:
                violations.append(("asynchronous", p["id"], d, e))
            if entry[0] == "split":
                splits += 1
                continue
            q = t.packets[entry[3]]
            child = orient(t.states[q["state"]], q["orientation"])
            r2 = defect(child[0], child[1], *q["occurrences"])
            require(list(r2) == q["residual"], "L4", f"packet {q['id']}: residual field")
            if r2 != predicted:
                violations.append(("child", p["id"], d, e, q["id"]))
            children += 1
    return children, splits, violations


@fail_closed("L5")
def split_account(rows):
    """Per expandable packet: |sigma(a)| * |sigma(b)| entries, row-major, children + splits."""
    t = Table(rows)
    require(len(t.stars) == len(t.packets) > 0, "L5", "one star row per packet")
    children = splits = product = 0
    for p, star in zip(t.packets, t.stars):
        state = t.states[p["state"]]
        if not star["expanded"]:
            require(state[0] == state[1] or p["success"], "L5",
                    f"packet {p['id']}: unexpanded noncoincident packet")
            require(star["entries"] == [], "L5", f"packet {p['id']}: entries at a terminal")
            continue
        a, b = p["target_letters"]
        pairs = [(d, e) for d in range(len(t.sigma[a])) for e in range(len(t.sigma[b]))]
        require([(x[1], x[2]) for x in star["entries"]] == pairs, "L5",
                f"packet {p['id']}: entries are not every digit pair once, row-major")
        blocks = len(factorisation(t.sigma, orient(state, p["orientation"]))[2]) - 1
        for x in star["entries"]:
            if x[0] == "split":
                require(len(x) == 5 and x[3] != x[4] and 0 <= x[3] < blocks and 0 <= x[4] < blocks,
                        "L5", f"packet {p['id']}: split ordinals")
                splits += 1
            else:
                require(len(x) == 4 and 0 <= x[3] < len(t.packets), "L5",
                        f"packet {p['id']}: child destination")
                children += 1
        product += len(pairs)
    require(children == t.header["edges"] and splits == t.header["split_descendants"]
            and product == children + splits, "L5", "split account does not add up")
    return {"children": children, "splits": splits, "digit_pairs": product}


# ---------------------------------------------------------------------------
# Item 4 (archive): v1 rows against the archived target-aware-bpa-v1 dumps
# ---------------------------------------------------------------------------


@fail_closed("L0")
def compare_with_archive(rows, archive_rows):
    """The v1 rows agree with the archived dump; returns the number of edges compared."""
    t = Table(rows)
    old = defaultdict(list)
    for row in archive_rows:
        old[row["record"]].append(row)
    h = old["header"][0]
    require(h["schema"] == "target-aware-bpa-v1" and h["sigma"] == t.header["sigma"], "L0",
            "archive schema or sigma")
    require((h["packets"], h["edges"], h["split_descendants"]) == (
        t.header["packets"], t.header["edges"], t.header["split_descendants"]), "L0",
        "archive counts")
    require([(tuple(r["top"]), tuple(r["bottom"])) for r in old["state"]] == t.states, "L2",
            "archive states")
    fields = ("id", "parent", "ordinal", "child", "orientation", "span")
    require([[r[f] for f in fields] for r in old["factor"]]
            == [[r[f] for f in fields] for r in t.factors], "L3", "archive factors")
    require(len(old["packet"]) == len(t.packets), "L4", "archive packet count")
    for a, p in zip(old["packet"], t.packets):
        same = ("id", "state", "orientation", "occurrences", "factor_edge", "target_letters",
                "residual", "interior", "success")
        require(all(a[f] == p[f] for f in same), "L4", f"archive packet {p['id']}")
        if p["factor_edge"] == -1:
            P, Q = p["occurrences"]
            require((a["top_address"], a["bottom_address"], p["top_address"], p["bottom_address"])
                    == ([P, -1, P, P], [Q, -1, Q, Q], None, None), "L4",
                    f"archive root address {p['id']}")
        else:
            require((a["top_address"], a["bottom_address"]) == (p["top_address"],
                                                                   p["bottom_address"]),
                    "L4", f"archive address {p['id']}")
    entries = []
    for star in t.stars:
        p = t.packets[star["packet"]]
        a, b = p["target_letters"]
        for x in star["entries"]:
            if x[0] == "child":
                lam = list(defect(t.sigma[a], t.sigma[b], x[1], x[2]))
                entries.append((star["packet"], x[3], [x[1], x[2]], lam))
    archived = [(e["source"], e["destination"], e["digits"], e["lambda"])
                for e in sorted(old["edge"], key=lambda e: e["id"])]
    require(archived == entries, "L5", "archive edges differ from the v1 child entries")
    first = {}
    for source, destination, digits, _ in archived:
        first.setdefault(destination, [source, *digits])
    for p in t.packets:
        require(p["birth"] == first.get(p["id"]), "L6",
                f"packet {p['id']}: birth is not the archive's first incoming edge")
    return len(entries)


# ---------------------------------------------------------------------------
# Item 5: bounded absolute replay in the iterates of the seeds
# ---------------------------------------------------------------------------


def _prefix_parikh(word):
    out, c = [(0, 0, 0)], [0, 0, 0]
    for a in word:
        c[a] += 1
        out.append(tuple(c))
    return out


# The fields of a packet row that an absolute pair determines (not `id`, not `birth`).
REPLAY_FIELDS = ("state", "orientation", "occurrences", "factor_edge", "top_address",
                 "bottom_address", "target_letters", "residual", "interior", "success")


def _fields(p):
    return {f: p[f] for f in REPLAY_FIELDS}


def frame_readings(t, U, V, max_level):
    """Readings of the retained pairs of the frame `(U, V)`, levels `0..max_level`.

    Computed from the absolute words of the frame alone: no packet or star row is read. The
    factor rows supply only the id and orientation of the factor `(parent state, ordinal)`.
    A level-0 pair reads as a root in the frame's orientation (`-1` when `(U, V)` is not
    normalised); a retained pair `(P2, Q2)` at level `n + 1` of a pair `(P, Q)` in block
    `[lo, hi)` reads in the block `k` of the level-`n + 1` factorisation holding both
    positions, with the parent's orientation times the factor orientation, local positions,
    addresses `[P - lo, d, P2 - start(lo), P2 - lo2]` (and likewise below), the absolute
    prefix defect as residual, and the interior and success bits of that block. A pair whose
    block is a coincidence (or a success) is terminal.
    """
    sigma = t.sigma
    index = {s: i for i, s in enumerate(t.states)}
    factor_of = {(f["parent"], f["ordinal"]): f for f in t.factors}
    pu, pv = _prefix_parikh(U), _prefix_parikh(V)
    norm = normalise((U, V))
    require(norm in index, "L2", f"frame {(U, V)}: the seed is not a listed state")
    live = {(P, Q): ({"state": index[norm], "orientation": 1 if (U, V) == norm else -1,
                      "occurrences": [P, Q], "factor_edge": -1, "top_address": None,
                      "bottom_address": None, "target_letters": [U[P], V[Q]],
                      "residual": [x - y for x, y in zip(pu[P], pv[Q])], "interior": False,
                      "success": False}, 0, len(U))
            for P in range(len(U)) for Q in range(len(V))}
    levels = []
    for level in range(max_level + 1):
        levels.append({pq: r for pq, (r, _, _) in live.items()})
        if level == max_level:
            break
        U2, V2 = inflate(sigma, U), inflate(sigma, V)
        su, sv = image_starts(sigma, U), image_starts(sigma, V)
        cuts2 = balanced_cuts(U2, V2)
        require(cuts2[-1] == len(U2), "L2", "an iterate of a seed is not balanced")
        owner = {}
        for k in range(len(cuts2) - 1):
            for x in range(cuts2[k], cuts2[k + 1]):
                owner[x] = k
        pu, pv = _prefix_parikh(U2), _prefix_parikh(V2)
        new = {}
        for (P, Q), (r, lo, hi) in live.items():
            if r["success"] or U[lo:hi] == V[lo:hi]:
                continue
            k0 = owner[su[lo]]
            for d in range(len(sigma[U[P]])):
                for e in range(len(sigma[V[Q]])):
                    P2, Q2 = su[P] + d, sv[Q] + e
                    if owner[P2] != owner[Q2]:
                        continue
                    lo2, hi2 = cuts2[owner[P2]], cuts2[owner[P2] + 1]
                    raw = (U2[lo2:hi2], V2[lo2:hi2])
                    f = factor_of[r["state"], owner[P2] - k0]
                    sign = r["orientation"] * f["orientation"]
                    require(orient(normalise(raw), sign) == raw, "L3",
                            "a factor orientation disagrees with the absolute words")
                    interior = P2 == Q2 == lo2 and lo2 > su[lo]
                    new[P2, Q2] = ({
                        "state": index[normalise(raw)], "orientation": sign,
                        "occurrences": [P2 - lo2, Q2 - lo2], "factor_edge": f["id"],
                        "top_address": [P - lo, d, P2 - su[lo], P2 - lo2],
                        "bottom_address": [Q - lo, e, Q2 - sv[lo], Q2 - lo2],
                        "target_letters": [U2[P2], V2[Q2]],
                        "residual": [x - y for x, y in zip(pu[P2], pv[Q2])],
                        "interior": interior,
                        "success": interior and raw[0] == raw[1] and (
                            t.target is None or raw[0][0] == t.target)}, lo2, hi2)
        U, V, live = U2, V2, new
    return levels


@fail_closed("L5")
def absolute_replay(rows, max_level):
    """Follow every retained absolute pair of every seed, and of its swap, up to `max_level`.

    Level 0: the four position pairs of a normalised swap seed `T0 = (ab, ba)`, read as its
    root packets. A pair `(P, Q)` at level `n`, read as packet `p` with block span `[lo, hi)`,
    produces at level `n + 1` the pairs `(start(P) + d, start(Q) + e)` in
    `(sigma(U), sigma(V))`; a pair is retained when both lie in one block of the level
    `n + 1` factorisation of `(sigma^(n+1)(ab), sigma^(n+1)(ba))`. Checked for every
    retained pair: the block is a listed state in the packet's orientation; the packet's
    state, orientation, positions, factor, addresses, letters, interior and success fields
    are those of the absolute words, and its residual equals the absolute prefix defect
    `Parikh(U[:P]) - Parikh(V[:Q])`; the packet's star entry for every digit pair is the
    absolute outcome. The `birth` field is not compared: it names the table's first incoming
    entry, which need not be the parent of this pair. Also checked per level (by counting,
    each retained pair lying in one block): the retained pairs are exactly the pairs inside
    the noncoincident blocks together with the single pair of every coincidence block whose
    parent block is noncoincident. Pairs inside a coincidence block that descends from an
    earlier coincidence are *not* retained: coincidence packets are terminal. The packets
    read up to `max_level` are exactly those within `max_level` child steps of the seed root
    packets.

    The same readings are recomputed from the absolute words alone (`frame_readings`, no packet
    or star row read) and must agree. The swapped frame `(ba, ab)` is then replayed from its
    words alone: its iterates are `(sigma^n(ba), sigma^n(ab))`, the side swap of the
    normalised ones, with the same cuts, so its reading of `(Q, P)` must be `_mirror` of the
    normalised reading of `(P, Q)` (the fields above; orientation negated, positions,
    addresses and letters exchanged, residual negated). The table lists roots in orientation
    `+1` only, so the mirrored root readings are never listed packets and the others need
    not be; how many distinct mirrored readings are listed is returned
    (`swap_readings_listed`, of `swap_readings`), as an observation.
    """
    require(type(max_level) is int and 0 <= max_level <= 12, "L0", "level bound in 0..12")
    t = Table(rows)
    sigma = t.sigma
    index = {s: i for i, s in enumerate(t.states)}
    ids = {packet_key(p): p["id"] for p in t.packets}
    factor_of = {(f["parent"], f["ordinal"]): f for f in t.factors}
    hit, per_level = set(), [0] * (max_level + 1)
    swap_keys = set()
    for a in range(3):
        for b in range(a + 1, 3):
            U, V = (a, b), (b, a)
            s0 = index[(U, V)]
            live = {(P, Q): (ids[(s0, 1, P, Q, -1)], 0, 2) for P in range(2) for Q in range(2)}
            normal = []
            inherited = 0  # coincidence blocks inside the inflation of an earlier coincidence
            for level in range(max_level + 1):
                pu, pv = _prefix_parikh(U), _prefix_parikh(V)
                cuts = balanced_cuts(U, V)
                require(cuts[-1] == len(U), "L2", "an iterate of a seed is not balanced")
                spans = list(zip(cuts, cuts[1:]))
                inside = sum((hi - lo) ** 2 for lo, hi in spans if U[lo:hi] != V[lo:hi])
                coincidences = [lo for lo, hi in spans if U[lo:hi] == V[lo:hi]]
                live_nc = sum(U[lo:hi] != V[lo:hi] for _, lo, hi in live.values())
                require(live_nc == inside and len(live) - live_nc == len(coincidences) - inherited,
                        "L5", f"seed {(a, b)} level {level}: {live_nc} + {len(live) - live_nc} "
                        f"retained pairs, {inside} pairs inside noncoincident blocks and "
                        f"{len(coincidences) - inherited} coincidence blocks with a "
                        f"noncoincident parent")
                inherited = sum(len(sigma[U[lo]]) for lo in coincidences)
                per_level[level] += len(live)
                normal.append({pq: _fields(t.packets[pid]) for pq, (pid, _, _) in live.items()})
                cut_set = set(cuts)
                for (P, Q), (pid, lo, hi) in live.items():
                    p = t.packets[pid]
                    hit.add(pid)
                    block = orient(t.states[p["state"]], p["orientation"])
                    require((U[lo:hi], V[lo:hi]) == block and lo in cut_set and hi in cut_set,
                            "L4",
                            f"packet {pid}: its block is not the absolute block")
                    require(p["occurrences"] == [P - lo, Q - lo]
                            and p["target_letters"] == [U[P], V[Q]], "L4",
                            f"packet {pid}: positions or letters differ from the absolute pair")
                    require(p["residual"] == [x - y for x, y in zip(pu[P], pv[Q])], "L4",
                            f"packet {pid}: residual is not the absolute prefix defect")
                if level == max_level:
                    break
                U2, V2 = inflate(sigma, U), inflate(sigma, V)
                su, sv = image_starts(sigma, U), image_starts(sigma, V)
                cuts2 = balanced_cuts(U2, V2)
                owner = {}
                for k in range(len(cuts2) - 1):
                    for x in range(cuts2[k], cuts2[k + 1]):
                        owner[x] = k
                new = {}
                for (P, Q), (pid, lo, hi) in live.items():
                    p = t.packets[pid]
                    star = t.stars[pid]
                    if not star["expanded"]:
                        continue
                    k0 = owner[su[lo]]
                    entries = {(x[1], x[2]): x for x in star["entries"]}
                    for d in range(len(sigma[U[P]])):
                        for e in range(len(sigma[V[Q]])):
                            P2, Q2 = su[P] + d, sv[Q] + e
                            kt, kb = owner[P2], owner[Q2]
                            x = entries.get((d, e))
                            if kt != kb:
                                require(x == ["split", d, e, kt - k0, kb - k0], "L5",
                                        f"packet {pid}: absolute split ({d}, {e})")
                                continue
                            lo2, hi2 = cuts2[kt], cuts2[kt + 1]
                            raw = (U2[lo2:hi2], V2[lo2:hi2])
                            f = factor_of[p["state"], kt - k0]
                            key = (index[normalise(raw)], p["orientation"] * f["orientation"],
                                   P2 - lo2, Q2 - lo2, f["id"])
                            require(key in ids and x == ["child", d, e, ids[key]], "L5",
                                    f"packet {pid}: absolute child ({d}, {e}) is not its "
                                    "star entry")
                            q = t.packets[ids[key]]
                            require(q["top_address"] == [P - lo, d, P2 - su[lo], P2 - lo2]
                                    and q["bottom_address"] == [Q - lo, e, Q2 - sv[lo], Q2 - lo2],
                                    "L4", f"packet {q['id']}: absolute addresses")
                            interior = P2 == Q2 == lo2 and lo2 > su[lo]
                            success = interior and raw[0] == raw[1] and (
                                t.target is None or raw[0][0] == t.target)
                            require(q["interior"] is interior and q["success"] is success, "L4",
                                    f"packet {q['id']}: absolute interior/success")
                            new[P2, Q2] = (ids[key], lo2, hi2)
                U, V, live = U2, V2, new
            # The same readings from the absolute words alone, and the swapped frame.
            require(frame_readings(t, (a, b), (b, a), max_level) == normal, "L4",
                    f"seed {(a, b)}: the word-only readings differ from the listed rows")
            swapped = frame_readings(t, (b, a), (a, b), max_level)
            for level, readings in enumerate(normal):
                mirrored = {(Q, P): _fields(_mirror(r, None)) for (P, Q), r in readings.items()}
                require(swapped[level] == mirrored, "L4",
                        f"seed {(a, b)} level {level}: the swapped frame does not read the "
                        "mirrors of the normalised readings")
                swap_keys |= {(r["state"], r["orientation"], *r["occurrences"], r["factor_edge"])
                              for r in swapped[level].values()}
    # The packets read by retained pairs up to `max_level` are exactly the packets within
    # `max_level` child steps of the seed roots: every packet edge out of a read packet is
    # realised by an absolute pair, and nothing else is read.
    seeds = {index[((a, b), (b, a))] for a in range(3) for b in range(a + 1, 3)}
    near = {p["id"] for p in t.packets if p["factor_edge"] == -1 and p["state"] in seeds}
    frontier = set(near)
    for _ in range(max_level):
        frontier = {e[3] for i in frontier for e in t.stars[i]["entries"] if e[0] == "child"} - near
        near |= frontier
    require(hit == near, "L5", "absolute readings differ from the packets near the seed roots")
    return {"pairs_per_level": per_level, "packets_hit": len(hit),
            "non_root_packets_hit": sum(t.packets[i]["factor_edge"] != -1 for i in hit),
            "swap_readings": len(swap_keys),
            "swap_readings_listed": sum(k in ids for k in swap_keys)}


# ---------------------------------------------------------------------------
# Item 6: the committed Lean data modules against the JSONL
# ---------------------------------------------------------------------------

_TOKEN = re.compile(r"\s*(?:(!\[|[\[\]()⟨⟩,])|(-?\d+)|(\.?[A-Za-z_][A-Za-z_0-9]*))")


class _Anon(tuple):
    """An anonymous constructor `⟨...⟩`."""


def _tokens(text):
    pos, out = 0, []
    text = text.rstrip()
    while pos < len(text):
        m = _TOKEN.match(text, pos)
        require(m is not None and m.end() > pos, "L0",
                f"Lean literal: cannot read {text[pos:pos + 20]!r}")
        punct, number, word = m.groups()
        out.append(("p", punct) if punct else ("n", int(number)) if number else ("w", word))
        pos = m.end()
    return out


def _parse_expr(tokens, i):
    kind, value = tokens[i]
    if kind == "n":
        return value, i + 1
    if kind == "w":
        if value in ("true", "false"):
            return value == "true", i + 1
        if value == "none":
            return None, i + 1
        if value == "some":
            inner, j = _parse_expr(tokens, i + 1)
            return ("some", inner), j
        if value in (".child", ".split"):
            arity = 3 if value == ".child" else 4
            args = [tokens[i + 1 + k] for k in range(arity)]
            require(all(k == "n" for k, _ in args), "L0", f"Lean literal: {value} arguments")
            return (value[1:], *[v for _, v in args]), i + 1 + arity
        raise InvalidPacketSquare("L0", f"Lean literal: unexpected identifier {value!r}")
    close = {"[": "]", "![": "]", "(": ")", "⟨": "⟩"}.get(value)
    require(close is not None, "L0", f"Lean literal: unexpected {value!r}")
    items, i = [], i + 1
    if tokens[i] != ("p", close):
        while True:
            item, i = _parse_expr(tokens, i)
            items.append(item)
            if tokens[i] == ("p", ","):
                i += 1
                continue
            require(tokens[i] == ("p", close), "L0", f"Lean literal: expected {close!r}")
            break
    i += 1
    if value == "⟨":
        return _Anon(items), i
    if value == "(":
        return (items[0] if len(items) == 1 else tuple(items)), i
    return items, i


@fail_closed("L0")
def parse_lean_literal(text):
    tokens = _tokens(text)
    value, i = _parse_expr(tokens, 0)
    require(i == len(tokens), "L0", "Lean literal: trailing tokens")
    return value


def lean_module_path(name, layout, root=None):
    """The data module of fixture `name`: `nested` (PacketSquareData/X) or `flat`."""
    suffix = FIXTURES[name][1]
    module = f"PscVerif.PacketSquareData.{suffix}" if layout == "nested" else \
        f"PscVerif.PacketSquareData{suffix}"
    return module, Path(LEAN_ROOT if root is None else root) / (module.replace(".", "/") + ".lean")


def find_lean_module(name, root=None):
    """(module, path) of the committed data module, None if absent; refuses two layouts."""
    found = [lean_module_path(name, layout, root) for layout in ("nested", "flat")]
    found = [(m, p) for m, p in found if p.is_file()]
    require(len(found) <= 1, "L0", f"{name}: data module present in both layouts")
    return found[0] if found else None


_FIELDS = ("letters", "s", "target", "states", "factors", "packets", "stars", "keyOrder", "hubs")


@fail_closed("L0")
def parse_lean_module(text, module):
    """The fields of `def table : Table (Fin 3) where ...`, and the module's framing."""
    for word in ("sorry", "admit", "native_decide", "axiom", "private"):
        require(re.search(rf"\b{word}\b", text) is None, "L0", f"Lean module contains {word}")
    require(text.count(f"namespace {module}\n") == 1 and text.count(f"end {module}\n") == 1
            and text.count("import PscVerif.PacketCertificate\n") == 1, "L0",
            "Lean module framing (namespace, end, import)")
    theorems = re.findall(r"^theorem .*$", text, flags=re.M)
    require(theorems == ["theorem accepted : table.check = true := by decide +kernel"], "L0",
            f"Lean module theorems {theorems}")
    head = "def table : Table (Fin 3) where\n"
    require(text.count(head) == 1, "L0", "Lean module has no single table definition")
    body = text.split(head, 1)[1].split("\n\n", 1)[0]
    body = re.sub(r"--[^\n]*", "", body)
    parts = re.split(r"^  ([A-Za-z]+) := ", body, flags=re.M)
    require(parts[0].strip() == "" and len(parts) == 2 * len(_FIELDS) + 1, "L0",
            "Lean table fields")
    names = parts[1::2]
    require(tuple(names) == _FIELDS, "L0", f"Lean table fields {names}")
    table = {n: parse_lean_literal(v) for n, v in zip(names, parts[2::2])}
    comment = text.split("-/", 1)[0]
    table["_rows_line"] = re.search(r"^Rows: (.*)$", comment, flags=re.M).group(1)
    table["_pip_line"] = re.search(r"^PIP: (\w+) ", comment, flags=re.M).group(1)
    table["_command"] = re.search(r"^Command: (.*)$", comment, flags=re.M).group(1)
    return table


def _some(x):
    if x is None:
        return None
    require(isinstance(x, tuple) and len(x) == 2 and x[0] == "some", "L0", f"Lean option {x!r}")
    return x[1]


@fail_closed("L0")
def compare_lean_module(table, rows, name, module):
    """Every Lean field equals its JSONL row; returns the number of compared packet rows."""
    t = Table(rows)
    h = t.header
    sigma = FIXTURES[name][0]
    require(table["letters"] == [0, 1, 2] and table["s"] == h["sigma"], "L0", "Lean letters/s")
    require(_some(table["target"]) == h["target"] if table["target"] is not None
            else h["target"] is None, "L0", "Lean target")
    require(table["states"] == [(list(u), list(v)) for u, v in t.states], "L2", "Lean states")
    require(table["factors"] == [
        _Anon([f["parent"], f["ordinal"], f["child"], f["orientation"] == 1, *f["span"]])
        for f in t.factors], "L3", "Lean factor rows")
    require(len(table["packets"]) == len(t.packets) > 0, "L4", "Lean packet count")
    for lean, p in zip(table["packets"], t.packets):
        require(isinstance(lean, _Anon) and len(lean) == 12, "L4", "Lean packet row shape")
        (state, sign, top, bot, factor, ta, ba, letters, residual, interior, success,
         birth) = lean
        tup = (lambda x: None if x is None else list(_some(x)))
        require([state, sign, top, bot] == [p["state"], p["orientation"] == 1,
                                            *p["occurrences"]]
                and (-1 if factor is None else _some(factor)) == p["factor_edge"]
                and tup(ta) == p["top_address"] and tup(ba) == p["bottom_address"]
                and list(letters) == p["target_letters"] and residual == p["residual"]
                and (interior, success) == (p["interior"], p["success"])
                and tup(birth) == p["birth"], "L4", f"Lean packet row {p['id']}")
    require(len(table["stars"]) == len(t.stars), "L5", "Lean star count")
    for lean, star in zip(table["stars"], t.stars):
        require([list(x) for x in lean] == star["entries"], "L5",
                f"Lean star of packet {star['packet']}")
    require(table["keyOrder"] == t.key_order, "L6", "Lean key order")
    bit = {None: None, ("some", True): 1, ("some", False): 0}
    require(len(table["hubs"]) == len(t.hubs), "L7", "Lean hub row count")
    for lean, r in zip(table["hubs"], t.hubs):
        require(list(lean[:2]) == [r["state"], r["hub"]]
                and [bit[b] for b in lean[2]] == r["bits"], "L7",
                f"Lean hub row ({r['state']}, {r['hub']})")
    rows_line = (f"{h['states']} states, {h['factors']} factors, {h['packets']} packets, "
                 f"{h['edges']} edges, {h['split_descendants']} split descendants, "
                 f"{h['roots']} roots, {h['hub_rows']} hub rows.")
    require(table["_rows_line"] == rows_line, "L0", "Lean module Rows line")
    require(table["_pip_line"] == ("true" if h["pip"] else "false"), "L0", "Lean module PIP line")
    command = table["_command"]
    require(f"--sigma {sigma} " in command and f"--module {module} " in command + " "
            and "--target any" in command and command.endswith("--hub-rows"), "L0",
            "Lean module Command line")
    return len(t.packets)


def _lean_list(xs):
    return "[" + ", ".join(map(str, xs)) + "]"


def _lean_tuple(xs):
    return "(" + ", ".join(map(str, xs)) + ")"


def _lean_bool(b):
    require(type(b) is bool, "L0", f"Lean template: {b!r} is not a boolean")
    return "true" if b else "false"


def _lean_some(x, render):
    return "none" if x is None else "some " + render(x)


def _lean_block(name, items):
    """`  name := [` then one item per line, closed on the last item; `[]` when empty."""
    if not items:
        return [f"  {name} := []"]
    return [f"  {name} := ["] + [f"    {x}" + ("," if k + 1 < len(items) else "]")
                                  for k, x in enumerate(items)]


def lean_template(rows, module):
    """(prefix, suffix) of the data module of `rows`: the module text is `prefix + free +
    suffix`, where `free` is the paragraph of the module docstring after its title line.

    Rendered here from the JSONL rows, independently of the Mojo emitter, in the layout of
    the committed modules: the leading comment (provenance, Command, Rows, PIP), the import,
    the docstring title, the namespace, `open`, the two declaration docstrings, every line of
    the table body (its two `--` comment lines included), the theorem and `end`.
    """
    t = Table(rows)
    h, b = t.header, t.budget
    sigma = sigma_text(t.sigma)
    target = "any" if t.target is None else str(t.target)
    hub_flag = " --hub-rows" if t.hubs else ""
    command = (f"cd kernel && pixi run --locked mojo run -I . packet_square_export.mojo "
               f"--sigma {sigma} --target {target} --state-cap {b['bpa_states']} "
               f"--length-cap {b['bpa_length']} --packet-cap {b['packets']} "
               f"--edge-cap {b['edges']} --format lean --module {module}{hub_flag}")
    head = [
        "/-",
        "Generated by kernel/psc/packet_square_export.mojo (schema packet-square-v1). "
        "Do not edit:",
        "kernel/check_packet_square.sh regenerates this file and compares the bytes.",
        f"Command: {command}",
        f"Rows: {h['states']} states, {h['factors']} factors, {h['packets']} packets, "
        f"{h['edges']} edges, {h['split_descendants']} split descendants, {h['roots']} roots, "
        f"{h['hub_rows']} hub rows.",
        f"PIP: {_lean_bool(h['pip'])} (recorded by the exporter; the checker does not read it).",
        "-/",
        "import PscVerif.PacketCertificate",
        "",
        "/-!",
        f"# packet-square-v1 data: `{sigma}`, target {target}",
    ]
    body = [
        "  letters := " + _lean_list(h["letters"]),
        "  s := ![" + ", ".join(_lean_list(w) for w in t.sigma) + "]",
        "  target := " + _lean_some(t.target, str),
    ]
    body += _lean_block("states", [f"({_lean_list(u)}, {_lean_list(v)})" for u, v in t.states])
    body.append("  -- factor rows: parent, ordinal, child, sign, start, stop, total")
    body += _lean_block("factors", [
        f"⟨{f['parent']}, {f['ordinal']}, {f['child']}, {_lean_bool(f['orientation'] == 1)}, "
        + ", ".join(map(str, f["span"])) + "⟩" for f in t.factors])
    body.append("  -- packet rows: state, sign, top, bot, factor, topAddr, botAddr, letters, "
                "residual, interior,")
    body.append("  -- success, birth")
    def factor(p):
        return _lean_some(None if p["factor_edge"] == -1 else p["factor_edge"], str)

    body += _lean_block("packets", [
        f"⟨{p['state']}, {_lean_bool(p['orientation'] == 1)}, {p['occurrences'][0]}, "
        f"{p['occurrences'][1]}, {factor(p)}, {_lean_some(p['top_address'], _lean_tuple)}, "
        f"{_lean_some(p['bottom_address'], _lean_tuple)}, {_lean_tuple(p['target_letters'])}, "
        f"{_lean_list(p['residual'])}, {_lean_bool(p['interior'])}, {_lean_bool(p['success'])}, "
        f"{_lean_some(p['birth'], _lean_tuple)}⟩" for p in t.packets])
    body += _lean_block("stars", ["[" + ", ".join(f".{e[0]} " + " ".join(map(str, e[1:]))
                                                 for e in s["entries"]) + "]"
                                  for s in t.stars])
    order = t.key_order
    body += _lean_block("keyOrder", [", ".join(map(str, order[k:k + 20]))
                                     for k in range(0, len(order), 20)])
    bit = {None: "none", 0: "some false", 1: "some true"}
    body += _lean_block("hubs", [f"⟨{r['state']}, {r['hub']}, ["
                                 + ", ".join(bit[x] for x in r["bits"]) + "]⟩" for r in t.hubs])
    tail = [
        "-/",
        "",
        f"namespace {module}",
        "",
        "open Psc.PacketCertificate",
        "",
        f"/-- The exported packet-square-v1 rows of `{sigma}`, target {target}. -/",
        "def table : Table (Fin 3) where",
        *body,
        "",
        "/-- The v1 checker accepts the exported table (one kernel evaluation). -/",
        "theorem accepted : table.check = true := by decide +kernel",
        "",
        f"end {module}",
    ]
    return "\n".join(head) + "\n", "\n".join(tail) + "\n"


@fail_closed("L0")
def check_lean_template(text, rows, name, module):
    """The module text is the template of its JSONL rows with a free docstring paragraph.

    Every line outside that paragraph must equal the template (`lean_template`), so an extra
    declaration, option, instance, import, `open` or comment, or any changed field, is
    refused. The paragraph may hold any lines without a comment delimiter (`/-`, `-/`), so it
    cannot end the docstring early or open a nested comment; its prose is not compared here
    (the byte comparison with the emitter is `kernel/check_packet_square.sh`). Returns the
    number of free lines.
    """
    require(name in FIXTURES, "L0", f"unknown fixture {name!r}")
    prefix, suffix = lean_template(rows, module)
    require(text.startswith(prefix), "L0",
            f"{module}: the text before the docstring paragraph differs from the template")
    require(text.endswith(suffix) and len(text) >= len(prefix) + len(suffix), "L0",
            f"{module}: the text after the docstring paragraph differs from the template")
    free = text[len(prefix):len(text) - len(suffix)]
    require("/-" not in free and "-/" not in free and (free == "" or free.endswith("\n")),
            "L0", f"{module}: the docstring paragraph holds a comment delimiter")
    return free.count("\n")


# ---------------------------------------------------------------------------
# Negative-control generators (each returns new rows; the input is not changed)
# ---------------------------------------------------------------------------


def _copy(rows):
    return json.loads(json.dumps(rows))


def _with_counts(rows):
    """Refresh header and summary counts and the key order after a forgery."""
    t = Table(rows)
    children = sum(e[0] == "child" for s in t.stars for e in s["entries"])
    splits = sum(e[0] == "split" for s in t.stars for e in s["entries"])
    for row in (t.header, t.summary):
        row.update(packets=len(t.packets), edges=children, split_descendants=splits)
    t.by["key_order"][0]["packets"] = sorted(range(len(t.packets)),
                                             key=lambda i: key_tuple(t.packets[i]))
    return rows


def _mirror(p, new_id):
    """The same occurrence pair read in the other orientation."""
    return {**p, "id": new_id, "orientation": -p["orientation"],
            "occurrences": p["occurrences"][::-1], "top_address": p["bottom_address"],
            "bottom_address": p["top_address"], "target_letters": p["target_letters"][::-1],
            "residual": [-x for x in p["residual"]]}


def forged_mirror(rows, cycle):
    """Add the mirrors of the forward closure of `cycle` (a set of non-root packets).

    Every added row is a literal occurrence pair with its literal star, and the enlarged set
    is still closed under the literal transition (a fixed point), but no added row is
    reachable from a root. Header, summary and key order are made consistent.
    """
    rows = _copy(rows)
    t = Table(rows)
    stars = {s["packet"]: s for s in t.stars}
    closure, stack = set(cycle), list(cycle)
    while stack:
        for e in stars[stack.pop()]["entries"]:
            if e[0] == "child" and e[3] not in closure:
                closure.add(e[3])
                stack.append(e[3])
    require(all(t.packets[i]["factor_edge"] != -1 for i in closure), "L6", "closure has a root")
    ids = {packet_key(p): p["id"] for p in t.packets}
    image, added = {}, []
    for i in sorted(closure):
        m = _mirror(t.packets[i], len(t.packets) + len(added))
        if packet_key(m) in ids:
            image[i] = ids[packet_key(m)]
        else:
            image[i] = ids[packet_key(m)] = m["id"]
            added.append(m)
    new_stars = []
    for m in added:
        source = next(i for i in closure if image[i] == m["id"])
        entries = []
        for e in stars[source]["entries"]:
            if e[0] == "child":
                entries.append(["child", e[2], e[1], image[e[3]]])
            else:
                entries.append(["split", e[2], e[1], e[4], e[3]])
        entries.sort(key=lambda x: (x[1], x[2]))
        new_stars.append({"record": "star", "packet": m["id"],
                          "expanded": stars[source]["expanded"], "entries": entries})
    by_id = {m["id"]: m for m in added}
    for star in new_stars:
        for e in star["entries"]:
            target = by_id.get(e[3]) if e[0] == "child" else None
            if target is not None and target["birth"] is not None and target.get("_born") is None:
                target["birth"], target["_born"] = [star["packet"], e[1], e[2]], True
    for m in added:
        m.pop("_born", None)
    k = max(i for i, r in enumerate(rows) if r["record"] == "packet") + 1
    rows[k:k] = added
    k = max(i for i, r in enumerate(rows) if r["record"] == "star") + 1
    rows[k:k] = new_stars
    return _with_counts(rows)


def _find(rows, record, field, value):
    return next(r for r in rows if r["record"] == record and r[field] == value)


def drop_split(rows, packet, entry):
    """Remove one split entry of a star; header and summary split counts follow."""
    rows = _copy(rows)
    star = _find(rows, "star", "packet", packet)
    require(star["entries"][entry][0] == "split", "L5", "not a split entry")
    del star["entries"][entry]
    return _with_counts(rows)


def side_swap(rows, packet):
    """Flip the orientation bit of one packet row, nothing else."""
    rows = _copy(rows)
    p = _find(rows, "packet", "id", packet)
    p["orientation"] = -p["orientation"]
    return rows


def wrong_factor_ordinal(rows, factor, ordinal):
    rows = _copy(rows)
    _find(rows, "factor", "id", factor)["ordinal"] = ordinal
    return rows


def swap_split_ordinals(rows, packet, entry):
    rows = _copy(rows)
    x = _find(rows, "star", "packet", packet)["entries"][entry]
    require(x[0] == "split", "L5", "not a split entry")
    x[3], x[4] = x[4], x[3]
    return rows


def late_birth(rows, packet):
    """Point a birth at a later packet whose star holds no entry for it."""
    rows = _copy(rows)
    p = _find(rows, "packet", "id", packet)
    p["birth"] = [packet + 1, *p["birth"][1:]]
    return rows


def coerce_hub_bit(rows):
    """Replace the first undefined (null) hub bit by 0."""
    rows = _copy(rows)
    for r in rows:
        if r["record"] == "hub" and None in r["bits"]:
            r["bits"][r["bits"].index(None)] = 0
            return rows
    raise InvalidPacketSquare("L7", "no undefined hub bit to coerce")


def wrong_global_position(rows, packet):
    rows = _copy(rows)
    p = _find(rows, "packet", "id", packet)
    p["top_address"][2] += 1
    return rows


# ---------------------------------------------------------------------------
# Command line: every check on the four committed fixtures
# ---------------------------------------------------------------------------


PASS_LINE = ("packet-square oracle: every check passed on the four committed fixtures and the "
             "four Lean data modules were compared (finite evidence; no claim moves)")


def run_all(levels=6, evidence=None, lean_root=None):
    """(lines, missing): one line per fixture, and the Lean data modules not found.

    Raises on the first refusal. A missing data module is not compared and is returned in
    `missing`; `main` never reports a pass while `missing` is not empty.
    """
    check_digests(evidence)
    lines, missing = [], []
    for name in FIXTURES:
        rows = load_rows(fixture_path(name, evidence))
        n = compare_rebuild(name, evidence)
        counts = verify(rows)
        children, splits, bad = transport_law(rows)
        require(not bad, "L4", f"{name}: transport law violated at {bad[:3]}")
        account = split_account(rows)
        archived = compare_with_archive(rows, load_rows(ARCHIVE / f"{name}.jsonl")) \
            if name in ARCHIVED else "not archived"
        replay = absolute_replay(rows, levels)
        found = find_lean_module(name, lean_root)
        if found is None:
            looked = [str(lean_module_path(name, layout, lean_root)[1])
                      for layout in ("nested", "flat")]
            missing.append(f"{lean_module_path(name, 'nested')[0]} (looked for {looked})")
            lean = "MISSING (not compared)"
        else:
            module, path = found
            text = path.read_text()
            table = parse_lean_module(text, module)
            free = check_lean_template(text, rows, name, module)
            lean = (f"{compare_lean_module(table, rows, name, module)} rows equal, template "
                    f"equal outside {free} free docstring lines")
        lines.append(
            f"{name} ({FIXTURES[name][0]}): rebuilt {n} rows, bytes equal; accepted {counts}; "
            f"transport law on {children} edges and {splits} splits; digit pairs "
            f"{account['digit_pairs']}; archive edges {archived}; absolute replay to level "
            f"{levels}: pairs {replay['pairs_per_level']}, packets hit {replay['packets_hit']}, "
            f"swapped frame mirrored ({replay['swap_readings_listed']} of "
            f"{replay['swap_readings']} mirrored readings listed); Lean module {lean}")
    return lines, missing


def main(argv=None):
    """Exit 0: every check passed and all four Lean data modules were compared. Exit 1: a
    refusal, an inconclusive budget, malformed input, or (without `--allow-missing-lean`) a
    missing Lean data module. Exit 2: `--allow-missing-lean` and a module missing while every
    other check passed (INCOMPLETE, never the pass line)."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--levels", type=int, default=6, help="absolute replay level bound")
    parser.add_argument("--evidence", type=Path, default=None,
                        help=f"directory of the four JSONL files and SHA256SUMS ({EVIDENCE})")
    parser.add_argument("--lean-root", type=Path, default=None,
                        help=f"Lean package root holding PscVerif/ ({LEAN_ROOT})")
    parser.add_argument("--allow-missing-lean", action="store_true",
                        help="before the data modules are committed: report a missing module "
                             "as INCOMPLETE (exit 2) instead of refusing (exit 1)")
    args = parser.parse_args(argv)
    try:
        lines, missing = run_all(args.levels, args.evidence, args.lean_root)
    except InvalidPacketSquare as e:
        print(f"REFUSED: {e}", file=sys.stderr)
        return 1
    except BudgetExhausted as e:
        print(f"INCONCLUSIVE: {e}", file=sys.stderr)
        return 1
    except Exception as e:  # fail closed: malformed input never ends in a pass
        print(f"REFUSED: malformed input or oracle failure: {type(e).__name__}: {e}",
              file=sys.stderr)
        return 1
    for line in lines:
        print(line)
    if missing and not args.allow_missing_lean:
        print("REFUSED: Lean data modules missing, not compared: " + "; ".join(missing)
              + " (before the modules are committed, run with --allow-missing-lean)",
              file=sys.stderr)
        return 1
    if missing:
        print("INCOMPLETE: Lean data modules not compared: " + "; ".join(missing)
              + "; every other check passed")
        return 2
    print(PASS_LINE)
    return 0


if __name__ == "__main__":
    sys.exit(main())

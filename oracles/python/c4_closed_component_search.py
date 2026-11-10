"""Independent oracle for the K_2 = 0 window search off the PIP corpus.

Canonical implementation: kernel/psc/closed_component_search.mojo with the
driver kernel/c4_closed_component_search.mojo
(docs/c4-closed-component-search-2026-11-07.md; gate
docs/c4-solidify-stop-go-2026-11-07.md, section 4.6). This stdlib script shares
no code with it and recomputes, by different methods:

1. the partition of the 59,319 substitutions on {0,1,2} with images of
   length 1..3: primitivity (Boolean matrix powers), irreducibility of
   chi_M (no integer root), the number of non-Perron roots outside the unit
   disc (Sturm chains over Fraction for three real roots; the sign of
   chi(|det M|) for one real root), and the endpoint flag (the first-letter
   or last-letter map is eventually constant, decided by composing the map
   with itself three times, not by its cycle type);
2. the list P_L of normalised (u_0 < v_0) irreducible pairs with K_1 = K_2 = 0
   and length at most L, by grouping all words of each length by the exact
   signature (Parikh vector, N_ab for all a, b) in a dictionary;
3. the greatest fixed point below P_L of X -> {T in X : children(T) <= X},
   where the children of (u, v) are the normalised blocks of the zero-return
   factorisation of (sigma(u), sigma(v)), computed on materialised words.

It reports, per specimen, the number of members of P_L whose every child is
a member (the first pass), the number of removal rounds and the number of
survivors, and compares them with the WINDOW_SPECIMEN lines of a Mojo log.
A failed check raises OracleFailure. Nothing here turns a window into a
verdict: an empty limit means "no K_2 = 0 strict system with all states of
length at most L", nothing more.

Usage:
  python3 -I oracles/python/c4_closed_component_search.py domain
  python3 -I oracles/python/c4_closed_component_search.py universe L
  python3 -I oracles/python/c4_closed_component_search.py window L [START STOP STRIDE]
  python3 -I oracles/python/c4_closed_component_search.py compare LOG
"""
from fractions import Fraction
from itertools import product
import json
import sys

ALPHABET = (0, 1, 2)
CLASSES = ("one-outside", "both-outside", "reducible")


class OracleFailure(ValueError):
    """A finite obligation failed; never read as a mathematical verdict."""


def require(condition, reason):
    if not condition:
        raise OracleFailure(reason)


# ------------------------------------------------------------------ domain


def image_words():
    """The 39 images, by length and then lexicographically (the corpus order)."""
    out = []
    for n in (1, 2, 3):
        out.extend(product(ALPHABET, repeat=n))
    return out


def incidence(sigma):
    """M[i][j] = number of letters i in sigma(j)."""
    return [[sigma[j].count(i) for j in ALPHABET] for i in ALPHABET]


def primitive(m):
    support = [[1 if m[i][j] else 0 for j in ALPHABET] for i in ALPHABET]
    power = support
    for _ in range(5):  # Wielandt: (n-1)^2 + 1 = 5
        if all(power[i][j] for i in ALPHABET for j in ALPHABET):
            return True
        power = [[1 if any(power[i][k] and support[k][j] for k in ALPHABET) else 0
                  for j in ALPHABET] for i in ALPHABET]
    return all(power[i][j] for i in ALPHABET for j in ALPHABET)


def charpoly(m):
    """(c0, c1, c2) of x^3 + c2 x^2 + c1 x + c0, by cofactor expansion."""
    tr = m[0][0] + m[1][1] + m[2][2]
    minors = (m[0][0] * m[1][1] - m[0][1] * m[1][0]
              + m[0][0] * m[2][2] - m[0][2] * m[2][0]
              + m[1][1] * m[2][2] - m[1][2] * m[2][1])
    det = (m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
           - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
           + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0]))
    return (-det, minors, -tr)


def value(c, x):
    return ((x + c[2]) * x + c[1]) * x + c[0]


def integer_root(c):
    if c[0] == 0:
        return True
    n = abs(c[0])
    return any(value(c, s * d) == 0 for d in range(1, n + 1) if n % d == 0 for s in (1, -1))


def _poly_rem(a, b):
    a = list(a)
    while len(a) >= len(b) and any(a):
        if a[-1] == 0:
            a.pop()
            continue
        f = a[-1] / b[-1]
        shift = len(a) - len(b)
        for k in range(len(b)):
            a[shift + k] -= f * b[k]
        a.pop()
    while a and a[-1] == 0:
        a.pop()
    return a


def sturm(c):
    p = [Fraction(c[0]), Fraction(c[1]), Fraction(c[2]), Fraction(1)]
    chain = [p, [p[1], 2 * p[2], 3 * p[3]]]
    while len(chain[-1]) > 1:
        r = _poly_rem(chain[-2], chain[-1])
        if not r:
            break
        chain.append([-x for x in r])
    return chain


def _changes(chain, x):
    signs = []
    for q in chain:
        v = sum(q[k] * x ** k for k in range(len(q)))
        if v != 0:
            signs.append(v > 0)
    return sum(1 for a, b in zip(signs, signs[1:]) if a != b)


def roots_in(chain, a, b):
    """Distinct real roots in (a, b] (Sturm)."""
    return _changes(chain, Fraction(a)) - _changes(chain, Fraction(b))


def outside_count(c):
    """Non-Perron roots outside the closed unit disc of an irreducible cubic
    with a real Perron root beta > 1."""
    chain = sturm(c)
    bound = 1 + max(abs(x) for x in c)
    real = roots_in(chain, -bound, bound)
    if real == 3:
        return 2 - roots_in(chain, -1, 1)
    require(real == 1, "an irreducible cubic has one or three real roots")
    v = value(c, abs(c[0]))
    require(v != 0, "|det| is a rational root")
    return 2 if v > 0 else 0


def eventually_constant(h):
    """h o h o h is constant: on three letters every orbit is periodic after
    at most two steps, so this is eventual constancy."""
    image = set(h[h[h[a]]] for a in ALPHABET)
    return len(image) == 1


def synchronizing(sigma):
    first = tuple(w[0] for w in sigma)
    last = tuple(w[-1] for w in sigma)
    return eventually_constant(first) or eventually_constant(last)


def off_corpus():
    """[(i, j, k, sigma, class, synchronizing)] for every primitive non-PIP
    triple, in (i, j, k) order."""
    words = image_words()
    cache, out = {}, []
    for i, a in enumerate(words):
        for j, b in enumerate(words):
            for k, c in enumerate(words):
                sigma = (a, b, c)
                m = incidence(sigma)
                if not primitive(m):
                    continue
                cp = charpoly(m)
                if cp not in cache:
                    cache[cp] = "reducible" if integer_root(cp) else ("PIP", "one-outside", "both-outside")[outside_count(cp)]
                klass = cache[cp]
                if klass == "PIP":
                    continue
                out.append((i, j, k, sigma, klass, synchronizing(sigma)))
    return out


def domain():
    """Partition counts: class -> [total, non-synchronizing], and the PIP corpus."""
    words = image_words()
    pip, pip_nonsync = 0, 0
    for sigma in product(words, repeat=3):
        m = incidence(sigma)
        if primitive(m):
            cp = charpoly(m)
            if not integer_root(cp) and outside_count(cp) == 0:
                pip += 1
                pip_nonsync += 0 if synchronizing(sigma) else 1
    out = {"PIP": [pip, pip_nonsync]}
    for name in CLASSES:
        out[name] = [0, 0]
    for (_, _, _, sigma, klass, sync) in off_corpus():
        out[klass][0] += 1
        out[klass][1] += 0 if sync else 1
    return out


# ------------------------------------------------------------- P_L


def signature(w):
    """(Parikh vector, N_ab for all ordered a, b): equal signatures of two
    words of one length are K_1 = K_2 = 0."""
    seen, n2 = [0, 0, 0], [0] * 9
    for x in w:
        for a in ALPHABET:
            n2[3 * a + x] += seen[a]
        seen[x] += 1
    return tuple(seen) + tuple(n2)


def irreducible(u, v):
    d = [0, 0, 0]
    for k in range(len(u) - 1):
        d[u[k]] += 1
        d[v[k]] -= 1
        if d == [0, 0, 0]:
            return False
    return True


def k2_zero_pairs(max_length):
    """Every normalised (u_0 < v_0) irreducible pair with K_1 = K_2 = 0 and
    length 2..max_length, as a sorted list of (u, v) tuples."""
    out = []
    for n in range(2, max_length + 1):
        groups = {}
        for w in product(ALPHABET, repeat=n):
            groups.setdefault(signature(w), []).append(w)
        for ws in groups.values():
            for u in ws:
                for v in ws:
                    if u[0] < v[0] and u[-1] != v[-1] and irreducible(u, v):
                        out.append((u, v))
    out.sort(key=lambda p: (len(p[0]), p))
    return out


def universe_counts(max_length):
    counts = {}
    for u, _ in k2_zero_pairs(max_length):
        counts[len(u)] = counts.get(len(u), 0) + 1
    return counts


# ------------------------------------------------------- fixed point


def inflate(sigma, w):
    return tuple(x for a in w for x in sigma[a])


def red(u, v):
    """Zero-return factorisation of a balanced pair, as normalised blocks."""
    require(len(u) == len(v), "pair sides differ in length")
    blocks, start, d = [], 0, [0, 0, 0]
    for k in range(len(u)):
        d[u[k]] += 1
        d[v[k]] -= 1
        if d == [0, 0, 0]:
            x, y = u[start:k + 1], v[start:k + 1]
            blocks.append((x, y) if x <= y else (y, x))
            start = k + 1
    require(start == len(u), "pair is not balanced")
    return blocks


def window(sigma, pairs, index=None):
    """(first_pass, rounds, survivors) of the greatest fixed point below
    `pairs` for `sigma`."""
    if index is None:
        index = {p: t for t, p in enumerate(pairs)}
    kids = {}
    for t, (u, v) in enumerate(pairs):
        row = []
        for b in red(inflate(sigma, u), inflate(sigma, v)):
            if b not in index:
                row = None
                break
            row.append(index[b])
        if row is not None:
            kids[t] = row
    first_pass = len(kids)
    alive = set(kids)
    rounds = 0
    while True:
        dead = {t for t in alive if any(c not in alive for c in kids[t])}
        if not dead:
            break
        alive -= dead
        rounds += 1
    return first_pass, rounds, len(alive)


def key(sigma):
    return "/".join("".join(str(x) for x in w) for w in sigma)


def run_window(max_length, start=0, stop=None, stride=1):
    """Window over the domain and the R3 pass: totals per class and one row
    per specimen with a first-pass survivor."""
    pairs = k2_zero_pairs(max_length)
    index = {p: t for t, p in enumerate(pairs)}
    specimens = off_corpus()
    stop = len(specimens) if stop is None else stop
    totals = {name: {"specimens": 0, "first_pass_specimens": 0, "first_pass": 0, "nonempty": 0} for name in CLASSES}
    rows = []
    for s in range(start, stop, stride):
        i, j, k, sigma, klass, sync = specimens[s]
        if sync:
            continue
        first, rounds, survivors = window(sigma, pairs, index)
        t = totals[klass]
        t["specimens"] += 1
        if first:
            t["first_pass_specimens"] += 1
            t["first_pass"] += first
            rows.append({"sigma": key(sigma), "class": klass, "first_pass": first, "rounds": rounds,
                         "survivors": survivors})
        if survivors:
            t["nonempty"] += 1
            require(klass != "both-outside", "a nonempty limit in the both-outside class contradicts R3")
    return {"L": max_length, "pairs": len(pairs), "totals": totals, "rows": rows}


def compare(path):
    """Recompute every WINDOW_SPECIMEN line of a Mojo log."""
    rows, universes = [], {}
    with open(path) as f:
        for line in f:
            if line.startswith("WINDOW_SPECIMEN "):
                rows.append(json.loads(line[len("WINDOW_SPECIMEN "):]))
    require(rows, "no WINDOW_SPECIMEN line in the log")
    for row in rows:
        L = row["L"]
        if L not in universes:
            pairs = k2_zero_pairs(L)
            universes[L] = (pairs, {p: t for t, p in enumerate(pairs)})
        pairs, index = universes[L]
        sigma = tuple(tuple(int(ch) for ch in w) for w in row["sigma"].split("/"))
        got = window(sigma, pairs, index)
        want = (row["first_pass"], row["rounds"], row["survivors"])
        require(got == want, "specimen %s: oracle %s, Mojo %s" % (row["sigma"], got, want))
    return {"rows": len(rows), "agree": True}


def main(argv):
    if len(argv) >= 2 and argv[1] == "domain":
        print(json.dumps(domain(), sort_keys=True))
        return 0
    if len(argv) >= 3 and argv[1] == "universe":
        print(json.dumps(universe_counts(int(argv[2])), sort_keys=True))
        return 0
    if len(argv) >= 3 and argv[1] == "window":
        rest = [int(x) for x in argv[3:6]]
        print(json.dumps(run_window(int(argv[2]), *rest), sort_keys=True))
        return 0
    if len(argv) >= 3 and argv[1] == "compare":
        print(json.dumps(compare(argv[2]), sort_keys=True))
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))

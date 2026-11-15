"""Independent flattened-word replay of #487's complete return-cut refinement.

The canonical implementation is Mojo. No Mojo code or precomputed transition
list is imported here. Mathematical all-depth identities have written proofs;
these deterministic tests are finite independent regressions, not G1 evidence.
"""
from collections import Counter
from dataclasses import dataclass
from itertools import product

import pytest

SIGMA = ("01", "121", "012")


def apply(images, word):
    if any(c not in tuple(str(i) for i in range(len(images))) for c in word):
        raise ValueError("letter outside supplied alphabet")
    if sum(len(images[int(c)]) for c in word) > 100_000:
        raise ValueError("refuse expansion before allocation")
    return "".join(images[int(c)] for c in word)


def power(images, word, n):
    if type(n) is not int or not 0 <= n <= 8:
        raise ValueError("bounded exact replay depth")
    for _ in range(n):
        word = apply(images, word)
    return word


def split0(word):
    if not word or word[0] != "0":
        raise ValueError("initial marker missing")
    indices = [i for i, c in enumerate(word) if c == "0"]
    return [word[a:b] for a, b in zip(indices, indices[1:] + [len(word)])]


def derive():
    prefix = power(SIGMA, "0", 6)
    # Discard the last piece: the next marker beyond the prefix is unknown.
    returns = tuple(dict.fromkeys(split0(prefix)[:-1]))
    index = {r: str(i) for i, r in enumerate(returns)}
    tau = tuple("".join(index[r] for r in split0(apply(SIGMA, w)))
                for w in returns)
    return returns, tau


RETURNS, TAU = derive()
STATES = tuple((j, d) for j, w in enumerate(RETURNS) for d in range(len(w)))


def decode(word):
    return "".join(RETURNS[int(c)] for c in word)


def parikh(word):
    return tuple(word.count(str(i)) for i in range(3))


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def subtract(a, b):
    return tuple(x-y for x, y in zip(a, b))


def m_times(v):
    return (v[0]+v[2], v[0]+2*v[1]+v[2], v[1]+v[2])


@dataclass(frozen=True)
class Edge:
    child: int
    occurrence: int
    target: tuple[int, int]
    emitted: str


def edge(j, d, t):
    if type(j) is not int or not 0 <= j < len(RETURNS):
        raise ValueError("bad return index")
    if type(d) is not int or not 0 <= d < len(RETURNS[j]):
        raise ValueError("terminal cut or invalid interior position")
    image = SIGMA[int(RETURNS[j][d])]
    if type(t) is not int or not 0 <= t < len(image):
        raise ValueError("invalid child index")
    before = apply(SIGMA, RETURNS[j][:d]) + image[:t]
    # Independent implementation: flatten and label every physical position,
    # then index directly. Canonical Mojo subtracts return-block lengths.
    labelled = [(k, int(c), e)
                for k, c in enumerate(TAU[j])
                for e in range(len(RETURNS[int(c)]))]
    k, c, e = labelled[len(before)]
    q = TAU[j][:k]
    assert before == decode(q) + RETURNS[c][:e]
    assert image[t] == RETURNS[c][e]
    return Edge(t, k, (c, e), q)


ALL_EDGES = tuple((j, d, t, edge(j, d, t)) for j, d in STATES
                  for t in range(len(SIGMA[int(RETURNS[j][d])])) )


def residual(n, kind):
    if type(n) is not int or not 0 <= n <= 6 or kind not in (0, 1):
        raise ValueError("invalid residual replay budget or pair")
    q = v = ""
    phase = kind
    for _ in range(n):
        q = apply(TAU, q) + ("0" if phase == 0 else "32")
        v = "2" + apply(TAU, v)
        phase = 1
    long = q + ("0" if phase == 0 else "1") + v
    short = q + ("3" if phase == 0 else "2")
    return phase, q, v, long, short


def test_actual_input_and_complete_edge_inventory():
    assert RETURNS == ("01121121", "012121121", "012121", "01121")
    assert TAU == ("012", "3212", "322", "02")
    assert len(STATES) == 28 and len(ALL_EDGES) == 80
    for j in range(4):
        assert apply(SIGMA, RETURNS[j]) == decode(TAU[j])
        actual = [e.target for jj, d, t, e in ALL_EDGES if jj == j]
        expected = [(int(c), k) for c in TAU[j]
                    for k in range(len(RETURNS[int(c)]))]
        assert actual == expected  # Lambda H = H tau, ordered occurrences
        projected = "".join(RETURNS[c][e] for c, e in actual)
        assert projected == apply(SIGMA, RETURNS[j])


def test_every_edge_preserves_external_prefix_and_next_letter():
    for j, d, t, e in ALL_EDGES:
        c, offset = e.target
        for exterior in ("", "0", "32"):
            prefix = decode(exterior) + RETURNS[j][:d]
            x = RETURNS[j][d]
            left = apply(SIGMA, prefix) + SIGMA[int(x)][:t]
            right = decode(apply(TAU, exterior) + e.emitted) + RETURNS[c][:offset]
            assert left == right
            assert SIGMA[int(x)][t] == RETURNS[c][offset]


def test_all_occurrence_paths_to_depth_four_without_deduplication():
    count = 0
    for j, d in STATES:
        # (current local state, exterior code, complete physical prefix, letter)
        paths = [((j, d), "", RETURNS[j][:d], RETURNS[j][d])]
        for depth in range(1, 5):
            next_paths = []
            for (a, b), q, prefix, x in paths:
                for t, next_letter in enumerate(SIGMA[int(x)]):
                    e = edge(a, b, t)
                    c, offset = e.target
                    new_q = apply(TAU, q) + e.emitted
                    direct = apply(SIGMA, prefix) + SIGMA[int(x)][:t]
                    recoded = decode(new_q) + RETURNS[c][:offset]
                    assert recoded == direct
                    assert RETURNS[c][offset] == next_letter
                    next_paths.append((e.target, new_q, direct, next_letter))
                    count += 1
            paths = next_paths
            # Every descendant letter of the selected original occurrence,
            # in order, occurs once, rather than only one selected branch.
            full = power(SIGMA, RETURNS[j], depth)
            start = len(power(SIGMA, RETURNS[j][:d], depth))
            end = start + len(power(SIGMA, RETURNS[j][d], depth))
            assert [len(p) for s, q, p, x in paths] == list(range(start, end))
            assert "".join(x for s, q, p, x in paths) == full[start:end]
    assert count == sum(len(power(SIGMA, w, n)) for w in RETURNS for n in range(1, 5)) == 2796


def test_inherited_map_has_interior_fixed_cuts_not_automatic_seams():
    basins = Counter()
    for s in STATES:
        for _ in range(3):
            s = edge(*s, 0).target
        assert edge(*s, 0).target == s
        basins[s] += 1
    assert basins == {(0, 0): 12, (1, 6): 8, (2, 3): 8}
    assert edge(0, 5, 0) == Edge(0, 1, (1, 6), "0")
    assert edge(1, 6, 0) == Edge(0, 2, (1, 6), "32")
    assert [edge(1, 6, t).target for t in range(3)] == [(1, 6), (1, 7), (1, 8)]


def test_two_phase_control_reconstructs_entire_words_and_unbounded_tail():
    for n, kind in product(range(7), range(2)):
        phase, q, v, long, short = residual(n, kind)
        a, b = ("0", "3") if kind == 0 else ("1", "2")
        assert long == power(TAU, a, n)
        assert short == power(TAU, b, n)
        assert v == "".join(power(TAU, "2", i) for i in range(n))
        tail = "121" + decode(v)
        assert tail == power(SIGMA, "1", n+1)
        assert decode(long) == decode(short) + tail
        if phase == 1:
            assert long[:len(q)] == short[:len(q)] == q
            assert (long[len(q)], short[len(q)]) == ("1", "2")
    assert [len(residual(n, 0)[2]) for n in range(7)] == [0, 1, 4, 12, 34, 96, 272]


def test_all_6400_one_step_two_track_defect_updates():
    for (j, d, t, et), (k, e, u, eb) in product(ALL_EDGES, repeat=2):
        prefix_t, prefix_b = RETURNS[j][:d], RETURNS[k][:e]
        x, y = RETURNS[j][d], RETURNS[k][e]
        delta = subtract(parikh(prefix_t), parikh(prefix_b))
        correction = subtract(parikh(SIGMA[int(x)][:t]), parikh(SIGMA[int(y)][:u]))
        expected = add(m_times(delta), correction)
        ct, dt = et.target
        cb, db = eb.target
        pt = decode(et.emitted) + RETURNS[ct][:dt]
        pb = decode(eb.emitted) + RETURNS[cb][:db]
        assert subtract(parikh(pt), parikh(pb)) == expected


def test_local_state_and_equal_next_letter_do_not_mean_equal_prefix_mass():
    p = RETURNS[1][:6]
    q = RETURNS[0] + p
    assert RETURNS[1][6] == "1"
    delta = subtract(parikh(p), parikh(q))
    assert delta == (-1, -5, -2)
    for _ in range(6):
        assert edge(1, 6, 0).target == (1, 6)
        p, q = apply(SIGMA, p), apply(SIGMA, q)
        delta = m_times(delta)
        assert subtract(parikh(p), parikh(q)) == delta != (0, 0, 0)


def test_equal_target_letters_do_not_erase_occurrence_addresses():
    a, b = edge(1, 2, 0), edge(1, 7, 0)
    assert a.target == b.target == (2, 0)
    assert (a.occurrence, b.occurrence) == (1, 3)
    assert (a.emitted, b.emitted) == ("3", "321")


def test_invalid_addresses_and_caps_fail_before_expansion():
    for args in ((-1, 0, 0), (4, 0, 0), (0, -1, 0), (0, 8, 0),
                 (0, 0, -1), (0, 0, 2), (1, 6, 3)):
        with pytest.raises(ValueError):
            edge(*args)
    for n, kind in ((-1, 0), (7, 0), (1000000, 1), (0, -1), (0, 2)):
        with pytest.raises(ValueError):
            residual(n, kind)

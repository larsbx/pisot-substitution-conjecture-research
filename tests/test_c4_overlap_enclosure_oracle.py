"""Independent full-word replay of all strict uniform-control routes."""

from itertools import combinations

from test_c4_addressed_newborn_oracle import inflate_addresses, global_cuts


def test_whole_factor_enclosure_for_every_literal_source():
    sigma = ("012", "120", "201")
    support = set(combinations(sigma, 2))
    checked = 0
    for pair in support:
        depth_two = [inflate_addresses(sigma, word, 2) for word in pair]
        depth_three = [inflate_addresses(sigma, word, 3) for word in pair]
        cut_two = global_cuts(*("".join(a for a, _ in track) for track in depth_two))
        cut_three = global_cuts(*("".join(a for a, _ in track) for track in depth_three))
        for source in range(3):
            positions = [i for i, (_, a) in enumerate(depth_two[0]) if a[0] == source]
            lo, hi = min(positions), max(positions) + 1
            enclosed = [(left, right) for left, right in zip(cut_two, cut_two[1:])
                        if lo < left < right < hi]
            assert len(enclosed) == 1
            left, right = enclosed[0]
            children = [(a, b) for a, b in zip(cut_three, cut_three[1:])
                        if 3 * left <= a < b <= 3 * right]
            assert len(children) == 3
            states = set()
            for a, b in children:
                target = tuple("".join(letter for letter, _ in row[a:b])
                               for row in depth_three)
                states.add(tuple(sorted(target)))
                assert b - a == 3
                for pos in range(a, b):
                    top, bottom = (row[pos] for row in depth_three)
                    assert top[0] != bottom[0]
                    assert top[1][0] == bottom[1][0] == source
                    checked += 1
            assert states == support
    assert checked == 81


def test_phase_zero_prefix_reverses_a_represented_terminal_pair():
    from test_c4_two_generation_rank_oracle import factor, inflate

    sigma = ("01", "12", "021")
    root = ("10", "01")
    terminals = [(root[0][-1], root[1][-1])]
    for size in (1, 2):
        row = factor(*(inflate(sigma, w) for w in root))
        assert len(row) == size
        assert all(a[0] == "1" and b[0] != "1" for a, b in row)
        root = row[-1]
        terminals.append((root[0][-1], root[1][-1]))
    assert terminals == [("0", "1"), ("1", "2"), ("2", "1")]
    assert root == ("12", "21")


def test_strict_control_realizes_only_nonreversing_suffix_pairs():
    from test_c4_complete_cone_hub_audit_oracle import SIGMA, STATES, literal_system

    _, rows = literal_system(SIGMA, STATES)
    assert all((a[0], b[0]) == ("1", "2") for row in rows for a, b in row)
    terminals = {(a[-1], b[-1]) for a, b in STATES}
    assert terminals == {("2", "0"), ("1", "0")}
    suffix = tuple(word[-1] for word in SIGMA)
    assert suffix == ("0", "2", "1")
    assert {(suffix[int(a)], suffix[int(b)]) for a, b in terminals} == terminals
    assert all((b, a) not in terminals for a, b in terminals)


def test_right_hub_reversal_transports_complete_child_rows():
    from test_c4_complete_cone_hub_audit_oracle import SIGMA, STATES, literal_system

    sigma_c = ("020", "20", "12")
    states_c = (("012", "120"), ("02", "20"), ("02012", "12020"))
    ids, _ = literal_system(sigma_c, states_c)
    assert ids == [[1, 2], [2], [1, 0, 1, 2]]
    assert all(a[0] == "0" and b[0] != "0" for a, b in states_c)

    for sigma, states, hub, top_has_hub in (
            (sigma_c, states_c, "2", True), (SIGMA, STATES, "0", False)):
        _, original = literal_system(sigma, states)
        reversed_sigma = tuple(w[::-1] for w in sigma)
        reversed_states = tuple((a[::-1], b[::-1]) for a, b in states)
        _, reversed_rows = literal_system(reversed_sigma, reversed_states)
        for before, after in zip(original, reversed_rows):
            assert after == [(a[::-1], b[::-1]) for a, b in reversed(before)]
            assert all((a[0] == hub) == top_has_hub and
                       (b[0] == hub) != top_has_hub for a, b in after)

    from test_c4_two_generation_rank_oracle import inflate, p

    for sigma, a, b, depth, i in (
            (sigma_c, "1", "2", 2, 3),
            (tuple(w[::-1] for w in sigma_c), "0", "1", 1, 0),
            (tuple(w[::-1] for w in SIGMA), "1", "2", 2, 7)):
        for _ in range(depth):
            a, b = inflate(sigma, a), inflate(sigma, b)
        assert a[i] == b[i] and p(a[:i]) == p(b[:i])


def test_type_d_endpoint_constraints_allow_mixed_right_hub_sides():
    suffix = tuple("012")
    terminals = {("1", "0"), ("2", "1")}
    assert {(suffix[int(a)], suffix[int(b)]) for a, b in terminals} == terminals
    assert all((b, a) not in terminals and {a, b} != {"0", "2"}
               for a, b in terminals)
    assert {a == "1" for a, _ in terminals} == {False, True}


def test_type_d_good_edge_forces_mirrored_descendant_labels():
    from test_c4_two_generation_rank_oracle import p

    reversed_sigma = ("021", "102", "201")
    assert tuple(w[0] for w in reversed_sigma) == tuple("012")
    a, h, b = reversed_sigma
    index = 2
    assert a[index] == b[index] == "1"
    assert p(a[:index]) == p(b[:index])
    first = (h[index], a[index], tuple(x-y for x,y in zip(p(a[:index]), p(h[:index]))))
    second = (b[index], h[index], tuple(x-y for x,y in zip(p(h[:index]), p(b[:index]))))
    assert first == ("2", "1", (0, -1, 1))
    assert second == (first[1], first[0], tuple(-x for x in first[2]))

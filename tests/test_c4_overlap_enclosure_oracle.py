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

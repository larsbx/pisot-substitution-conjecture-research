"""Independent addressed transport using full, untrimmed inflation words."""

import pytest

from test_c4_two_generation_rank_oracle import inflate, p


def inflate_addresses(sigma, original, depth):
    addressed = [(a, (source,)) for source, a in enumerate(original)]
    for _ in range(depth):
        addressed = [(child, address + (digit,))
                     for a, address in addressed
                     for digit, child in enumerate(sigma[int(a)])]
    return addressed


def global_cuts(top, bottom):
    return [i for i in range(len(top) + 1) if p(top[:i]) == p(bottom[:i])]


def resolve(sigma, root, addresses):
    depth = len(addresses[0]) - 1
    assert depth > 0 and len(addresses[1]) == depth + 1
    ancestor_intervals = [(0, len(root[0]))]
    ordinals = []
    first = None
    for level in range(1, depth + 1):
        tracks = [inflate_addresses(sigma, word, level) for word in root]
        words = tuple("".join(a for a, _ in track) for track in tracks)
        positions = [next(i for i, (_, got) in enumerate(track)
                          if got == expected[:level + 1])
                     for track, expected in zip(tracks, addresses)]
        cuts = global_cuts(*words)
        interval = next(((i, j) for i, j in zip(cuts, cuts[1:])
                         if all(i <= k < j for k in positions)), None)
        if interval is None:
            raise ValueError("split marked ancestry")

        previous = [word for word in root]
        for _ in range(level - 1):
            previous = [inflate(sigma, word) for word in previous]
        lo, hi = ancestor_intervals[-1]
        parent = tuple(word[lo:hi] for word in previous)
        absolute_start = len(inflate(sigma, previous[0][:lo]))
        ordinal = cuts.index(interval[0]) - cuts.index(absolute_start)
        ordinals.append(ordinal)
        ancestor_intervals.append(interval)
        if interval[1] - interval[0] == 1 and first is None:
            local = interval[0] - absolute_start
            sync_right = local > 0
            cut = local if sync_right else local + 1
            one_step = [inflate(sigma, word) for word in parent]
            assert 0 < cut < len(one_step[0])
            assert cut in global_cuts(*one_step)
            assert one_step[0][cut if sync_right else cut - 1] == one_step[1][
                cut if sync_right else cut - 1]
            first = tuple(ordinals), parent, cut, sync_right
    if ancestor_intervals[-1][1] - ancestor_intervals[-1][0] != 1:
        raise ValueError("missing final coincidence")
    return first


def test_physical_overlap_sources_produce_literal_newborns():
    assert resolve(("01", "12", "021"), ("1201", "0112"),
                   ((1, 2, 1, 2), (2, 1, 0, 1))) == (
                       (0, 1, 2), ("02112", "21120"), 11, True)
    assert resolve(("1", "02", "220"), ("12202202201", "02220220112"),
                   ((8, 1, 0, 0), (9, 1, 0, 1))) == (
                       (2, 2, 1), ("202201", "012202"), 4, True)


def test_exterior_witnesses_and_earliest_diagonal():
    root = ("01", "10")
    assert resolve(("01", "0", "2"), root, ((0, 0, 1), (0, 0, 1))) == (
        (0,), root, 1, False)
    assert resolve(("10", "0", "2"), root, ((1, 0), (1, 1))) == (
        (1,), root, 2, True)


def test_split_is_inherited_and_no_final_diagonal_is_rejected():
    sigma, root = ("01", "0", "2"), ("01", "10")
    with pytest.raises(ValueError, match="split"):
        resolve(sigma, root, ((0, 1, 0), (0, 0, 0)))
    with pytest.raises(ValueError, match="missing final"):
        resolve(sigma, root, ((1, 0), (1, 0)))


def test_first_diagonal_does_not_validate_a_malformed_suffix():
    sigma, root = ("01", "0", "2"), ("01", "10")
    # The independent oracle searches the full untrimmed address stream.
    with pytest.raises(StopIteration):
        resolve(sigma, root, ((0, 0, 2), (0, 0, 1)))
    with pytest.raises(ValueError, match="split"):
        resolve(sigma, root, ((0, 0, 0), (0, 0, 1)))

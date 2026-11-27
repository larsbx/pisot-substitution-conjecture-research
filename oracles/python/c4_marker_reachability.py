#!/usr/bin/env python3
"""Check exported C4 witnesses directly in literal substitution iterates.

Addresses are decoded by block lengths. Marker counts are then scanned in
literal prefixes with no corrected register, Parikh DFA, or product search.
"""

from collections import Counter
from itertools import chain, islice, pairwise
from pathlib import Path
import sys

from c4_original_marker_parity import compose_power


def prefix(sigma, seed, depth, limit):
    word = (seed,)
    for _ in range(depth):
        word = tuple(islice(chain.from_iterable(sigma[a] for a in word), limit))
    return word


def position(sigma, seed, path):
    lengths = [tuple(1 for _ in sigma)]
    for _ in path:
        lengths.append(tuple(sum(lengths[-1][c] for c in image) for image in sigma))
    offset = 0
    a = seed
    for remaining, digit in zip(reversed(lengths[:-1]), path, strict=True):
        assert 0 <= digit < len(sigma[a])
        offset += sum(remaining[b] for b in sigma[a][:digit])
        a = sigma[a][digit]
    return offset, a


def classify(top, bottom, cut, marker, first, last):
    u, v = top[:cut], bottom[:cut]
    counts = Counter(u)
    if counts != Counter(v):
        return None
    a0, b0 = marker
    observed_u, observed_v = (
        sum((last[a], first[b]) == marker for a, b in pairwise(w)) for w in (u, v)
    )
    same_last = (last[u[-1]] == a0) == (last[v[-1]] == a0)
    same_next = (first[top[cut]] == b0) == (first[bottom[cut]] == b0)
    required = (1 + (first[u[0]] != b0) + (last[u[-1]] != a0)) % 2
    violates = same_last or same_next or (observed_u - observed_v) % 2 != required
    return counts, observed_u, observed_v, required, same_last, same_next, violates


def replay(report):
    header, *rows = [line.split("\t") for line in report.read_text().splitlines()]
    version, source, marker_text, top_seam, bottom_seam = header
    assert version == "c4-marker-v1"
    images = tuple(tuple(map(int, image)) for image in source.split("/"))
    for rule, side, *data in rows:
        assert side in {"right", "left"}
        sigma = images if side == "right" else tuple(w[::-1] for w in images)
        endpoint = int(side == "right")
        top_seed, bottom_seed = int(top_seam[endpoint]), int(bottom_seam[endpoint])
        marker = tuple(map(int, marker_text if endpoint else marker_text[::-1]))
        first = compose_power(tuple(w[0] for w in sigma), 6)
        last = compose_power(tuple(w[-1] for w in sigma), 6)
        if rule == "certificate":
            assert len(data) == 1 and data[0]
            # Bounded calibration of the literal property. The Mojo checker
            # verifies all levels from the full exported invariant.
            top = prefix(sigma, top_seed, 12, 257)
            bottom = prefix(sigma, bottom_seed, 12, 257)
            assert len(top) == len(bottom) == 257
            for cut in range(1, 257):
                entry = classify(top, bottom, cut, marker, first, last)
                assert entry is None or not entry[-1], cut
            print(f"{source} {side}: literal control passes through cut 256")
            continue
        assert rule == "violation"
        (cut, u, v, top_next, bottom_next, parikh, mu, mv, required,
         equal_last, equal_next, top_path, bottom_path) = data
        cut = int(cut)
        paths = [tuple(map(int, w.split(","))) for w in (top_path, bottom_path)]
        depth = len(paths[0])
        assert depth == len(paths[1]) and depth > 0 and depth % 6 == 0
        top = prefix(sigma, top_seed, depth, cut + 1)
        bottom = prefix(sigma, bottom_seed, depth, cut + 1)
        for seed, path, ray, word, following in zip(
            (top_seed, bottom_seed), paths, (top, bottom), (u, v),
            (int(top_next), int(bottom_next)), strict=True
        ):
            assert position(sigma, seed, path) == (cut, following)
            assert ray == (*map(int, word), following)
        actual = classify(top, bottom, cut, marker, first, last)
        assert actual is not None
        counts, observed_u, observed_v, expected, same_last, same_next, violates = actual
        assert tuple(counts[a] for a in range(len(sigma))) == tuple(map(int, parikh.split(",")))
        assert (observed_u, observed_v, expected, same_last, same_next) == (
            int(mu), int(mv), int(required), bool(int(equal_last)), bool(int(equal_next)),
        )
        assert violates
        for earlier in range(1, cut):
            entry = classify(top, bottom, earlier, marker, first, last)
            assert entry is None or not entry[-1], earlier
        print(f"{source} {side}: replayed cut {cut} at depth {depth} ({u}/{v})")
        if source.startswith("0120") and side == "right" and cut > 3:
            assert classify(top, bottom, 3, marker, first, last)[1:] == (0, 0, 0, False, False, False)
            print("reordered third cut: balanced, opposite groups, parity 0")


if __name__ == "__main__":
    for path in sys.argv[1:]:
        replay(Path(path))

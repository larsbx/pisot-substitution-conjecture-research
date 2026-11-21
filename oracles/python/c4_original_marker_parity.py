#!/usr/bin/env python3
"""Independent exact replay of the original-word C4 marker witnesses."""

from collections import Counter
from itertools import product
from pathlib import Path
import sys

from h1_census_ap import image, legal_words

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "reference"))
from psc_research.pip_screen import charpoly, mat, pip_corpus


def compose_power(endpoint_map, power):
    values = tuple(range(len(endpoint_map)))
    for _ in range(power):
        values = tuple(endpoint_map[a] for a in values)
    return values


def right_ray(sigma, letter):
    word = (letter,)
    for _ in range(12):
        word = image(sigma, word)
        if len(word) > 3**12:
            raise ValueError("literal ray exceeds the word cap")
    return word


def prefixes(ray, last, first, marker):
    counts = [0] * 3
    marks = 0
    for i, letter in enumerate(ray[:-1]):
        counts[letter] += 1
        if i:
            marks += (last[ray[i - 1]], first[letter]) == marker
        yield tuple(counts), marks, last[letter], first[ray[i + 1]]


def violation(top, bottom, last, first, marker):
    a0, b0 = marker
    start = int(first[top[0]] != b0)
    for length, (u, v) in enumerate(
        zip(prefixes(top, last, first, marker), prefixes(bottom, last, first, marker)), 1
    ):
        parikh_u, marks_u, last_u, next_u = u
        parikh_v, marks_v, last_v, next_v = v
        if parikh_u != parikh_v:
            continue
        if (last_u == a0) == (last_v == a0) or (next_u == b0) == (next_v == b0):
            continue
        if (marks_u - marks_v - 1 - start - int(last_u != a0)) % 2:
            return length
    return None


def replay():
    corpus = pip_corpus()
    assert len(corpus) == 4554
    specimens = 0
    maximum = 0
    witnesses = Counter()
    for raw in corpus:
        if any(coefficient % 2 for coefficient in charpoly(mat(raw))):
            continue
        sigma = tuple(tuple(b - 1 for b in raw[a]) for a in range(1, 4))
        last = compose_power(tuple(w[-1] for w in sigma), 6)
        first = compose_power(tuple(w[0] for w in sigma), 6)
        left, right = set(last), set(first)
        legal = legal_words(sigma, 2)
        seams = legal.intersection(product(left, right))
        if len(seams) <= len(left) + len(right) - 1:
            continue
        specimens += 1
        rays = {b: right_ray(sigma, b) for b in right}
        shape = (len(left), len(right), len(seams))
        markers = 0
        for a0, b0 in sorted(seams):
            cells = {(a != a0, b != b0) for a, b in seams}
            if len(cells) != 4:
                continue
            markers += 1
            opponents = sorted({b for a, b in seams if a != a0 and b != b0})
            hit = None
            for b in opponents:
                hit = violation(rays[b0], rays[b], last, first, (a0, b0))
                if hit:
                    break
            if hit is None:
                raise AssertionError(f"missing marker witness for {sigma} at {a0}.{b0}")
            witnesses[shape] += 1
            maximum = max(maximum, hit)
        if not markers:
            raise AssertionError(f"missing grouped square for {sigma}")
    return specimens, witnesses, maximum


if __name__ == "__main__":
    count, by_shape, longest = replay()
    assert (count, sum(by_shape.values()), longest) == (96, 540, 5038)
    assert sorted(by_shape.items()) == [
        ((2, 2, 4), 96), ((2, 3, 5), 24), ((2, 3, 6), 144),
        ((3, 2, 5), 24), ((3, 2, 6), 144), ((3, 3, 9), 108),
    ]
    print(f"even residue {count}, singleton markers {sum(by_shape.values())}, max prefix {longest}")
    print("marker witnesses", *sorted(by_shape.items()))

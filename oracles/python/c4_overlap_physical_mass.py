"""Independently replay physical overlaps by merging literal interval cuts."""
from collections import Counter
from functools import lru_cache

from c4_overlap_scc_obstruction import components, condensation, graph
from c4_pair_overlap_new_incidence import ELL, M, interval, literal_words, power, require

ZERO = (0, 0, 0)
UNITS = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
GRID = 10**9
SQUARE = power(M, 2)


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def apply(matrix, vector):
    return tuple(sum(x*y for x, y in zip(row, vector)) for row in matrix)


@lru_cache(maxsize=1)
def length_bounds():
    bounds = [interval(ell) for ell in ELL]
    require(all(lo > 0 for lo, _ in bounds), 'positive physical letter lengths')
    return tuple((int(lo*GRID), int(hi*GRID)+1) for lo, hi in bounds)


def sign(vector):
    if vector == ZERO:
        return 0
    bounds = length_bounds()
    lower = sum(x*ends[x < 0] for x, ends in zip(vector, bounds))
    upper = sum(x*ends[x >= 0] for x, ends in zip(vector, bounds))
    require(lower > 0 or upper < 0, 'unseparated physical length sign')
    return 1 if lower > 0 else -1


def overlap(a, b, displacement):
    left = displacement if sign(displacement) > 0 else ZERO
    right = add(displacement, b)
    return sub(a if sign(sub(a, right)) < 0 else right, left)


def partition_word(word):
    prefix = ZERO
    result = []
    for letter in word:
        letter = int(letter)
        end = add(prefix, UNITS[letter])
        result.append((letter, prefix, end))
        prefix = end
    return result


def forward(first, second, shift, words):
    """Intersect two translated partitions by sweeping both endpoint lists."""
    top, bottom = words[first], words[second]
    i = j = 0
    while i < len(top) and j < len(bottom):
        a, p, end = top[i]
        b, q, other_end = bottom[j]
        z = sub(add(shift, p), q)
        length = overlap(UNITS[a], UNITS[b], sub(ZERO, z))
        if sign(length) > 0:
            swapped = (b, a, *sub(ZERO, z))
            yield min((a, b, *z), swapped), length
        advance = sign(sub(end, sub(other_end, shift)))
        if advance <= 0:
            i += 1
        if advance >= 0:
            j += 1


def packet_lines():
    yield 'schema c4-overlap-physical-mass-v1'
    for source in range(12):
        obj = graph(source)
        states, rows = obj.states, obj.rows
        words = [partition_word(word) for word in literal_words(source, 2)]
        by_state = {state: i for i, state in enumerate(states)}
        require(len(by_state) == len(states), 'duplicate state')
        incoming = [Counter() for _ in states]
        for i, row in enumerate(rows):
            for j in row:
                incoming[j][i] += 1
        deficits = []
        losses = 0
        for i, (a, b, *z) in enumerate(states):
            z = tuple(z)
            # This reachable class never hits a fixed point of track swap.
            require(a != b or z != ZERO, 'unexpected fixed track-swap orbit')
            mass = overlap(UNITS[a], UNITS[b], sub(ZERO, z))
            require(sign(mass) > 0, 'nonpositive physical mass')
            budget = apply(SQUARE, mass)
            total = omitted = ZERO
            observed = Counter()
            for state, length in forward(a, b, apply(SQUARE, z), words):
                total = add(total, length)
                if state in by_state:
                    observed[by_state[state]] += 1
                else:
                    omitted = add(omitted, length)
            require(total == budget, 'literal subdivisions do not partition the mass')
            require(observed == incoming[i], 'forward/inverse occurrence multiplicities differ')
            losses += sign(omitted) > 0
            deficits.append(omitted)
            yield f'row {source} {i} ' + ' '.join(map(str, (*mass, *omitted)))
        blocks = components(rows)
        dag = condensation(rows, blocks)
        non_sources = {child for row in dag for child in row}
        count = 0
        for c, block in enumerate(blocks):
            if c in non_sources:
                continue
            require(any(i < 3 for i in block), 'source SCC without a declared root')
            witness = next((i for i in block if deficits[i] != ZERO), -1)
            require(witness >= 0, 'source SCC has no strictly losing row; inconclusive')
            count += 1
            yield f'block {source} {c} {len(block)} {witness}'
        yield f'graph {source} {len(states)} {sum(map(len, rows))} {losses} {count}'


if __name__ == '__main__':
    for line in packet_lines():
        print(line)

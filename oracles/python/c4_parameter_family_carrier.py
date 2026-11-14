"""Independent replay of the (1, 01^k2, 001) ordered 01/10 carrier.

The symbolic certificate uses k = n + 5, n >= 0. Exponents are pairs
(coefficient of n, constant). Its tests compare exact word identities
and irreducible blocks. A separate literal replay handles small k.
"""

from collections import Counter


# I is 1^(n+5). A prime swaps the preceding state ID. J is k-1
# diagonal 1s. Cj and Dj are n+j oriented periods followed by k-2
# diagonal 1s; the latter are spelled K in the table for readability.
TABLE = """
0 0 |
01 10 | 1' J 22
010I2 I2001 | 1' J 24 C3 K 14
011 110 | 1' J 23 J 22
0110I2 I20011 | 1' J 23 J 24 C2 K 16
0110I20 I200101 | 1' J 23 J 24 C2 K 17
0110I20I2 I20I20011 | 1' J 23 J 24 C2 K 15 3' C2 K 16
01110I20I2 I20I200111 | 1' J 23 J 23 J 24 C1 K 18 3' C1 K 19
01110I20I20 I20I2001101 | 1' J 23 J 23 J 24 C1 K 18 3' C1 K 21
01110I20I210 I20I20011011 | 1' J 23 J 23 J 24 C1 K 18 3' C1 K 20 J 22'
1 1 |
1120 2011 | 0 6'
11200 20011 | 0 7'
1120I200 200110I2 | 0 9' D4 K 12' 10
1120I2001 2001110I2 | 0 8' J 24' D3 K 14'
1120I20I200 200110I20I2 | 0 9' D4 K 12' 3 D4 K 12' 10
1120I20I2001 2001110I20I2 | 0 8' J 24' D3 K 13' 3 D3 K 14'
1120I20I20011 2001110I210I2 | 0 8' J 24' D3 K 13' 1 J 24' D2 K 16'
1120I20I20I200 200110I20I20I2 | 0 9' D4 K 12' 3 D4 K 12' 3 D4 K 12' 10
1120I20I20I2001 2001110I20I20I2 | 0 8' J 24' D3 K 13' 3 D3 K 13' 3 D3 K 14'
1120I20I20I200101 2001110I20I210I20 | 0 8' J 24' D3 K 13' 3 D3 K 13' 1 J 24' D2 K 17'
1120I20I20I20011 2001110I20I210I2 | 0 8' J 24' D3 K 13' 3 D3 K 13' 1 J 24' D2 K 16'
12 21 | 0 2'
120 201 | 0 4'
1210 2011 | 0 5' J 22'
""".strip().splitlines()

ZERO = (0, 0)
ONE = (0, 1)
K = (1, 5)
IMAGE = 'A'  # 0 1^(n+5) 2
ONES = '1'


def add(left, right):
    return (left[0] + right[0], left[1] + right[1])


def sub(left, right):
    return (left[0] - right[0], left[1] - right[1])


def require(condition, message):
    if not condition:
        raise ValueError(message)


def coalesce(tokens):
    """Combine adjacent identical pieces as affine exponents."""
    result = []
    for symbol, exponent in tokens:
        if exponent == ZERO:
            continue
        if result and result[-1][0] == symbol:
            result[-1] = (symbol, add(result[-1][1], exponent))
        else:
            result.append((symbol, exponent))
    return result


def normal_form(tokens):
    """Re-express each literal occurrence of A as one power of A."""
    runs = coalesce(tokens)
    result = []
    i = 0
    while i < len(runs):
        if (i + 2 < len(runs) and runs[i][0] == '0' and
                runs[i + 1] == (ONES, K) and runs[i + 2][0] == '2'):
            result.extend([
                ('0', sub(runs[i][1], ONE)),
                (IMAGE, ONE),
                ('2', sub(runs[i + 2][1], ONE)),
            ])
            i += 3
        else:
            result.append(runs[i])
            i += 1
    return coalesce(result)


def decode_word(template):
    return coalesce((ONES, K) if c == 'I' else (c, ONE) for c in template)


def inflate(word):
    result = []
    for symbol, exponent in word:
        if symbol == '0':
            result.append((ONES, exponent))
        elif symbol == ONES:
            result.append((IMAGE, exponent))
        else:
            require(symbol == '2' and exponent[0] == 0, 'unsupported 2-run')
            result += [('0', (0, 2)), (ONES, ONE)] * exponent[1]
    return normal_form(result)


def block(word_top, word_bottom):
    """Verify every positive proper prefix. Only equal symbols may pump."""
    i = j = 0
    x, left = word_top[i]
    y, right = word_bottom[j]
    diff = [0, 0, 0]
    while True:
        delta = sub(left, right)
        if min(delta) >= 0:
            common = right
        else:
            require(max(delta) <= 0, 'run alignment changes with n')
            common = left
        require(min(common) >= 0 and common != ZERO, 'invalid alignment span')
        if x != y:
            require(common[0] == 0, 'unequal-letter run depends on n')
            for offset in range(common[1]):
                diff[int(x)] += 1
                diff[int(y)] -= 1
                if diff == [0, 0, 0]:
                    require(offset == common[1] - 1 and left == right and
                            i + 1 == len(word_top) and j + 1 == len(word_bottom),
                            'balanced proper prefix')
        elif diff == [0, 0, 0]:
            require(common == ONE and left == right and
                    i + 1 == len(word_top) and j + 1 == len(word_bottom),
                    'balanced proper prefix in equal columns')
        left, right = sub(left, common), sub(right, common)
        if left == ZERO:
            i += 1
            if i < len(word_top):
                x, left = word_top[i]
        if right == ZERO:
            j += 1
            if j < len(word_bottom):
                y, right = word_bottom[j]
        if i == len(word_top) or j == len(word_bottom):
            require(i == len(word_top) and j == len(word_bottom) and
                    diff == [0, 0, 0], 'incomplete or unbalanced endpoint')
            return


def signed_index(token):
    return int(token.rstrip("'")) + (25 if token.endswith("'") else 0)


def row_tracks(tokens, states, side):
    out = []
    position = 0
    while position < len(tokens):
        token = tokens[position]
        position += 1
        if token == 'J':
            out.append((ONES, (1, 4)))
        elif token[0] in 'CD':
            # The long and short cyclic words have the terminal phase
            # 1^(k-2)112 and 1^(k-2)2. The initial phase is identical.
            if token[0] == 'D':
                side_is_long = side == 1
            else:
                side_is_long = side == 0
            suffix = '112' if side_is_long else '2'
            require(tokens[position] == 'K', 'period lacks diagonal tail')
            position += 1
            final_child = states[signed_index(tokens[position])][side]
            remaining = list(final_child)
            for char in suffix:
                symbol, count = remaining[0]
                require(char == symbol and count[1] >= 1, 'terminal phase mismatch')
                residual = sub(count, ONE)
                if residual == ZERO:
                    remaining.pop(0)
                else:
                    remaining[0] = (symbol, residual)
            out += [(ONES, K if side_is_long else (1, 3)), ('2', ONE),
                    (IMAGE, (1, int(token[1:])))] + remaining
            position += 1
        else:
            out += states[signed_index(token)][side]
    return normal_form(out)


def symbolic(table=TABLE):
    entries = [line.split('|') for line in table]
    base = [tuple(map(decode_word, pair.split())) for pair, _ in entries]
    states = base + [(v, u) for u, v in base]
    require(base[1] == (decode_word('01'), decode_word('10')), 'missing ordered seed')
    for i, ((top, bottom), (_, row)) in enumerate(zip(base, entries, strict=True)):
        try:
            block(top, bottom)
            if top == bottom:
                require(not row.split(), 'terminal diagonal with children')
                continue
            for side, parent in enumerate((top, bottom)):
                actual = inflate(parent)
                supplied = row_tracks(row.split(), states, side)
                require(supplied == actual,
                        f'track {side}: supplied {supplied!r}, inflated {actual!r}')
        except ValueError as error:
            raise ValueError(f'row {i}: {error}') from error


def literal_row(tokens, states, k):
    """Decode the certificate independently of the symbolic track identities."""
    result = []
    for token in tokens:
        if token == 'J':
            result.extend([states[10]] * (k - 1))
        elif token == 'K':
            result.extend([states[10]] * (k - 2))
        elif token[0] in 'CD':
            last = states[11 if token[0] == 'C' else 36]
            result.extend(([states[10]] * (k - 2) + [last]) * (k - 5 + int(token[1:])))
        else:
            result.append(states[signed_index(token)])
    return result


def literal_children(images, pair):
    """Recompute cuts by full Parikh-prefix counts, retaining occurrences."""
    top, bottom = (''.join(images[int(letter)] for letter in word) for word in pair)
    require(len(top) == len(bottom), 'inflated length mismatch')
    counts_top, counts_bottom = Counter(), Counter()
    start = 0
    for end, (a, b) in enumerate(zip(top, bottom, strict=True), 1):
        counts_top[a] += 1
        counts_bottom[b] += 1
        if counts_top == counts_bottom:
            yield (top[start:end], bottom[start:end])
            start = end
    require(start == len(top), 'missing final cut')


def literal(k, *, show=True):
    images = ('1', '0' + '1' * k + '2', '001')
    seed = ('01', '10')
    seen = {seed}
    queue = [seed]
    occurrences = 0
    for pair in queue:
        require(len(queue) <= 250 and len(pair[0]) <= 2000, 'literal budget exhausted')
        if pair[0] == pair[1]:
            continue
        for child in literal_children(images, pair):
            occurrences += 1
            if child not in seen:
                seen.add(child)
                queue.append(child)
    if show:
        print(k, len(queue), max(len(top) for top, _ in queue), occurrences)
    return seen


def endpoint_intertwiners():
    """Endpoint powers have periods 2 and 3 after the first iterate."""
    from itertools import product

    maps = list(product(range(3), repeat=3))

    def power(mapping, n):
        result = tuple(range(3))
        for _ in range(n):
            result = tuple(mapping[a] for a in result)
        return result

    def admits(source, target):
        return any(all(q[source[a]] == target[q[a]] for a in range(3)) for q in maps)

    for n in range(1, 7):
        last_sigma = power((1, 2, 1), n)
        last_beta = power((1, 2, 0), n)
        first_sigma = power((1, 0, 0), n)
        first_beta = (0, 0, 0)
        require(admits(last_sigma, last_beta) == (n % 3 == 0),
                'unexpected forward endpoint intertwiner')
        require(admits(first_beta, first_sigma) == (n % 2 == 0),
                'unexpected reverse endpoint intertwiner')
        require(len(set(first_sigma)) == len(set(last_sigma)) == 2,
                'unexpected endpoint image size')


def negative_controls():
    for replacement in ("01 10 | 1' 22", "01 10 | 22 J 1'", "01 10 | 1 J 22"):
        edited = list(TABLE)
        edited[1] = replacement
        try:
            symbolic(edited)
        except ValueError as error:
            require(str(error).startswith('row 1: track '),
                    f'control failed at an unexpected boundary: {error}')
        else:
            raise ValueError(f'accepted edited ordered row: {replacement}')



def main():
    symbolic()
    negative_controls()
    endpoint_intertwiners()
    print('symbolic rows verified for every k >= 5 (50 ordered slots)')
    for k, count in ((2, 128), (3, 60), (4, 48), (5, 48), (8, 48)):
        seen = literal(k)
        require(len(seen) == count, f'unexpected carrier at k={k}')
        if k >= 4:
            base = [tuple(w.replace('I', '1' * k) for w in line.split('|')[0].split())
                    for line in TABLE]
            states = base + [(v, u) for u, v in base]
            require(set(states) == seen, f'literal template differs at k={k}')
            images = ('1', '0' + '1' * k + '2', '001')
            for pair, line in zip(base, TABLE, strict=True):
                if pair[0] == pair[1]:
                    continue
                actual = list(literal_children(images, pair))
                supplied = literal_row(line.split('|')[1].split(), states, k)
                require(supplied == actual, f'ordered row differs at k={k}, pair={pair}')
    counter_parent = ('01110111201112', '11120111200111')
    counter_child = ('12101112011120111200', '20011011120111201112')
    at_three = literal(3, show=False)
    require(counter_parent in at_three, 'negative-control parent must be reachable')
    require(counter_child in list(literal_children(('1', '01112', '001'), counter_parent)),
            'negative control lost its ordered child occurrence')
    templates = {tuple(w.replace('I', '111') for w in line.split('|')[0].split())
                 for line in TABLE}
    require(counter_child not in templates and counter_child[::-1] not in templates,
            'negative control child unexpectedly belongs to the templates')


if __name__ == '__main__':
    main()

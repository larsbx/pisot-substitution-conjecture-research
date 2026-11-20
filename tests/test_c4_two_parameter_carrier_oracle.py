"""Literal ordered replay of the bivariate balanced partition certificate."""

import re
from pathlib import Path

import pytest

from test_c4_strict_period_oracle import cuts, expand, row


SOURCE = Path(__file__).resolve().parents[1] / "kernel/tests/test_c4_two_parameter_carrier.mojo"


def decode(r, k):
    table = SOURCE.read_text().split('comptime CERTIFICATE = """', 1)[1].split('"""', 1)[0]
    records = [line.split(" | ") for line in table.strip().splitlines()]
    sigma = ("1", "0" + "1" * k + "2", "0" * r + "1")
    alphabet = dict(zip("012ABC", ("0", "1", "2", sigma[1], sigma[1][1:], sigma[2])))
    diagonals = {"E": k - r, "F": k - r + 1, "G": k - 1}

    def count(form):
        if m := re.fullmatch(r"(k-r|k|r)([+-][0-9]+)?", form):
            return {"k-r": k - r, "k": k, "r": r}[m[1]] + int(m[2] or "0")
        return int(form or "1")

    def word(source):
        tokens = (part.partition("^") for part in source.split())
        return "".join(alphabet[letter] * count(exponent) for letter, _, exponent in tokens)

    states = [(word(left), word(right)) for left, right, _ in records]
    children = {}
    for state, (_, _, expression) in zip(states, records, strict=True):
        if expression == "-":
            continue
        stack = [[]]
        for token in expression.split():
            if token == "(":
                stack.append([])
            elif token.startswith(")*"):
                block = stack.pop()
                stack[-1] += block * count(token[2:])
            else:
                prefix, colon, item = token.partition(":")
                child, _, exponent = (item if colon else prefix).partition("*")
                pair = states[int(child.rstrip("'"))]
                if child.endswith("'"):
                    pair = pair[::-1]
                prepend = [("1", "1")] * diagonals[prefix] if colon else []
                stack[-1] += (prepend + [pair]) * count(exponent)
        assert len(stack) == 1
        children[state] = stack.pop()
    return sigma, states, children


@pytest.mark.parametrize(("r", "k"), [(4, 7), (4, 13), (5, 8), (7, 11), (8, 11), (12, 23), (21, 24)])
def test_literal_certificate_matches_complete_rows_at_samples(r, k):
    sigma, states, children = decode(r, k)
    assert states[0] == ("01", "10")
    assert len(set(states)) == 30
    assert max(len(a) for a, _ in states) == (r + 2) * (k + 4)
    for parent in states:
        assert list(cuts(*parent)) == [0, len(parent[0])]
        if parent[0] == parent[1]:
            assert len(parent[0]) == 1
            continue
        assert [child for _, _, child in row(sigma, parent)] == children[parent]


def test_below_domain_the_boundary_row_changes():
    r, k = 4, 6
    sigma, states, children = decode(r, k)
    # The extrapolated expression uses a negative repeat at k-r-3.
    # Python's list repetition drops it, which still cannot reconstruct the row.
    parent = states[22]
    assert expand(sigma, parent[0]) != "".join(a for a, _ in children[parent])

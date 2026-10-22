"""Exact independent cardinalities of the finite PDS certificate domains.

PYTHONPATH=reference python oracles/python/omega_domain_audit.py

Group words by their Parikh vectors and weight each column by its exact
multinomial count. PIP depends only on the incidence matrix. This independently
checks the union and intersection counts without building overlap graphs or
using the historical floating-point screen. Canonical corpus: psc.corpus.
"""
from functools import lru_cache
from itertools import product
from math import factorial
import json

from psc_research.pip_screen import charpoly, irreducible, pisot, primitive


def columns(bound):
    return [p for p in product(range(bound + 1), repeat=3) if 1 <= sum(p) <= bound]


def multiplicity(p):
    return factorial(sum(p)) // (factorial(p[0]) * factorial(p[1]) * factorial(p[2]))


@lru_cache(None)
def pip(cols):
    matrix = [[cols[j][i] for j in range(3)] for i in range(3)]
    cubic = charpoly(matrix)
    return primitive(matrix) and irreducible(*cubic) and pisot(*cubic)


def count(bound, total=None):
    out = 0
    for cols in product(columns(bound), repeat=3):
        if total is not None and sum(map(sum, cols)) > total:
            continue
        if pip(cols):
            out += multiplicity(cols[0]) * multiplicity(cols[1]) * multiplicity(cols[2])
    return out


def main():
    standing = count(3)
    images4 = count(4)
    total8 = count(6, 8)  # non-erasing images leave at most six letters in one image
    intersection = count(4, 8)
    result = {"standing": standing, "images_le_4": images4, "total_le_8": total8,
              "intersection": intersection, "union": images4 + total8 - intersection,
              "screened_incidence_matrices": pip.cache_info().misses, "arithmetic": "integer/rational"}
    expected = (4554, 135990, 24486, 14670, 145806)
    if (standing, images4, total8, intersection, result["union"]) != expected:
        raise RuntimeError(f"finite-domain cardinality disagreement: {result}")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()

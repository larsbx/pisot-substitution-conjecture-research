"""Exhaust all 36 source substitutions and 1,296 child orders for one packet.

The fixed packet is P=[M^2,M^2], N=[[0,M],[M,0]], for the M of #490.
This is a finite literal-realizability exclusion, NOT general C4 or PSC.
Reuse #490's independently computed exact inverse; never treat a remaining
necessary-condition survivor as a genuine balanced-pair realization.
"""
from collections import Counter
from functools import lru_cache
from itertools import permutations, product
from pathlib import Path
import json

import test_c4_periodic_order_lift_oracle as prior


def sources():
    """All and only literal source words with the frozen incidence matrix."""
    return tuple(product(*(tuple(sorted(set(permutations(w)))) for w in prior.SIGMA)))


def require_source(sigma):
    if len(sigma) != 3:
        raise ValueError("ternary substitution required")
    expected = ((1, 1, 0), (0, 2, 1), (1, 1, 1))
    for word, mass in zip(sigma, expected):
        if prior.counts(word) != mass:
            raise ValueError("source outside the fixed incidence class")


def factor(top, bottom):
    if not top or prior.counts(top) != prior.counts(bottom):
        raise ValueError("nonempty balanced words required")
    defect, out, start = [0, 0, 0], [], 0
    for k, (x, y) in enumerate(zip(top, bottom), 1):
        defect[x] += 1
        defect[y] -= 1
        if not any(defect):
            out.append((top[start:k], bottom[start:k]))
            start = k
    if start != len(top) or start != len(bottom):
        raise ValueError("incomplete factorization")
    return tuple(out)


def inflate(sigma, word):
    return tuple(z for letter in word for z in sigma[letter])


@lru_cache(maxsize=1)
def order_numerators():
    """Separate the child-order contribution Q*Omega from -Q*C_sigma*P."""
    _, p, _, _, _, q, _, _, options = prior.packet()
    contributions = []
    zero = [[0] * 6 for _ in range(3)]
    for j, variants in enumerate(options):
        col = []
        for row in variants:
            omega = prior.right_hand_column(p, zero, j, row)
            col.append(tuple(sum(q[i][3*j+k] * omega[k] for k in range(3))
                             for i in range(18)))
        contributions.append(col)
    return tuple((choice, tuple(sum(contributions[j][c][i]
                                    for j, c in enumerate(choice))
                               for i in range(18)))
                 for choice in product(*(range(len(v)) for v in options)))


@lru_cache(maxsize=None)
def first_pairs(mean):
    # Prior replay exhausts all 20 words / 400 ordered pairs. Track swapping
    # is factored out only AFTER that complete actual irreducibility check.
    return tuple((u, v) for u, v in prior.first_state_pairs(mean) if u < v)


def inspect_root(sigma, choices, mean):
    """Return a necessary-condition stage and complete first-row receipts."""
    _, p, _, _, _, _, _, _, options = prior.packet()
    expected = tuple(tuple(p[i][child] for i in range(3))
                     for child in options[0][choices[0]])
    receipts = []
    for u, v in first_pairs(mean):
        children = factor(inflate(sigma, u), inflate(sigma, v))
        masses = tuple(prior.counts(a) for a, _ in children)
        diagonals = sum(a == b for a, b in children)
        compatible = not diagonals and masses == expected
        receipts.append({
            "root": [list(u), list(v)],
            "child_masses": [list(p) for p in masses],
            "expected_child_masses": [list(p) for p in expected],
            "diagonal_factors": diagonals,
            "row_compatible": compatible,
        })
    if not receipts:
        return "word_impossible", receipts
    if any(x["row_compatible"] for x in receipts):
        # This would be unresolved, never accepted or silently discarded.
        return "unresolved", receipts
    if any(not x["diagonal_factors"] for x in receipts):
        return "wrong_row", receipts
    return "diagonal", receipts


@lru_cache(maxsize=1)
def census():
    m, p, n, _, operator, q, den, _, _ = prior.packet()
    all_rows, survivors = [], []
    totals = Counter()
    for sigma in sources():
        require_source(sigma)
        c = [[prior.area(sigma[j])[i] for j in range(3)] for i in range(3)]
        cp = prior.mm(c, p)
        negcp = [-cp[a][j] for j in range(6) for a in range(3)]
        shift = tuple(sum(q[i][k] * negcp[k] for k in range(18)) for i in range(18))
        stats = Counter({key: 0 for key in (
            "nonintegral", "integral", "word_impossible", "diagonal", "wrong_row", "unresolved")})
        for choice, values in order_numerators():
            numerator = tuple(a + b for a, b in zip(values, shift))
            if any(v % den for v in numerator):
                stats["nonintegral"] += 1
                continue
            stats["integral"] += 1
            mean = tuple(v // den for v in numerator[:3])
            stage, receipt = inspect_root(sigma, choice, mean)
            stats[stage] += 1
            if receipt:
                survivors.append({"sigma": ["".join(map(str, w)) for w in sigma],
                                  "choices": list(choice), "first_mean": list(mean),
                                  "stage": stage, "roots": receipt})
        totals.update(stats)
        all_rows.append({"sigma": ["".join(map(str, w)) for w in sigma], **stats})
    return {"scope": "fixed six-state period-two P,N; all literal source orders with M; not general C4/PSC",
            "M": m, "P": p, "N": n, "source_count": len(all_rows),
            "orders_per_source": len(order_numerators()),
            "case_count": len(all_rows) * len(order_numerators()),
            "inverse_denominator": den, "operator_determinant": prior.det_bareiss(operator),
            "totals": dict(totals), "by_source": all_rows,
            "first_word_survivors": survivors}


def test_complete_source_and_order_domains():
    assert len(sources()) == len(set(sources())) == 36
    assert len(order_numerators()) == 1296
    m, p, n, _, _, _, _, _, options = prior.packet()
    for sigma in sources():
        require_source(sigma)
        assert [[w.count(i) for w in sigma] for i in range(3)] == m
    assert prior.mm(p, n) == prior.mm(m, p)
    for j, rows in enumerate(options):
        assert len(rows) == len(set(rows))
        for row in rows:
            assert tuple(row.count(i) for i in range(6)) == tuple(n[i][j] for i in range(6))


def test_precomputed_order_contribution_matches_direct_equations():
    _, p, _, _, _, q, den, _, options = prior.packet()
    # Rebuild the complete RHS, rather than sharing the optimized split.
    for sigma in (sources()[0], prior.SIGMA, sources()[-1]):
        c = [[prior.area(sigma[j])[i] for j in range(3)] for i in range(3)]
        cp = prior.mm(c, p)
        negcp = [-cp[a][j] for j in range(6) for a in range(3)]
        shift = tuple(sum(q[i][k]*negcp[k] for k in range(18)) for i in range(18))
        for choice, numerator in order_numerators():
            rhs = [v for j, selected in enumerate(choice)
                   for v in prior.right_hand_column(p, cp, j, options[j][selected])]
            direct = tuple(sum(q[i][k]*rhs[k] for k in range(18)) for i in range(18))
            assert direct == tuple(x+y for x, y in zip(numerator, shift))
    assert den == 1694


def test_complete_46656_case_exclusion_and_conservation():
    result = census()
    assert result["case_count"] == 46656
    assert result["totals"] == {"nonintegral": 46466, "integral": 190,
                                "word_impossible": 176, "diagonal": 8,
                                "wrong_row": 6, "unresolved": 0}
    for row in result["by_source"]:
        assert row["nonintegral"] + row["integral"] == 1296
        assert sum(row[k] for k in ("word_impossible", "diagonal", "wrong_row", "unresolved")) == row["integral"]
    assert len(result["first_word_survivors"]) == 14
    for entry in result["first_word_survivors"]:
        assert len(entry["roots"]) == 1
        root = entry["roots"][0]
        assert not root["row_compatible"]
        assert root["child_masses"] != root["expected_child_masses"]


def test_old_case_reversal_symmetry_and_track_swap():
    result = census()
    rows = {tuple(r["sigma"]): r for r in result["by_source"]}
    old = rows[("01", "121", "012")]
    assert (old["nonintegral"], old["integral"], old["word_impossible"]) == (1291, 5, 5)
    for sigma, row in rows.items():
        reverse = rows[tuple(w[::-1] for w in sigma)]
        assert all(row[k] == reverse[k] for k in result["totals"])
    for item in result["first_word_survivors"]:
        sigma = tuple(tuple(map(int, w)) for w in item["sigma"])
        for root in item["roots"]:
            u, v = map(tuple, root["root"])
            top, bottom = inflate(sigma, u), inflate(sigma, v)
            assert factor(bottom, top) == tuple((b, a) for a, b in factor(top, bottom))


def test_literal_split_has_positive_and_negative_controls():
    assert factor((0, 1), (1, 0)) == (((0, 1), (1, 0)),)
    assert factor((0, 1, 2), (0, 2, 1)) == (((0,), (0,)), ((1, 2), (2, 1)))
    for u, v in (((3,), (3,)), ((-1,), (0,)), ((0,), (1,)), ((), ())):
        try:
            factor(u, v)
        except ValueError:
            pass
        else:
            raise AssertionError("invalid factor input admitted")
    for sigma in (((0,), (1,), (2,)), ((0, 1), (1, 3, 1), (0, 1, 2))):
        try:
            require_source(sigma)
        except ValueError:
            pass
        else:
            raise AssertionError("out-of-domain source admitted")


def test_committed_receipt_reconstructs_exactly():
    path = Path(__file__).resolve().parents[1] / "evidence/c4-incidence-order-class-2026-11-04/receipt.json"
    assert json.loads(path.read_text()) == census()


if __name__ == "__main__":
    print(json.dumps(census(), indent=2, sort_keys=True))

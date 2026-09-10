#!/usr/bin/env python3
"""Classify exact degree-3 catalogue output by symmetry, spectrum and leakage.

Reads D3_STATE_JSON lines from stdin (emitted by mojo/degree3_catalog.mojo) and
prints deterministic finite-corpus summary lines. This is analysis of finite
census output only, not a theorem about general PIP substitutions.
"""

from __future__ import annotations

import json
import sys
from itertools import permutations

PERMS = tuple(permutations((0, 1, 2)))


def image_words() -> list[tuple[int, ...]]:
    out: list[tuple[int, ...]] = []
    for a in range(3):
        out.append((a,))
    for a in range(3):
        for b in range(3):
            out.append((a, b))
    for a in range(3):
        for b in range(3):
            for c in range(3):
                out.append((a, b, c))
    return out


WORDS = image_words()


def normalize_state(state: tuple[tuple[int, ...], tuple[int, ...]]):
    u, v = state
    return min((u, v), (v, u))


def relabel_state(state, p):
    u, v = state
    return normalize_state((tuple(p[x] for x in u), tuple(p[x] for x in v)))


def canonical_state(state):
    return min(relabel_state(state, p) for p in PERMS)


def reverse_state(state):
    u, v = state
    return normalize_state((tuple(reversed(u)), tuple(reversed(v))))


def conjugate_sigma(sigma, p):
    inverse = [0, 0, 0]
    for old, new in enumerate(p):
        inverse[new] = old
    out = []
    for new_letter in range(3):
        old_letter = inverse[new_letter]
        out.append(tuple(p[x] for x in sigma[old_letter]))
    return tuple(out)


def canonical_sigma(sigma):
    return min(conjugate_sigma(sigma, p) for p in PERMS)


def reverse_sigma(sigma):
    return tuple(tuple(reversed(word)) for word in sigma)


def parse_state_key(key: str):
    left, right = key.strip().split("|")
    return normalize_state(
        (tuple(int(c) for c in left.strip()), tuple(int(c) for c in right.strip()))
    )


def state_key(state):
    return "".join(map(str, state[0])) + "|" + "".join(map(str, state[1]))


def sigma_key(sigma):
    return "/".join("".join(map(str, word)) for word in sigma)


def incidence(sigma):
    m = [[0] * 3 for _ in range(3)]
    for j, word in enumerate(sigma):
        for a in word:
            m[a][j] += 1
    return tuple(tuple(row) for row in m)


def matmul(a, b):
    return tuple(
        tuple(sum(a[i][k] * b[k][j] for k in range(3)) for j in range(3))
        for i in range(3)
    )


def trace(a):
    return sum(a[i][i] for i in range(3))


def det3(a):
    return (
        a[0][0] * (a[1][1] * a[2][2] - a[1][2] * a[2][1])
        - a[0][1] * (a[1][0] * a[2][2] - a[1][2] * a[2][0])
        + a[0][2] * (a[1][0] * a[2][1] - a[1][1] * a[2][0])
    )


def charpoly(a):
    tr = trace(a)
    tr2 = trace(matmul(a, a))
    return (-det3(a), (tr * tr - tr2) // 2, -tr, 1)


def n2(word):
    seen = [0, 0, 0]
    out = [0] * 9
    for b in word:
        for a in range(3):
            out[3 * a + b] += seen[a]
        seen[b] += 1
    return tuple(out)


def n3(word):
    seen = [0, 0, 0]
    pref2 = [0] * 9
    out = [0] * 27
    for c in word:
        for a in range(3):
            for b in range(3):
                out[9 * a + 3 * b + c] += pref2[3 * a + b]
        for a in range(3):
            pref2[3 * a + c] += seen[a]
        seen[c] += 1
    return tuple(out)


def k3(state):
    left = n3(state[0])
    right = n3(state[1])
    return tuple(x - y for x, y in zip(left, right))


def is_degree3(state):
    return n2(state[0]) == n2(state[1]) and n3(state[0]) != n3(state[1])


def epsilon(i, j, k):
    if len({i, j, k}) < 3:
        return 0
    inversions = int(i > j) + int(i > k) + int(j > k)
    return -1 if inversions % 2 else 1


def theta(defect):
    out = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            total = 0
            for k in range(3):
                for ell in range(3):
                    total += epsilon(j, k, ell) * defect[9 * i + 3 * k + ell]
            out[i][j] = total
    return tuple(tuple(row) for row in out)


def apply_substitution(sigma, word):
    out = []
    for a in word:
        out.extend(sigma[a])
    return tuple(out)


def coincidence_boundaries(u, v):
    pu = [0, 0, 0]
    pv = [0, 0, 0]
    out = [0]
    for index, (a, b) in enumerate(zip(u, v)):
        pu[a] += 1
        pv[b] += 1
        if pu == pv:
            out.append(index + 1)
    return out


def children(sigma, state):
    su = apply_substitution(sigma, state[0])
    sv = apply_substitution(sigma, state[1])
    boundaries = coincidence_boundaries(su, sv)
    out = []
    for lo, hi in zip(boundaries, boundaries[1:]):
        out.append(normalize_state((su[lo:hi], sv[lo:hi])))
    return tuple(out)


SEED0 = (
    (0, 1, 1, 2, 2, 0, 1),
    (1, 2, 0, 0, 1, 1, 2),
)
SEED_ORBIT = {relabel_state(SEED0, p) for p in PERMS}


def main() -> None:
    rows = []
    for line in sys.stdin:
        if not line.startswith("D3_STATE_JSON "):
            continue
        payload = json.loads(line[len("D3_STATE_JSON ") :])
        payload["state"] = payload["state"].strip()
        rows.append(payload)

    if not rows:
        raise SystemExit("no D3_STATE_JSON rows found")

    state_classes: dict[tuple, list[dict]] = {}
    sigma_classes: dict[tuple, list[dict]] = {}
    seed_matches = 0
    centralizer_hits = 0
    theta_absdet2 = 0
    theta_trace_sq6 = 0
    length9_single_d3_successor = 0
    length19_five_child_one_coincidence = 0
    productive_within_two = 0
    sigma_dets = set()
    sigma_charpolys = set()

    for row in rows:
        state = parse_state_key(row["state"])
        state_classes.setdefault(canonical_state(state), []).append(row)
        sigma = (WORDS[row["i"]], WORDS[row["j"]], WORDS[row["k"]])
        sigma_classes.setdefault(canonical_sigma(sigma), []).append(row)
        if state in SEED_ORBIT:
            seed_matches += 1

        m = incidence(sigma)
        sigma_dets.add(det3(m))
        sigma_charpolys.add(charpoly(m))
        a = theta(k3(state))
        if matmul(m, a) == matmul(a, m):
            centralizer_hits += 1
        if abs(det3(a)) == 2:
            theta_absdet2 += 1
        if trace(matmul(a, a)) == 6:
            theta_trace_sq6 += 1

        cs = children(sigma, state)
        direct_coincidences = sum(child[0] == child[1] for child in cs)
        if len(state[0]) == 9 and len(cs) == 1 and len(cs[0][0]) == 19 and is_degree3(cs[0]):
            length9_single_d3_successor += 1
        if len(state[0]) == 19 and len(cs) == 5 and direct_coincidences == 1:
            length19_five_child_one_coincidence += 1

        if direct_coincidences:
            productive_within_two += 1
        elif any(any(grand[0] == grand[1] for grand in children(sigma, child)) for child in cs):
            productive_within_two += 1

    state_keys = sorted(state_key(state) for state in state_classes)
    sigma_keys = sorted(sigma_key(sigma) for sigma in sigma_classes)
    lengths = sorted({len(parse_state_key(row["state"])[0]) for row in rows})

    state_reversal_closed = all(
        canonical_state(reverse_state(state)) in state_classes for state in state_classes
    )
    sigma_reversal_closed = all(
        canonical_sigma(reverse_sigma(sigma)) in sigma_classes for sigma in sigma_classes
    )

    print(f"DEGREE3_OCCURRENCES {len(rows)}")
    print(f"DEGREE3_STATE_RELABEL_CLASSES {len(state_classes)}")
    print(f"DEGREE3_SUBSTITUTION_CONJUGACY_CLASSES {len(sigma_classes)}")
    print("DEGREE3_LENGTHS " + ",".join(map(str, lengths)))
    print(f"DEGREE3_SEED_ORBIT_MATCHES {seed_matches}")
    print(f"DEGREE3_STATE_REVERSAL_CLOSED {int(state_reversal_closed)}")
    print(f"DEGREE3_SIGMA_REVERSAL_CLOSED {int(sigma_reversal_closed)}")
    print("DEGREE3_SIGMA_DET_VALUES " + ",".join(map(str, sorted(sigma_dets))))
    print(
        "DEGREE3_SIGMA_CHARPOLYS "
        + ";".join(",".join(map(str, poly)) for poly in sorted(sigma_charpolys))
    )
    print(f"DEGREE3_CENTRALIZER_HITS {centralizer_hits}")
    print(f"DEGREE3_THETA_ABSDET2 {theta_absdet2}")
    print(f"DEGREE3_THETA_TRACE_SQ6 {theta_trace_sq6}")
    print(f"DEGREE3_LENGTH9_SINGLE_D3_SUCCESSOR {length9_single_d3_successor}")
    print(
        "DEGREE3_LENGTH19_FIVE_CHILD_ONE_COINCIDENCE "
        f"{length19_five_child_one_coincidence}"
    )
    print(f"DEGREE3_PRODUCTIVE_WITHIN_TWO {productive_within_two}")
    for key in state_keys:
        print("DEGREE3_STATE_CLASS " + key)
    for key in sigma_keys:
        print("DEGREE3_SIGMA_CLASS " + key)


if __name__ == "__main__":
    main()

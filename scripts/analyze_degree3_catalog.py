#!/usr/bin/env python3
"""Classify exact degree-3 catalogue output by alphabet relabeling/reversal.

Reads D3_STATE_JSON lines from stdin (emitted by mojo/degree3_catalog.mojo) and
prints deterministic finite-corpus summary lines.  This is analysis of finite
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
    return normalize_state(
        (tuple(p[x] for x in u), tuple(p[x] for x in v))
    )


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

    for row in rows:
        state = parse_state_key(row["state"])
        state_classes.setdefault(canonical_state(state), []).append(row)
        sigma = (WORDS[row["i"]], WORDS[row["j"]], WORDS[row["k"]])
        sigma_classes.setdefault(canonical_sigma(sigma), []).append(row)
        if state in SEED_ORBIT:
            seed_matches += 1

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
    for key in state_keys:
        print("DEGREE3_STATE_CLASS " + key)
    for key in sigma_keys:
        print("DEGREE3_SIGMA_CLASS " + key)


if __name__ == "__main__":
    main()

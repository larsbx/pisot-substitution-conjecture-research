from __future__ import annotations

import argparse
import random
from psc_research import boundary_sync_hits, build_bpa, recurrent_noncoincident_sccs, scc_is_productive


def random_sigma(size: int, min_len: int, max_len: int, rng: random.Random) -> dict[int, tuple[int, ...]]:
    return {
        a: tuple(rng.randint(1, size) for _ in range(rng.randint(min_len, max_len)))
        for a in range(1, size + 1)
    }


def appears_primitive(sigma: dict[int, tuple[int, ...]], steps: int = 8) -> bool:
    size = len(sigma)
    for a in range(1, size + 1):
        seen = {a}
        frontier = [a]
        for _ in range(steps):
            nxt = []
            for x in frontier:
                nxt.extend(sigma[x])
            frontier = nxt
            seen.update(frontier)
        if len(seen) < size:
            return False
    return True


def main() -> None:
    parser = argparse.ArgumentParser(description="Random boundary-synchronization sweep")
    parser.add_argument("--trials", type=int, default=500)
    parser.add_argument("--seed", type=int, default=1729)
    parser.add_argument("--max-states", type=int, default=2000)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    primitive_like = 0
    recurrent_sccs = 0
    productive = 0
    caught = 0
    failures = []

    for _ in range(args.trials):
        size = rng.choice([3, 4])
        sigma = random_sigma(size, 2, 4, rng)
        if not appears_primitive(sigma):
            continue
        primitive_like += 1
        try:
            graph = build_bpa(sigma, max_states=args.max_states)
        except Exception:
            continue
        for comp in recurrent_noncoincident_sccs(graph):
            recurrent_sccs += 1
            is_prod = scc_is_productive(sigma, comp, max_iterate=1)
            has_bsl = bool(boundary_sync_hits(sigma, comp, max_iterate=1))
            productive += int(is_prod)
            caught += int(has_bsl)
            if is_prod and not has_bsl:
                failures.append((sigma, comp))

    print(f"primitive-like specimens: {primitive_like}")
    print(f"recurrent noncoincident SCCs: {recurrent_sccs}")
    print(f"productive@1: {productive}")
    print(f"BSL caught@1: {caught}")
    print(f"productive but missed: {len(failures)}")
    if failures:
        sigma, comp = failures[0]
        print("first failure sigma:", sigma)
        print("first failure SCC size:", len(comp))


if __name__ == "__main__":
    main()

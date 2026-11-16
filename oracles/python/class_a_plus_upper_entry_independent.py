"""Exact finite calibration for the written upper all-source entry theorem.

The selector implements the written index cases. The verifier independently
counts prefixes at absolute positions of the original inflated words.
"""
import argparse
from collections import Counter
import json

from class_a_plus_upper_recurrence_independent import (
    LiteralMember, NoVerdict, add, emit, packet, replay, scale, subtract, vector,
)

X, C, Y = range(3)
ZERO = (0, 0, 0)
F = (X, C, X)
G = (X, X, C)
UNIT = tuple(tuple(int(i == j) for i in range(3)) for j in range(3))
STEP_CAP = 128
REFINEMENT_CAP = 512
PARAMETERS = tuple((n, J) for n in (7, 8, 12, 31) for J in (1, 2, 3, 4, 5, n+7))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reverse(source):
    a, b, *w = source
    return (b, a, *scale(-1, w))


def shift(source):
    return source[2:]


def multiply(member, w):
    p, q, r = w
    return (2*p+q+r, q+r, (member.n+member.d)*p+member.n*q+(member.n+1)*r)


def choose(member, source):
    """Return a literal pair, its case, and the full child before replay."""
    reversed_tracks = member.sign(shift(source)) < 0
    a, b, *w = reverse(source) if reversed_tracks else source
    run = (member.n+member.d, member.n, member.n+1)
    top_last, bottom_first = G[a], F[b]
    G_a, F_b = UNIT[top_last], UNIT[bottom_first]
    E = add(G_a, F_b)
    D = multiply(member, subtract(UNIT[a], w))

    def sign(w):
        return member.sign(w)

    def above_direct_threshold(top, bottom, margin):
        wall = add(UNIT[G[top]], UNIT[F[bottom]])
        doubled = scale(2, subtract(multiply(member, margin), wall))
        return sign(subtract(doubled, UNIT[Y])) > 0

    if above_direct_threshold(a, b, subtract(UNIT[a], w)):
        total = add(multiply(member, w), subtract(UNIT[F[b]], UNIT[F[a]]))
        for e in range(1-run[b], run[a]):
            error = scale(2, subtract(total, scale(e, UNIT[Y])))
            if sign(add(error, UNIT[Y])) > 0 and sign(subtract(error, UNIT[Y])) < 0:
                i, j = 1+max(e, 0), 1+max(-e, 0)
                p = add(UNIT[F[a]], scale(i-1, UNIT[Y]))
                q = add(UNIT[F[b]], scale(j-1, UNIT[Y]))
                next_source = (Y, Y, *add(multiply(member, w), subtract(q, p)))
                case = "direct"
                break
        else:
            raise ValueError("strict nearest gap absent in the literal RUN range")
    else:
        first_prefix = UNIT[F[a]]
        if sign(subtract(D, G_a)) <= 0:
            i, j = run[a]+1, 0
            child_a, child_b, q = top_last, bottom_first, ZERO
            case = "growth"
        elif sign(subtract(D, E)) >= 0:
            i, j = run[a]+1, 1
            child_a, child_b, q = top_last, Y, F_b
            case = "last_first_run"
        elif above_direct_threshold(bottom_first, top_last, subtract(E, D)):
            i, j = run[a]+1, 0
            child_a, child_b, q = top_last, bottom_first, ZERO
            case = "reverse_last_first"
        else:
            i, j = run[a], 0
            child_a, child_b, q = Y, bottom_first, ZERO
            case = "last_run_first"
        p = add(first_prefix, scale(i-1, UNIT[Y]))
        next_source = (child_a, child_b, *add(multiply(member, w), subtract(q, p)))

    if reversed_tracks:
        return (j, i), case, reverse(next_source)
    return (i, j), case, next_source


def construct(member, source):
    steps = []
    while not member.central(source):
        if len(steps) >= STEP_CAP:
            raise NoVerdict("entry path cap exhausted")
        indices, case, source = choose(member, source)
        steps.append((indices, case, source))
    return steps


def original_mark(member, root, indices, columns_by_depth):
    """Independently locate the mark by its absolute ordinal at this depth."""
    position = 0
    current = root
    for depth, i in zip(range(len(indices)-1, -1, -1), indices):
        word = member.words[current]
        require(0 <= i < len(word), "illegal marked index")
        position += sum(sum(columns_by_depth[depth][letter]) for letter in word[:i])
        current = word[i]
    expected_letter = current

    prefix = ZERO
    current = root
    for depth in range(len(indices)-1, -1, -1):
        for letter in member.words[current]:
            block = columns_by_depth[depth][letter]
            size = sum(block)
            if position < size:
                current = letter
                break
            prefix = add(prefix, block)
            position -= size
        else:
            raise ValueError("mark ordinal outside original word")
    require(position == 0 and current == expected_letter, "wrong original mark")
    return current, prefix


def verify_path(member, source, steps, expected_final):
    a, b, *w = packet(source)
    require(member.strict(source), "source is not strict")
    P = Q = ZERO
    columns_by_depth = [UNIT]
    top, bottom = [], []
    current, inflated = source, tuple(w)
    for indices, _, claimed in steps:
        actual, p, q = member.step(current, indices)
        require(actual == claimed, "wrong literal target")
        require(member.strict(actual), "literal target is not strict")
        P, Q = add(member.incidence(P), p), add(member.incidence(Q), q)
        inflated = member.incidence(inflated)
        require(shift(actual) == add(inflated, subtract(Q, P)), "wrong prefix identity")
        top.append(indices[0])
        bottom.append(indices[1])
        prev = columns_by_depth[-1]
        columns_by_depth.append(tuple(
            tuple(sum(prev[letter][i] for letter in word) for i in range(3))
            for word in member.words
        ))
        require(original_mark(member, a, top, columns_by_depth) == (actual[0], P),
                "wrong original top prefix")
        require(original_mark(member, b, bottom, columns_by_depth) == (actual[1], Q),
                "wrong original bottom prefix")
        current = actual
    require(current == expected_final, "wrong endpoint")
    return P, Q


def source_bound(member, source):
    a, _, *w = reverse(source) if member.sign(shift(source)) < 0 else source
    margin = subtract(UNIT[a], w)
    for k in range(1, STEP_CAP):
        margin = member.incidence(margin)
        if member.sign(subtract(margin, scale(4, UNIT[Y]))) >= 0:
            return k+1
    raise NoVerdict("bound calibration cap exhausted")


def sources(member):
    found = set()
    for p in range(-3, 4):
        for q in range(-3, 4):
            center = member.central_r(p, q)
            for r in range(center-4, center+5):
                for a in range(3):
                    for b in range(3):
                        source = (a, b, p, q, r)
                        if member.strict(source):
                            found.add(source)
    if member.J == member.n+7:
        # On this face β−(n+4)=2/β². Its powers supply exact near-wall
        # offsets with arbitrarily many forced boundary steps as the power grows.
        margin = UNIT[Y]
        for exponent in range(1, 21):
            margin = subtract(member.incidence(margin), scale(member.n+4, margin))
            if exponent in (1, 2, 4, 8, 12, 20):
                for a in range(3):
                    for b in range(3):
                        source = (a, b, *subtract(UNIT[a], margin))
                        found.update((source, reverse(source)))
    return sorted(found)


def controls(member):
    source = (Y, C, 0, 1, 0)
    steps = construct(member, source)
    first, second = steps
    require(first[0] == (member.n+2, 0) and second[0] == (1, 2)
            and second[-1] == (Y, Y, *ZERO), "two-edge control changed")
    a, b = source[:2]
    for i in range(len(member.words[a])):
        for j in range(len(member.words[b])):
            actual, _, _ = member.step(source, (i, j))
            require(not member.central(actual), "unexpected one-edge central child")
    fake = [
        [((member.n+1, 0), *first[1:]), second],
        [(first[0], first[1], (C, C, 0, 2, -1)), second],
        [first],
    ]
    for counterfeit in fake:
        try:
            verify_path(member, source, counterfeit, (Y, Y, *ZERO))
        except ValueError:
            continue
        raise ValueError("damaged certificate accepted")
    touching_source = (Y, Y, *ZERO)
    touching, _, _ = member.step(touching_source, (1, 2))
    try:
        verify_path(member, touching_source, [((1, 2), "control", touching)], touching)
    except ValueError as error:
        require(str(error) == "literal target is not strict", "wrong touching-target rejection")
    else:
        raise ValueError("touching child was accepted")
    return len(fake)+1


def read_native(path):
    rows = {}
    with open(path, encoding="utf-8") as stream:
        for line in stream:
            if not line.startswith("PLUS_UPPER_ENTRY "):
                continue
            n, J, a, b, p, q, r, depth, *values = map(int, line.split()[1:])
            key = (n, J, (a, b, p, q, r))
            require(key not in rows, "duplicate native source")
            require(0 <= depth <= STEP_CAP and len(values) == 7*depth,
                    "invalid native step count")
            rows[key] = [(tuple(values[i:i+2]), tuple(values[i+2:i+7]))
                         for i in range(0, len(values), 7)]
    return rows


def certify(output=None, native=None):
    totals = Counter()
    cases = Counter()
    max_depth = 0
    for n, J in PARAMETERS:
        member = LiteralMember(n, J, refinement_cap=REFINEMENT_CAP)
        totals["negative_controls"] += controls(member)
        for source in sources(member):
            steps = construct(member, source)
            endpoint = steps[-1][-1] if steps else source
            require(member.central(endpoint), "endpoint is not central")
            require(len(steps) <= source_bound(member, source), "entry bound exceeded")
            P, Q = verify_path(member, source, steps, endpoint)
            max_depth = max(max_depth, len(steps))
            totals["sources"] += 1
            totals["entry_edges"] += len(steps)
            cases.update(case for _, case, _ in steps)
            if native is not None and max(abs(source[2]), abs(source[3])) <= 3:
                require(native.pop((n, J, source), None) ==
                        [(indices, target) for indices, _, target in steps],
                        "missing or mismatched native literal path")
                totals["native_paths_matched"] += 1

            # Use moderate vectors for a separate end-to-end composition check.
            # The near-wall controls can have very large initial coordinates.
            if max(map(abs, source[2:])) <= 24 and all(abs(x) <= 12 for x in endpoint[2:]):
                record = emit(member, endpoint)
                replay(member, record)
                suffix = [(tuple(edge["indices"]), "central", tuple(edge["target"]))
                          for edge in record["steps"]]
                verify_path(member, source, steps+suffix, (Y, Y, *ZERO))
                totals["composed_to_zero"] += 1
            if output:
                output.write(json.dumps({"n": n, "J": J, "source": source, "steps": steps,
                                         "top_prefix": P, "bottom_prefix": Q})+"\n")

    require(not native, "unexpected native rows")
    require(set(cases) == {"direct", "growth", "last_first_run",
                           "reverse_last_first", "last_run_first"}, "entry case was untested")
    return {"members": len(PARAMETERS), **totals, "maximum_entry_depth": max_depth,
            "selector_cases": dict(cases), "step_cap": STEP_CAP,
            "refinement_cap": REFINEMENT_CAP}


def replay_transcripts(path):
    members = {(n, J): LiteralMember(n, J, refinement_cap=REFINEMENT_CAP)
               for n, J in PARAMETERS}
    remaining = {key: set(sources(member)) for key, member in members.items()}
    totals = Counter()
    with open(path, encoding="utf-8") as stream:
        for line in stream:
            record = json.loads(line)
            key = (record["n"], record["J"])
            require(all(type(value) is int for value in key), "invalid parameter identity")
            source = packet(record["source"])
            require(key in members and source in remaining[key], "unexpected transcript source")
            remaining[key].remove(source)
            member = members[key]
            steps = [(tuple(indices), case, packet(target))
                     for indices, case, target in record["steps"]]
            require(len(steps) <= STEP_CAP and len(steps) <= source_bound(member, source),
                    "entry bound exceeded")
            endpoint = steps[-1][-1] if steps else source
            require(member.central(endpoint), "endpoint is not central")
            P, Q = verify_path(member, source, steps, endpoint)
            require((P, Q) == (vector(record["top_prefix"]), vector(record["bottom_prefix"])),
                    "wrong supplied original prefix")
            totals["sources"] += 1
            totals["entry_edges"] += len(steps)
    require(not any(remaining.values()), "missing transcript sources")
    return dict(totals)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", help="optional native --emit transcript for exact comparison")
    paths = parser.add_mutually_exclusive_group()
    paths.add_argument("--transcripts", help="new JSONL path for full entry certificates")
    paths.add_argument("--replay-transcripts", help="verify an existing full JSONL transcript")
    args = parser.parse_args()
    native = read_native(args.native) if args.native else None
    if args.replay_transcripts:
        if args.native:
            parser.error("--native compares against freshly constructed paths")
        result = replay_transcripts(args.replay_transcripts)
    elif args.transcripts:
        with open(args.transcripts, "x", encoding="utf-8") as output:
            result = certify(output, native)
    else:
        result = certify(native=native)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()

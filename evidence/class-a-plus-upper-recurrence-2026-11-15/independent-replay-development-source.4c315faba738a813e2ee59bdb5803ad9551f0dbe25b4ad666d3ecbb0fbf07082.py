"""Independent exact finite replay of upper central-source occurrence paths.

This oracle imports no PSC arithmetic, native selector, or path implementation.
It expands the literal words, counts their prefixes, and uses Fraction root
enclosures to decide quadratic signs.  Nearest gaps are found by a linear
scan.  Every accepted path retains all typed integral states and original
prefix identities.  The fixed source grid is finite evidence, not the proof
of the unbounded central-source theorem, and does not cover arbitrary entry.

Root refinement, literal allocation, and path length have explicit caps.
Their exhaustion raises NoVerdict and is never an acceptance.  An evidence
directory must be new or empty; archived output is never overwritten.
"""
from __future__ import annotations

import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import platform
import sys

N_VALUES = (7, 8, 12, 31)
REFINEMENT_CAP = 256
WORD_OCCURRENCE_CAP = 50_000
STEP_CAP = 256
DENOMINATOR = (0, 1, 1)  # beta*(beta+1)>0, ascending coefficients.


class NoVerdict(RuntimeError):
    """An explicitly inconclusive resource refusal."""


def vector(value):
    result = tuple(value)
    if len(result) != 3 or any(type(x) is not int for x in result):
        raise ValueError("a complete three-integer vector is required")
    return result


def packet(value):
    result = tuple(value)
    if (len(result) != 5 or any(type(x) is not int for x in result)
            or result[0] not in range(3) or result[1] not in range(3)):
        raise ValueError("a typed complete integral packet is required")
    return result


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def subtract(a, b):
    return tuple(x-y for x, y in zip(a, b))


def scale(k, a):
    return tuple(k*x for x in a)


def zero(source):
    return packet(source)[2:] == (0, 0, 0)


def cycle_height(source):
    a, b, p, q, r = packet(source)
    return p if (a, b) == (2, 2) and (q, r) == (3*p, -6*p) else None


class LiteralMember:
    """The actual upper word geometry and a capped rational sign oracle."""

    def __init__(self, n, J, *, refinement_cap=REFINEMENT_CAP,
                 word_cap=WORD_OCCURRENCE_CAP):
        if (type(n) is not int or type(J) is not int or n < 7
                or not 1 <= J <= n+7):
            raise ValueError("the upper family requires n>=7 and 1<=J<=n+7")
        if (type(refinement_cap) is not int or refinement_cap < 0
                or type(word_cap) is not int or word_cap < 0):
            raise ValueError("resource caps must be nonnegative integers")
        self.n, self.J = n, J
        self.d = 2*n+12-J
        occurrences = 3*n+self.d+7
        if occurrences > word_cap:
            raise NoVerdict("literal word occurrence cap exhausted")
        self.refinement_cap, self.refinements = refinement_cap, 0
        self.lo, self.hi = Fraction(n+4), Fraction(n+6)
        if not self.polynomial(self.lo) < 0 < self.polynomial(self.hi):
            raise ValueError("the literal cubic fails its strict root bracket")
        if n*n+7*n+9+J <= 0:
            raise ValueError("the exact derivative lower bound is unavailable")
        if any(self.polynomial(Fraction(r)) == 0 for r in (1, -1, 2, -2)):
            raise ValueError("the family cubic is not irreducible by its rational-root test")
        self.words = ((0,)+(2,)*(n+self.d)+(0,),
                      (1,)+(2,)*n+(0,),
                      (0,)+(2,)*(n+1)+(1,))
        self.prefixes, self.columns = [], []
        for word in self.words:
            count, prefixes = [0, 0, 0], []
            for letter in word:
                prefixes.append(tuple(count))
                count[letter] += 1
            self.prefixes.append(tuple(prefixes))
            self.columns.append(tuple(count))
        if sum(map(len, self.words)) != occurrences:
            raise ValueError("the complete literal occurrence count changed")
        if tuple(self.columns) != ((2, 0, n+self.d), (1, 1, n), (1, 1, n+1)):
            raise ValueError("actual literal Parikh columns do not match the member")
        self.sign_cache = {}
        lengths = ((3, 6-J, 3), (-1, 0, 1), DENOMINATOR)
        for parent, counts in enumerate(self.columns):
            actual = tuple(sum(counts[a]*lengths[a][k] for a in range(3))
                           for k in range(3))
            if actual != self.multiply_beta(lengths[parent]):
                raise ValueError("actual word counts fail exact eigenlength scaling")
            if self.sign_numerator(lengths[parent]) <= 0:
                raise ValueError("a literal eigenlength is not positive")

    def polynomial(self, x):
        return x**3-(self.n+4)*x*x+(self.J-self.n-7)*x-2

    def multiply_beta(self, coefficients):
        a, b, c = vector(coefficients)
        return (2*c, a-(self.J-self.n-7)*c, b+(self.n+4)*c)

    def refine(self):
        if self.refinements >= self.refinement_cap:
            raise NoVerdict("exact root refinement cap exhausted")
        middle = (self.lo+self.hi)/2
        value = self.polynomial(middle)
        if value == 0:
            raise ValueError("unexpected rational upper root")
        if value > 0:
            self.hi = middle
        else:
            self.lo = middle
        self.refinements += 1
        if not self.polynomial(self.lo) < 0 < self.polynomial(self.hi):
            raise ValueError("bisection lost its strict root bracket")

    def sign_numerator(self, coefficients):
        coefficients = vector(coefficients)
        if coefficients == (0, 0, 0):
            return 0
        if coefficients in self.sign_cache:
            return self.sign_cache[coefficients]
        while True:
            low = high = Fraction(0)
            for degree, coefficient in enumerate(coefficients):
                lo_power, hi_power = self.lo**degree, self.hi**degree
                if coefficient >= 0:
                    low += coefficient*lo_power
                    high += coefficient*hi_power
                else:
                    low += coefficient*hi_power
                    high += coefficient*lo_power
            if low > 0 or high < 0:
                result = 1 if low > 0 else -1
                self.sign_cache[coefficients] = result
                return result
            self.refine()

    def numerator(self, w):
        p, q, r = vector(w)
        a, b = 3*p+q+r, 3*p-q
        return (b, a+b-self.J*p, a)

    def sign(self, w):
        return self.sign_numerator(self.numerator(w))

    def incidence(self, w):
        w = vector(w)
        return tuple(sum(self.columns[column][row]*w[column]
                         for column in range(3)) for row in range(3))

    def strict(self, source):
        a, b, *w = packet(source)
        upper = tuple(x-(i == a) for i, x in enumerate(w))
        lower = tuple(x+(i == b) for i, x in enumerate(w))
        return self.sign(upper) < 0 and self.sign(lower) > 0

    def central(self, source):
        source = packet(source)
        if source[:2] != (2, 2):
            return False
        twice = scale(2, self.numerator(source[2:]))
        return (self.sign_numerator(subtract(twice, DENOMINATOR)) < 0
                and self.sign_numerator(add(twice, DENOMINATOR)) > 0)

    def central_r(self, p, q):
        if type(p) is not int or type(q) is not int:
            raise ValueError("central coordinates must be integers")
        reserve = 4*abs(p)+abs(q)+1
        found = [r for r in range(-reserve, reserve+1)
                 if self.central((2, 2, p, q, r))]
        if len(found) != 1:
            raise ValueError("no unique central third coordinate in the exact search")
        return found[0]

    def nearest_gap(self, source):
        if not self.central(source):
            raise ValueError("nearest RUN selection requires a central y/y packet")
        twice = scale(2, self.multiply_beta(self.numerator(packet(source)[2:])))
        found = []
        for e in range(-self.n, self.n+1):
            lower = subtract(twice, scale(2*e-1, DENOMINATOR))
            upper = subtract(twice, scale(2*e+1, DENOMINATOR))
            if self.sign_numerator(lower) > 0 and self.sign_numerator(upper) < 0:
                found.append(e)
        if len(found) != 1:
            raise ValueError("nearest gap is absent, tied, or nonunique")
        if abs(found[0]) > self.n-1:
            raise ValueError("the sharper literal RUN gap bound failed")
        return found[0]

    def step(self, source, indices):
        a, b, *w = packet(source)
        indices = tuple(indices)
        if len(indices) != 2 or any(type(x) is not int for x in indices):
            raise ValueError("two integer original indices are required")
        i, j = indices
        if i < 0 or j < 0 or i >= len(self.words[a]) or j >= len(self.words[b]):
            raise ValueError("illegal original index")
        p, q = self.prefixes[a][i], self.prefixes[b][j]
        target = add(self.incidence(w), subtract(q, p))
        return (self.words[a][i], self.words[b][j], *target), p, q


def initial_reserve(member, source):
    a, b, p, q, r = packet(source)
    if (a, b) != (2, 2):
        raise ValueError("source letters must be y/y")
    return (member.n+7)*(abs(p)+abs(2*p+q+r)+1)


def check_reserve(member, source, B):
    _, _, p, q, r = packet(source)
    next_first = 2*p+q+r
    second = 2*next_first+p if member.J <= 4 else next_first
    if abs(p) > B or abs(second) > B:
        raise ValueError("the bounded two-coordinate invariant failed")


def check_reconstruction(member, source, target):
    source, target = packet(source), packet(target)
    if source[:2] != (2, 2) or target[:2] != (2, 2):
        raise ValueError("nearest RUN reconstruction changed its letters")
    a, b = source[2], target[2]
    c = 2*target[2]+target[3]+target[4]
    if b != 2*source[2]+source[3]+source[4]:
        raise ValueError("the original next-first-coordinate identity failed")
    if target[2:] != (b, b-2*a, c-3*b+2*a):
        raise ValueError("the full next-packet reconstruction failed")
    # Numerator of c+C*b+A*a, reduced against the independently bound cubic.
    expected = (2*(a+b), 2*a+(3-member.J)*b+c, b+c)
    if member.numerator(target[2:]) != expected:
        raise ValueError("the scalar recurrence lost a complete physical coordinate")
    if not member.central(target):
        raise ValueError("nearest RUN did not preserve strict centrality")


def cycle_schedule(member, signed_height):
    if type(signed_height) is not int or signed_height == 0:
        raise ValueError("a nonzero signed cycle height is required")
    H, J = abs(signed_height), member.J
    source = (2, 2, H, 3*H, -6*H)
    if not member.central(source):
        raise ValueError("cycle amplitude is not strictly central")
    if J*H > member.n-1:
        raise ValueError("the literal amplitude index bound failed")
    indices = []
    while J*H >= 3:
        indices.extend(((0, J*H-2), (J*(H-1)+4, 1)))
        H -= 1
    if H:
        if J == 1 and H in (1, 2):
            indices.extend(((0, 0), (1, 1+(member.n+4)*H), (1, 2*H+1)))
        elif (J, H) == (2, 1):
            indices.extend(((0, 0), (0, 2*member.n+6), (1, 2)))
        else:
            raise ValueError("the general cycle descent reached an uncovered base")
    return [pair[::-1] for pair in indices] if signed_height < 0 else indices


def emit(member, source, *, step_cap=STEP_CAP):
    source = packet(source)
    if type(step_cap) is not int or step_cap < 0:
        raise ValueError("the path cap must be a nonnegative integer")
    if not member.central(source):
        raise ValueError("source is not a strictly central integral y/y packet")
    record = dict(n=member.n, J=member.J, source=source,
                  B=initial_reserve(member, source), central_depth=0, steps=[])

    def append(indices):
        nonlocal source
        if len(record['steps']) >= step_cap:
            raise NoVerdict("literal path step cap exhausted")
        target, p, q = member.step(source, indices)
        record['steps'].append(dict(source=source, indices=indices, target=target,
                                   top_prefix=p, bottom_prefix=q))
        source = target

    while cycle_height(source) is None:
        check_reserve(member, source, record['B'])
        e = member.nearest_gap(source)
        append((1+max(e, 0), 1+max(-e, 0)))
        record['central_depth'] += 1
    if not zero(source):
        for indices in cycle_schedule(member, cycle_height(source)):
            append(indices)
    return record


def replay(member, record):
    if (type(record['n']) is not int or type(record['J']) is not int
            or record['n'] != member.n or record['J'] != member.J):
        raise ValueError("record is bound to different upper parameters")
    source = packet(record['source'])
    if not member.central(source):
        raise ValueError("source is not a strictly central integral y/y packet")
    central_depth, B = record['central_depth'], record['B']
    if (type(central_depth) is not int or not 0 <= central_depth <= len(record['steps'])
            or type(B) is not int or B != initial_reserve(member, source)):
        raise ValueError("invalid central cutoff or both-coordinate reserve")
    P = Q = (0, 0, 0)
    power = source[2:]
    check_reserve(member, source, B)
    terminal = zero(source)
    for index, edge in enumerate(record['steps']):
        if terminal:
            raise ValueError("continued the first integral zero")
        if packet(edge['source']) != source:
            raise ValueError("noncomposable full middle packet")
        if index < central_depth:
            if cycle_height(source) is not None:
                raise ValueError("nearest phase continued beyond its first cycle packet")
            e = member.nearest_gap(source)
            if tuple(edge['indices']) != (1+max(e, 0), 1+max(-e, 0)):
                raise ValueError("wrong unique nearest original RUN choice")
        elif index == central_depth:
            if cycle_height(source) is None or not member.central(source):
                raise ValueError("cycle cutoff is not the full strictly central W packet")
        target, p, q = member.step(source, edge['indices'])
        if packet(edge['target']) != target:
            raise ValueError("wrong child letters or complete integral offset")
        if vector(edge['top_prefix']) != p or vector(edge['bottom_prefix']) != q:
            raise ValueError("false original local occurrence prefix")
        if not member.strict(source) or not member.strict(target):
            raise ValueError("a literal edge is not strict")
        if index < central_depth:
            check_reconstruction(member, source, target)
            check_reserve(member, target, B)
        P, Q = add(member.incidence(P), p), add(member.incidence(Q), q)
        power = member.incidence(power)
        if target[2:] != add(power, subtract(Q, P)):
            raise ValueError("false composed original prefix identity")
        source = target
        terminal = zero(source)
        if terminal and source[0] != source[1]:
            raise ValueError("the first integral zero is not a typed coincidence")
    if not terminal or source[:2] != (2, 2):
        raise ValueError("incomplete central-source path to y/y zero")
    if power != subtract(P, Q):
        raise ValueError("false final original prefix identity")
    if central_depth == 0 and not record['steps'] and not zero(record['source']):
        raise ValueError("nonzero source cannot have an empty accepted path")
    return dict(P=P, Q=Q, M_power_source=power, depth=len(record['steps']),
                central_depth=central_depth, B=B)


def source_grid():
    """The exact finite declared source set, independently regenerated."""
    sources = set()
    for n in N_VALUES:
        for J in (1, 2, 3, 4, 5, n+7):
            member = LiteralMember(n, J)
            for p in range(-2, 3):
                for q in range(-2, 3):
                    sources.add((n, J, p, q, member.central_r(p, q)))
            for H in range(1, n):
                if member.central((2, 2, H, 3*H, -6*H)):
                    for orientation in (-1, 1):
                        sources.add((n, J, orientation*H, orientation*3*H,
                                     -orientation*6*H))
            for p, q in ((100, -83), (-100, 83)):
                sources.add((n, J, p, q, member.central_r(p, q)))
    return tuple(sorted(sources))


def negative_controls():
    member = LiteralMember(7, 1)
    source = (2, 2, 100, -83, member.central_r(100, -83))
    good = emit(member, source)
    replay(member, good)  # Baseline outside every expected-rejection handler.
    if good['central_depth'] < 2:
        raise AssertionError("central countercontrol fixture lost its transient")
    mutants = {}
    bad = copy.deepcopy(good)
    bad['steps'][0]['target'] = (2, 1, *bad['steps'][0]['target'][2:])
    mutants['wrong_child_type'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['indices'] = (-1, 1)
    mutants['negative_index'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['indices'] = (1, member.n+3)
    mutants['past_last_index'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['indices'] = (1, member.n+2)
    mutants['last_c_relabelled_run_y'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['target'] = (2, 2, 0, 0, 0)
    mutants['false_coincidence'] = bad
    bad = copy.deepcopy(good)
    target = list(bad['steps'][0]['target'])
    target[3] += 1
    bad['steps'][0]['target'] = target
    mutants['omitted_middle_coordinate'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][1]['source'] = (2, 2, 0, 0, 0)
    mutants['noncomposable_middle'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['bottom_prefix'] = (1, 0, -1)
    mutants['false_original_prefix'] = bad
    bad = copy.deepcopy(good)
    bad['steps'] = bad['steps'][:-1]
    mutants['truncated_nonzero_path'] = bad
    bad = copy.deepcopy(good)
    bad['central_depth'] -= 1
    mutants['premature_full_packet_reconstruction'] = bad
    bad = copy.deepcopy(good)
    bad['central_depth'] += 1
    mutants['continued_nearest_cycle'] = bad
    bad = copy.deepcopy(good)
    bad['B'] = (member.n+7)*(abs(source[2])+1)
    mutants['dropped_second_initial_coordinate'] = bad
    bad = copy.deepcopy(good)
    bad['J'] = 2
    mutants['wrong_member_parameters'] = bad
    bad = copy.deepcopy(good)
    last = packet(good['steps'][-1]['target'])
    target, p, q = member.step(last, (1, 1))
    bad['steps'].append(dict(source=last, indices=(1, 1), target=target,
                            top_prefix=p, bottom_prefix=q))
    mutants['continued_first_zero'] = bad
    bad = copy.deepcopy(good)
    bad['source'] = (0, 2, *source[2:])
    mutants['arbitrary_type_masquerading_as_central'] = bad
    rejected = {}
    for name, bad in mutants.items():
        try:
            replay(member, bad)
        except ValueError as error:
            rejected[name] = str(error)
        else:
            raise AssertionError(f"accepted invalid central path: {name}")
    refusals = {}
    for name, operation in (
            ('word_occurrences', lambda: LiteralMember(7, 1, word_cap=1)),
            ('root_refinement', lambda: LiteralMember(7, 1, refinement_cap=0)
             .sign_numerator((-12, 1, 0))),
            ('path_steps', lambda: emit(member, source, step_cap=0))):
        try:
            operation()
        except NoVerdict as error:
            refusals[name] = str(error)
        else:
            raise AssertionError(f"failed to refuse exhausted resource: {name}")
    return rejected, refusals


def certify(output_dir):
    output_dir = Path(output_dir)
    if output_dir.exists() and any(output_dir.iterdir()):
        raise ValueError("output directory is not empty; historical evidence preserved")
    output_dir.mkdir(parents=True, exist_ok=True)
    source_bytes = Path(__file__).resolve().read_bytes()
    source_digest = hashlib.sha256(source_bytes).hexdigest()
    source_name = f'class_a_plus_upper_recurrence_independent.{source_digest}.py'
    (output_dir/source_name).write_bytes(source_bytes)
    sources = source_grid()
    paths = edges = central_edges = maximum_depth = maximum_central_depth = 0
    maximum_prefix = maximum_refinements = maximum_B = 0
    large_source_depths, member_counts = [], {}
    transcript_digest = hashlib.sha256()
    cached_member = None
    with (output_dir/'exact-transcripts.jsonl').open('w') as stream:
        for n, J, p, q, r in sources:
            if cached_member is None or (cached_member.n, cached_member.J) != (n, J):
                cached_member = LiteralMember(n, J)
            member = cached_member
            record = emit(member, (2, 2, p, q, r))
            record['result'] = replay(member, record)
            line = json.dumps(record, separators=(',', ':'), sort_keys=True)+'\n'
            stream.write(line)
            transcript_digest.update(line.encode())
            paths += 1
            edges += len(record['steps'])
            central_edges += record['central_depth']
            maximum_depth = max(maximum_depth, len(record['steps']))
            maximum_central_depth = max(maximum_central_depth, record['central_depth'])
            maximum_prefix = max(maximum_prefix,
                *(abs(x) for key in ('P', 'Q', 'M_power_source')
                  for x in record['result'][key]))
            maximum_refinements = max(maximum_refinements, member.refinements)
            maximum_B = max(maximum_B, record['B'])
            key = f'{n},{J}'
            member_counts[key] = member_counts.get(key, 0)+1
            if abs(p) == 100:
                large_source_depths.append(dict(n=n, J=J, p=p, q=q, r=r,
                    central_depth=record['central_depth'], depth=len(record['steps']),
                    prefix_decimal_digits=len(str(max(map(abs, record['result']['P']+
                                                          record['result']['Q']))))))
    if paths != len(sources):
        raise AssertionError("the independent declared source set was not exhausted")
    rejected, refusals = negative_controls()
    summary = dict(
        status='accepted_finite_replay',
        scope='finite central integral y/y source paths only; no arbitrary-entry or universal BH claim',
        source_file='oracles/python/class_a_plus_upper_recurrence_independent.py',
        source_sha256=source_digest, immutable_source_snapshot=source_name,
        python_version=platform.python_version(), n_values=N_VALUES,
        source_grid='J in {1,2,3,4,5,n+7}; p,q in -2..2 with exact central r; all admissible signed W_H; pairs (100,-83),(-100,83)',
        source_set_sha256=hashlib.sha256(json.dumps(sources, separators=(',', ':')).encode()).hexdigest(),
        member_counts=member_counts, paths=paths, edges=edges, central_edges=central_edges,
        maximum_depth=maximum_depth, maximum_central_depth=maximum_central_depth,
        largest_absolute_prefix_coordinate=maximum_prefix, maximum_initial_reserve=maximum_B,
        refinement_cap=REFINEMENT_CAP, maximum_refinements=maximum_refinements,
        word_occurrence_cap=WORD_OCCURRENCE_CAP, step_cap=STEP_CAP,
        transcripts_sha256=transcript_digest.hexdigest(),
        rejected_mutations=rejected, resource_refusals=refusals,
        large_source_depths=large_source_depths,
        all_source_entry=False, universal_BH=False)
    (output_dir/'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True)+'\n')
    files = {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
             for path in sorted(output_dir.iterdir()) if path.is_file()}
    (output_dir/'manifest.json').write_text(json.dumps(dict(files=files), indent=2,
                                                     sort_keys=True)+'\n')
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    try:
        summary = certify(args.output_dir)
    except (NoVerdict, ValueError) as error:
        print(json.dumps(dict(status='no_verdict', reason=str(error))), file=sys.stderr)
        return 2
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

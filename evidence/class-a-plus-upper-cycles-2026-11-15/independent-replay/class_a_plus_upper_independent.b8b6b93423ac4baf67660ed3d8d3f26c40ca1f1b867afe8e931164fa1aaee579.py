"""Independent exact finite replay of the eight upper-cycle path recipes.

This oracle imports no PSC arithmetic or path implementation. It counts the
literal words, uses unbounded integer vectors, and determines physical signs
by rational enclosures of a quadratic numerator at the upper cubic root.
The fixed grid supports the symbolic proof; it is not a universal theorem.

Every sign query shares an explicit root-refinement budget. Word allocation
also has a stated cap. Exhaustion raises NoVerdict; it is never acceptance.
The output directory must be new or empty so archived receipts are preserved.
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

CASES = ((1, 1), (1, 2), (1, 3), (1, 4), (2, 1), (2, 2), (3, 1), (4, 1))
N_VALUES = tuple(range(7, 66)) + (127, 255, 1024, 4096)
REFINEMENT_CAP = 256
WORD_OCCURRENCE_CAP = 50_000


class NoVerdict(RuntimeError):
    """A resource refusal, explicitly distinct from a mathematical result."""


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
    return tuple(x + y for x, y in zip(a, b))


def subtract(a, b):
    return tuple(x - y for x, y in zip(a, b))


class LiteralMember:
    """Literal count geometry with a bounded rational root-sign procedure."""

    def __init__(self, n, J, *, refinement_cap=REFINEMENT_CAP,
                 word_cap=WORD_OCCURRENCE_CAP):
        if (type(n) is not int or type(J) is not int or n < 7
                or J not in (1, 2, 3, 4)):
            raise ValueError("the finite oracle requires n>=7 and J in 1..4")
        if (type(refinement_cap) is not int or refinement_cap < 0
                or type(word_cap) is not int or word_cap < 0):
            raise ValueError("resource caps must be nonnegative integers")
        self.n, self.J = n, J
        self.d = 2*n + 12 - J
        occurrences = 3*n + self.d + 7
        if occurrences > word_cap:
            raise NoVerdict("literal word occurrence cap exhausted")
        self.refinement_cap, self.refinements = refinement_cap, 0
        self.lo, self.hi = Fraction(n+4), Fraction(n+6)
        if not self.polynomial(self.lo) < 0 < self.polynomial(self.hi):
            raise ValueError("the literal cubic does not satisfy its root bracket")
        # chi' is positive at and beyond the left endpoint. This exact bound
        # establishes uniqueness of the root followed by the bisection.
        if n*n + 7*n + 9 + J <= 0:
            raise ValueError("the positive derivative bound is unavailable")
        self.words = ((0,) + (2,)*(n+self.d) + (0,),
                      (1,) + (2,)*n + (0,),
                      (0,) + (2,)*(n+1) + (1,))
        self.prefixes, self.columns = [], []
        for word in self.words:
            count, row = [0, 0, 0], []
            for letter in word:
                row.append(tuple(count))
                count[letter] += 1
            self.prefixes.append(tuple(row))
            self.columns.append(tuple(count))
        if sum(map(len, self.words)) != occurrences:
            raise ValueError("the complete literal occurrence count changed")
        expected = ((2, 0, n+self.d), (1, 1, n), (1, 1, n+1))
        if tuple(self.columns) != expected:
            raise ValueError("literal Parikh counts differ from the family incidence")
        self.sign_cache = {}
        # D=beta(beta+1)>0. These are the full numerators of Lx,Lc,Ly.
        lengths = ((3, 6-J, 3), (-1, 0, 1), (0, 1, 1))
        for parent, counts in enumerate(self.columns):
            actual = tuple(sum(counts[a]*lengths[a][k] for a in range(3))
                           for k in range(3))
            c0, c1, c2 = lengths[parent]
            scaled = (2*c2, c0-(J-n-7)*c2, c1+(n+4)*c2)
            if actual != scaled:
                raise ValueError("actual word counts fail exact positive scaling")
            if self.sign_numerator(lengths[parent]) <= 0:
                raise ValueError("a literal eigenlength is not positive")

    def polynomial(self, x):
        return x**3 - (self.n+4)*x*x + (self.J-self.n-7)*x - 2

    def refine(self):
        if self.refinements >= self.refinement_cap:
            raise NoVerdict("exact root refinement cap exhausted")
        middle = (self.lo+self.hi)/2
        value = self.polynomial(middle)
        if value == 0:
            raise ValueError("unexpected rational root in the upper family")
        if value > 0:
            self.hi = middle
        else:
            self.lo = middle
        self.refinements += 1
        if not self.polynomial(self.lo) < 0 < self.polynomial(self.hi):
            raise ValueError("rational bisection lost its strict root bracket")

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
                sign = 1 if low > 0 else -1
                self.sign_cache[coefficients] = sign
                return sign
            self.refine()

    def sign(self, w):
        p, q, r = vector(w)
        a, b = 3*p+q+r, 3*p-q
        return self.sign_numerator((b, a+b-self.J*p, a))

    def incidence(self, w):
        w = vector(w)
        return tuple(sum(self.columns[column][row]*w[column]
                         for column in range(3)) for row in range(3))

    def strict(self, source):
        a, b, *w = packet(source)
        upper = tuple(x-(i == a) for i, x in enumerate(w))
        lower = tuple(x+(i == b) for i, x in enumerate(w))
        return self.sign(upper) < 0 and self.sign(lower) > 0

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


def source_packet(J, H, flip):
    if (type(J) is not int or type(H) is not int or (J, H) not in CASES
            or type(flip) is not bool):
        raise ValueError("outside the eight cases or invalid orientation")
    source = (2, 2, H, 3*H, -6*H)
    return (2, 2, *(-x for x in source[2:])) if flip else source


def schedule(n, J, H, flip):
    source_packet(J, H, flip)
    indices = []
    while J*H >= 3:
        indices.extend(((0, J*H-2), (J*(H-1)+4, 1)))
        H -= 1
    if H:
        if J == 1 and H in (1, 2):
            indices.extend(((0, 0), (1, 1+(n+4)*H), (1, 2*H+1)))
        elif (J, H) == (2, 1):
            indices.extend(((0, 0), (0, 2*n+6), (1, 2)))
        else:
            raise ValueError("uncovered base: no verdict")
    return [pair[::-1] for pair in indices] if flip else indices


def emit(member, H, flip):
    source = source_packet(member.J, H, flip)
    record = dict(n=member.n, J=member.J, H=H, flip=flip,
                  source=source, steps=[])
    for indices in schedule(member.n, member.J, H, flip):
        target, p, q = member.step(source, indices)
        record['steps'].append(dict(source=source, indices=indices, target=target,
                                    top_prefix=p, bottom_prefix=q))
        source = target
    return record


def replay(member, record):
    if record['n'] != member.n or record['J'] != member.J:
        raise ValueError("record is bound to different parameters")
    source = packet(record['source'])
    if source != source_packet(record['J'], record['H'], record['flip']):
        raise ValueError("record changed its required full source packet")
    if not member.strict(source):
        raise ValueError("nonstrict source")
    P = Q = (0, 0, 0)
    power = source[2:]
    terminal = False
    for edge in record['steps']:
        if terminal:
            raise ValueError("continued terminal")
        if packet(edge['source']) != source:
            raise ValueError("noncomposable middle")
        target, p, q = member.step(source, edge['indices'])
        if packet(edge['target']) != target:
            raise ValueError("wrong child type or full offset")
        if vector(edge['top_prefix']) != p or vector(edge['bottom_prefix']) != q:
            raise ValueError("false original prefix")
        if not member.strict(target):
            raise ValueError("nonstrict child")
        P, Q = add(member.incidence(P), p), add(member.incidence(Q), q)
        power = member.incidence(power)
        if target[2:] != add(power, subtract(Q, P)):
            raise ValueError("false complete prefix identity")
        source = target
        terminal = source[2:] == (0, 0, 0)
        if terminal and source[0] != source[1]:
            raise ValueError("first integral zero is not typed coincidence")
    if not terminal:
        raise ValueError("incomplete path")
    if power != subtract(P, Q):
        raise ValueError("false final original prefix identity")
    return dict(P=P, Q=Q, M_power_source=power, depth=len(record['steps']))


def negative_controls():
    member = LiteralMember(7, 1)
    good = emit(member, 4, False)
    replay(member, good)
    mutants = {}
    bad = copy.deepcopy(good)
    bad['steps'][0]['target'] = (2, 2, *bad['steps'][0]['target'][2:])
    mutants['wrong_middle_type'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['indices'] = (-1, 0)
    mutants['negative_index'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['indices'] = (0, 10)
    mutants['past_last'] = bad
    bad = copy.deepcopy(good)
    bad['steps'] = bad['steps'][:-1]
    mutants['truncated_path'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['target'] = (0, 2, 0, 0, 0)
    mutants['false_zero'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][1]['source'] = (0, 2, 0, 0, 0)
    mutants['noncomposable_middle'] = bad
    bad = copy.deepcopy(good)
    bad['steps'][0]['bottom_prefix'] = (1, 0, 0)
    mutants['wrong_original_prefix'] = bad
    bad = copy.deepcopy(good)
    last = good['steps'][-1]['target']
    target, p, q = member.step(last, (1, 1))
    bad['steps'].append(dict(source=last, indices=(1, 1), target=target,
                             top_prefix=p, bottom_prefix=q))
    mutants['continued_zero'] = bad
    rejected = {}
    for name, bad in mutants.items():
        try:
            replay(member, bad)
        except ValueError as error:
            rejected[name] = str(error)
        else:
            raise AssertionError(f"accepted invalid certificate: {name}")
    cap_refusals = {}
    for name, operation in (
            ('word_occurrences', lambda: LiteralMember(7, 1, word_cap=1)),
            ('root_refinement', lambda: LiteralMember(7, 1, refinement_cap=0)
             .sign_numerator((-12, 1, 0)))):
        try:
            operation()
        except NoVerdict as error:
            cap_refusals[name] = str(error)
        else:
            raise AssertionError(f"failed to refuse exhausted resource: {name}")
    diagnosis = {}
    for J, H in ((1, 4), (2, 2), (4, 1)):
        member = LiteralMember(7, J)
        first, _, _ = member.step(source_packet(J, H, False), (1, J*H))
        second, _, _ = member.step(first, (1, member.n+6-J*H))
        if second != (2, 1, H-1, 3*H-1, 4-6*H) or not member.strict(second):
            raise AssertionError("retired formula's actual y/c diagnosis changed")
        diagnosis[f'{J},{H}'] = dict(actual_target=second, index=member.n+2)
    return rejected, cap_refusals, diagnosis


def certify(output_dir):
    output_dir = Path(output_dir)
    if output_dir.exists() and any(output_dir.iterdir()):
        raise ValueError("output directory is not empty; historical evidence preserved")
    output_dir.mkdir(parents=True, exist_ok=True)
    source = Path(__file__).resolve().read_bytes()
    source_digest = hashlib.sha256(source).hexdigest()
    source_name = f'class_a_plus_upper_independent.{source_digest}.py'
    (output_dir/source_name).write_bytes(source)
    paths = edges = maximum_prefix = maximum_refinements = 0
    transcript_digest = hashlib.sha256()
    with (output_dir/'exact-transcripts.jsonl').open('w') as stream:
        for n in N_VALUES:
            for J, H in CASES:
                member = LiteralMember(n, J)
                for flip in (False, True):
                    record = emit(member, H, flip)
                    record['result'] = replay(member, record)
                    line = json.dumps(record, separators=(',', ':'), sort_keys=True)+'\n'
                    stream.write(line)
                    transcript_digest.update(line.encode())
                    paths += 1
                    edges += len(record['steps'])
                    maximum_prefix = max(maximum_prefix,
                        *(abs(x) for key in ('P', 'Q', 'M_power_source')
                          for x in record['result'][key]))
                    maximum_refinements = max(maximum_refinements, member.refinements)
    if paths != 1008 or edges != 3780:
        raise AssertionError("the complete fixed replay grid changed")
    rejected, cap_refusals, diagnosis = negative_controls()
    summary = dict(
        status='accepted_finite_replay',
        scope='independent finite literal-word replay; no recurrence or universal theorem',
        source_file='oracles/python/class_a_plus_upper_independent.py',
        source_sha256=source_digest, immutable_source_snapshot=source_name,
        python_version=platform.python_version(),
        n_values=N_VALUES, cases=CASES, paths=paths, edges=edges,
        depths=[len(schedule(7, J, H, False)) for J, H in CASES],
        maximum_depth=7, largest_absolute_prefix_coordinate=maximum_prefix,
        refinement_cap=REFINEMENT_CAP, maximum_refinements=maximum_refinements,
        word_occurrence_cap=WORD_OCCURRENCE_CAP,
        transcripts_sha256=transcript_digest.hexdigest(),
        rejected_mutations=rejected, resource_refusals=cap_refusals,
        failed_three_run_diagnosis=diagnosis,
        recurrence_executed=False, all_source_entry=False, universal_BH=False)
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

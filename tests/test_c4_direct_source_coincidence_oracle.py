"""Exact source certificates: all 36 M_2 orders, plus the uniform 021 family.

Positive prefix certificates imply productivity for every nonempty balanced
root of the covered substitution, independently of a proposed P,N template.
Finite tests do not establish the parameter-unbounded word proof in the note.
No pure-discrete-spectrum or general PSC inference is made.
"""
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
import json

WORD_CAP = 500_000


def validate_sigma(sigma):
    if len(sigma) != 3 or any(not isinstance(w, str) or not w or len(w) > 32 for w in sigma):
        raise ValueError("invalid ternary substitution or image budget")
    if any(c not in '012' for w in sigma for c in w):
        raise ValueError("invalid letter")


def inflate(sigma, word):
    validate_sigma(sigma)
    if not word or any(c not in '012' for c in word):
        raise ValueError("invalid nonempty source word")
    size = sum(len(sigma[int(c)]) for c in word)
    if size > WORD_CAP:
        raise ValueError("word budget exhausted, not a noncoincidence verdict")
    return ''.join(sigma[int(c)] for c in word)


def iterate(sigma, word, level):
    if type(level) is not int or level not in range(8):
        raise ValueError("invalid level budget")
    validate_sigma(sigma)
    for _ in range(level):
        word = inflate(sigma, word)
    return word


def parikh(word):
    if any(c not in '012' for c in word):
        raise ValueError("invalid Parikh letter")
    return tuple(word.count(c) for c in '012')


def verify(sigma, level, cut, mass, letter):
    if type(level) is not int or level not in range(1, 8):
        raise ValueError("invalid positive level")
    if type(cut) is not int or cut < 0 or cut > WORD_CAP:
        raise ValueError("invalid cut")
    if len(mass) != 3 or any(type(x) is not int or x < 0 or x > WORD_CAP for x in mass):
        raise ValueError("invalid prefix mass")
    if sum(mass) != cut or letter not in ('0', '1', '2'):
        raise ValueError("inconsistent certificate")
    words = [iterate(sigma, c, level) for c in '012']
    if not all(cut < len(w) and w[cut] == letter and parikh(w[:cut]) == tuple(mass) for w in words):
        raise ValueError("false literal prefix certificate")
    return tuple(map(len, words))


def search(sigma):
    """Bounded discovery; exhaustion raises, it never claims noncoincidence."""
    words = ['0', '1', '2']
    for level in range(1, 8):
        words = [inflate(sigma, w) for w in words]
        counts = [[0, 0, 0] for _ in words]
        for cut, letters in enumerate(zip(*words)):
            if len(set(letters)) == 1 and counts[0] == counts[1] == counts[2]:
                return level, cut, tuple(counts[0]), letters[0]
            for row, c in zip(counts, letters):
                row[int(c)] += 1
    raise ValueError("no witness within budget; no negative verdict")


def incidence_sources():
    return tuple(product(('01', '10'), ('112', '121', '211'),
                         tuple(''.join(w) for w in permutations('012'))))


def family(a, b):
    if type(a) is not int or type(b) is not int or min(a, b) < 0 or max(a, b) > 8 or not 1 <= a+b <= 12:
        raise ValueError("bounded family domain")
    return '01', '1'*a + '2' + '1'*b, '021'


def family_witness(a, b):
    family(a, b)
    s = a+b
    if a == 0:
        return 2, 0, (0, 0, 0), '0'
    if b > 0:
        return 5, a*(s*s+s+3)+1, (a+1, a*(s*s+1), a*(s+1)), '1'
    if a == 1:
        return 5, 16, (4, 7, 5), '0'
    return 5, a**3+2*a*a+5*a+6, (a+2, a**3+a*a+2*a+2, a*a+2*a+2), '0'


def balanced_factors(top, bottom):
    if not top or parikh(top) != parikh(bottom):
        raise ValueError("nonempty balanced root required")
    counts = [0, 0, 0]
    out, start = [], 0
    for end, (x, y) in enumerate(zip(top, bottom), 1):
        counts[int(x)] += 1
        counts[int(y)] -= 1
        if not any(counts):
            out.append((start, end, top[start:end], bottom[start:end]))
            start = end
    if start != len(top) or start != len(bottom):
        raise ValueError("missing terminal cut")
    return out


def receipt():
    rows = []
    for sigma in incidence_sources():
        level, cut, mass, letter = search(sigma)
        lengths = verify(sigma, level, cut, mass, letter)
        rows.append({'sigma': list(sigma), 'generation': level, 'cut': cut,
                     'prefix_parikh': list(mass), 'next_letter': letter,
                     'word_lengths': list(lengths)})
    return {'scope': 'all 36 sources with M_2; no P,N or state-count restriction; not general PSC',
            'source_count': len(rows), 'maximum_exhibited_generation': max(r['generation'] for r in rows),
            'certificates': rows}


def test_all_36_literal_positive_certificates_and_exact_domain():
    sources = incidence_sources()
    assert len(sources) == len(set(sources)) == 36
    for sigma in sources:
        assert [[w.count(str(i)) for w in sigma] for i in range(3)] == [[1,0,1],[1,2,1],[0,1,1]]
        verify(sigma, *search(sigma))
    assert receipt()['maximum_exhibited_generation'] == 7
    assert search(('01', '211', '120')) == (7, 464, (75,252,137), '1')


def test_all_36_actual_swap_diagonals():
    for sigma in incidence_sources():
        n, p, q, z = search(sigma)
        for x, y in combinations('012', 2):
            top, bottom = iterate(sigma, x+y, n), iterate(sigma, y+x, n)
            assert (p, p+1, z, z) in balanced_factors(top, bottom)


def test_uniform_family_grid_and_full_word_identities():
    cases = 0
    for a in range(9):
        for b in range(9):
            if not 1 <= a+b <= 12:
                continue
            sigma = family(a, b)
            A, B, C = sigma
            F, G, H = A+B, B*a+C+B*b, A+C+B
            U, V, W = F+G, G*a+H+G*b, F+H+G
            X, Y, Z = U+V, V*a+W+V*b, U+W+V
            n, p, q, z = family_witness(a, b)
            verify(sigma, n, p, q, z)
            assert [iterate(sigma, c, 2) for c in '012'] == [F,G,H]
            assert [iterate(sigma, c, 3) for c in '012'] == [U,V,W]
            assert [iterate(sigma, c, 4) for c in '012'] == [X,Y,Z]
            if a > 0 and b > 0:
                assert G.endswith('1'+B)
                T = G[:-len('1'+B)]
                first = F+G*(a-1)+T
                second = G*a+'0'
                words = [iterate(sigma, c, 5) for c in '012']
                assert words[0].startswith(first+'1') and words[2].startswith(first+'1')
                assert words[1].startswith(second+'1')
                assert parikh(first) == parikh(second) == q
                assert len(first) == len(second) == p
            elif a >= 2 and b == 0:
                first = F+G*(a+1)
                second = G*a+H+B*a
                words = [iterate(sigma, c, 5) for c in '012']
                assert words[0].startswith(first+'0') and words[2].startswith(first+'0')
                assert words[1].startswith(second+'0')
                assert parikh(first) == parikh(second) == q
                assert len(first) == len(second) == p
            cases += 1
    assert cases == 70


def test_exceptional_boundary_is_literal_not_an_extrapolated_formula():
    sigma = family(1,0)
    words = [iterate(sigma,c,5) for c in '012']
    assert [w[:17] for w in words] == ['01121202112021010','12021010211201120','01121202112021010']
    assert all(parikh(w[:16]) == (4,7,5) and w[16] == '0' for w in words)
    for b in range(1,9):
        sigma = family(0,b)
        assert all(iterate(sigma,c,2).startswith('0') for c in '012')


def test_family_actual_balanced_roots_and_longer_roots():
    roots = [('01','10'), ('02','20'), ('12','21'), ('012','210'), ('0112','2101')]
    for a in range(5):
        for b in range(5):
            if not a+b:
                continue
            sigma = family(a,b)
            n,p,q,z = family_witness(a,b)
            for u,v in roots:
                assert (p,p+1,z,z) in balanced_factors(iterate(sigma,u,n),iterate(sigma,v,n))


def test_false_certificates_and_budget_exhaustion_fail_closed():
    sigma = ('01','211','120')
    n,p,q,z = search(sigma)
    bad = [(n,p+1,q,z), (n,p,q,'2'), (0,p,q,z), (8,p,q,z), (n,-1,q,z),
           (n,p,(-1,253,212),z), (n,p,(75,251,138),z)]
    for args in bad:
        try: verify(sigma,*args)
        except ValueError: pass
        else: raise AssertionError('false certificate accepted')
    for sig in (('01','131','012'), ('','1','2'), ('0','1')):
        try: verify(sig,1,0,(0,0,0),'0')
        except ValueError: pass
        else: raise AssertionError('malformed substitution accepted')
    try: search(('0','1','2'))
    except ValueError as exc: assert 'budget' in str(exc)
    else: raise AssertionError('missing witness became a certificate')
    for a,b in ((0,0),(-1,1),(9,0),(8,8),(True,1)):
        try: family_witness(a,b)
        except ValueError: pass
        else: raise AssertionError('invalid family input')


def test_receipt_and_native_fixture_recompute():
    root = Path(__file__).resolve().parents[1]
    expected = json.loads((root/'evidence/c4-direct-source-coincidence-2026-11-04/receipt.json').read_text())
    assert receipt() == expected
    import ast
    content = (root/'kernel/tests/test_c4_direct_source_coincidence.mojo').read_text()
    table = ast.literal_eval('[' + content.split('# BEGIN CERTIFICATE TABLE\n',1)[1].split('# END CERTIFICATE TABLE',1)[0] + ']')
    assert table == [[r['generation'],r['cut'],*r['prefix_parikh'],int(r['next_letter'])] for r in expected['certificates']]


if __name__ == '__main__':
    print(json.dumps(receipt(), indent=2, sort_keys=True))

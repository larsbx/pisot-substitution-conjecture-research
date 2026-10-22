"""Independent integer-polynomial oracle for uniform class-A geometry.

No finite parameter extrapolation: positivity is established for all
0<h<1/5 using the positive-coefficient transform h=t/(5(1+t)).
"""
from pathlib import Path
import re

SOURCE = Path(__file__).resolve().parents[1] / "kernel/psc/class_a_typed_carrier.mojo"
LENGTHS = ((1, 1, 1, 0), (1, 0, 0, 0), (1, 1, 0, 0))
SEEDS = (
    (0,1,0,0,0),(1,0,-1,1,0),(0,0,0,1,0),
    (0,2,0,0,0),(2,0,-1,0,1),(0,0,0,0,1),
    (1,2,0,0,0),(2,1,0,-1,1),(2,2,0,-1,0),
)


def rows():
    matches = re.findall(
        r"^\s+List\[Int\]\(\[(-?\d+(?:,-?\d+){7})\]\),$",
        SOURCE.read_text(), re.MULTILINE,
    )
    result = [tuple(map(int, m.split(","))) for m in matches]
    assert len(result) == 89
    return result


def endpoint(s, y, a, b):
    return (s+a, -a+b+y, -a+b, -a)


def positive_transform(poly):
    """125(1+t)^3 f(t/(5(1+t))) in ascending powers of t."""
    a, b, c, d = poly
    return (
        125*a,
        375*a+25*b,
        375*a+50*b+5*c,
        125*a+25*b+5*c+d,
    )


def certified(poly):
    coef = positive_transform(poly)
    return all(c >= 0 for c in coef) and any(c > 0 for c in coef)


def margins(row):
    top, bottom, s, y, al, bl, au, bu = row
    low, high = endpoint(s,y,al,bl), endpoint(s,y,au,bu)
    return (
        tuple(a+b for a,b in zip(LENGTHS[bottom],low)),
        tuple(a-b for a,b in zip(LENGTHS[top],high)),
    )


def includes_seed_for_all_n(template, seed):
    top,bottom,k,c,y=seed
    return any(
        (a,b,s,q)==(top,bottom,k+c+y,y)
        and al<=0 and au>=0 and al*4+bl<=k<=au*4+bu
        for a,b,s,q,al,bl,au,bu in template
    )


def test_all_interval_margins_uniformly_positive():
    template = rows()
    ms = [m for row in template for m in margins(row)]
    assert len(ms) == 178
    assert all(certified(m) for m in ms)
    assert not certified((0,0,0,0))  # boundary is not interior
    assert not certified((0,-1,0,0))
    assert certified((0,1,0,0))
    # Deliberately extend a bound beyond actual overlap geometry.
    broken = list(template[0])
    broken[7] += 50
    assert any(not certified(m) for m in margins(broken))


def test_all_n_interval_nonemptiness_disjointness_and_cardinality():
    template=rows()
    assert sum(au-al for _,_,_,_,al,bl,au,bu in template)==40
    assert sum(bu-bl+1 for _,_,_,_,al,bl,au,bu in template)==115
    for i,a in enumerate(template):
        assert a[6]-a[4]>=0 and 4*(a[6]-a[4])+a[7]-a[5]>=0
        for b in template[i+1:]:
            if a[:4]!=b[:4]:
                continue
            before_a = b[4]-a[6] >= 0 and 4*(b[4]-a[6])+b[5]-a[7] >= 1
            before_b = a[4]-b[6] >= 0 and 4*(a[4]-b[6])+a[5]-b[7] >= 1
            assert before_a or before_b


def test_all_n_canonical_seed_inclusion():
    template=rows()
    assert len(set(SEEDS))==9
    assert all(includes_seed_for_all_n(template,s) for s in SEEDS)
    # Remove the sole (y,y,-1,0) slice; it contains one canonical seed.
    sliced = [r for r in template if r[:4]!=(2,2,-1,0)]
    assert not includes_seed_for_all_n(sliced,(2,2,0,-1,0))

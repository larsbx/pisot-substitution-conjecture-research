"""Independent integer-time sweep of actual physical hub completions.

The reference computes the height from scratch at EVERY integer time,
not by merging endpoint queues like the canonical Mojo kernel. Counts
scattered hub/nonhub subwords separately to verify weighted area.
All tested widths are positive exact integers (not Perron approximations).
"""
from collections import Counter
from itertools import product
import pytest


def area_from_unit_time(pair,hub,widths):
    top,bottom=pair
    assert top and bottom and top[0]==hub and bottom[0]!=hub
    assert Counter(top)==Counter(bottom)
    ends=[]
    for word in (top,bottom):
        acc=0
        records=[]
        for x in word:
            acc+=widths[x]
            records.append((acc,x))
        ends.append(records)
    assert ends[0][-1][0]==ends[1][-1][0]
    T=ends[0][-1][0]
    heights=[
        sum(x==hub and end<=t for end,x in ends[0])
        -sum(x==hub and end<=t for end,x in ends[1])
        for t in range(T)
    ]
    area=sum(heights)
    neg=sum(h<0 for h in heights)
    pos=sum(h>0 for h in heights)
    # Completely separate O(n²) scattered-subword oracle.
    weighted_scattered=0
    for word,sign in ((top,1),(bottom,-1)):
        for i,x in enumerate(word):
            if x==hub:
                weighted_scattered+=sign*sum(widths[y] for y in word[i+1:])
    assert area==weighted_scattered
    assert min(heights[:widths[hub]])==0
    if not neg:
        assert area>=widths[bottom[0]]
    return area,neg,pos,T


@pytest.mark.parametrize("widths",[(1,1,1),(2,3,5),(3,1,4)])
def test_known_physical_positive_negative_and_reducible_controls(widths):
    controls=[
        ((1,2,0,1),(0,1,1,2),1),
        ((1,2,2,0,2,2,0,2,2,0,1),(0,2,2,2,0,2,2,0,1,1,2),1),
        ((2,1,0),(1,0,2),2),
        ((2,1,1,1,0),(1,1,1,0,2),2),
    ]
    for top,bottom,hub in controls:
        area,neg,pos,T=area_from_unit_time((top,bottom),hub,widths)
        assert T==sum(widths[x] for x in top)
        if (top,bottom)==controls[2][:2]:
            assert neg==0 and area>=widths[bottom[0]]
    assert area_from_unit_time(controls[0][:2],1,(2,3,5))==(-3,5,2,13)
    assert area_from_unit_time(controls[1][:2],1,(2,3,5))==(26,5,31,42)


def test_all_small_balanced_oriented_pairs_exact_weighted_identity():
    checked=0;crossing=0;noncrossing=0
    for n in range(2,6):
        words=list(product(range(3),repeat=n))
        by_mass={}
        for word in words:
            by_mass.setdefault(tuple(word.count(a) for a in range(3)),[]).append(word)
        for family in by_mass.values():
            for top in family:
                for bottom in family:
                    if top==bottom or top[0]==bottom[0]:
                        continue
                    hub=top[0]
                    for widths in ((1,1,1),(2,3,5)):
                        area,neg,_,_=area_from_unit_time((top,bottom),hub,widths)
                        if neg:
                            crossing+=1
                        else:
                            noncrossing+=1
                            assert area>=min(widths)
                        checked+=1
    assert checked>1000 and crossing>0 and noncrossing>0


def test_balanced_cut_additivity_and_false_hub_orientation():
    pair=((1,2,0,1),(0,1,1,2))
    a=area_from_unit_time(pair,1,(2,3,5))
    doubled=(pair[0]*2,pair[1]*2)
    b=area_from_unit_time(doubled,1,(2,3,5))
    assert b[0]==2*a[0] and b[1]==2*a[1]
    with pytest.raises(AssertionError):
        area_from_unit_time((pair[1],pair[0]),1,(2,3,5))
    with pytest.raises(AssertionError):
        area_from_unit_time(((1,2),(2,2)),1,(2,3,5))

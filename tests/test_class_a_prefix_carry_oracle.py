"""Independent literal σ² occurrence-pair oracle for the finite-place carry.

The reference criterion is exact Cramer's-rule divisibility of the
completely expanded prefix difference by M². The separate digit-carry
algorithm receives genuine root-to-leaf ordered child addresses and checks
the same result without expanding σ². Neither test proves reachability.
"""

from itertools import product
import pytest
from test_class_a_madic_digits_oracle import matrix,power,cramers,matvec,words


def prefix(word,index):
    counts=[0,0,0]
    for a in word[:index]:
        counts[a]+=1
    return tuple(counts)


def expand_once(w,sigma):
    return tuple(a for x in w for a in sigma[x])


def addressed_prefixes(sigma,parent):
    full=expand_once(sigma[parent],sigma)
    out=[]
    position=0
    for i,letter in enumerate(sigma[parent]):
        for j in range(len(sigma[letter])):
            out.append(((i,j),prefix(full,position+j),letter))
        position+=len(sigma[letter])
    assert position==len(full)
    assert len(out)==len(full)
    return out


def carry_pair(sigma,k,t,a,b,apath,bpath):
    ai,aj=apath
    bi,bj=bpath
    al=sigma[a][ai]
    bl=sigma[b][bi]
    low=tuple(x-y for x,y in zip(prefix(sigma[al],aj),
                                  prefix(sigma[bl],bj)))
    high=tuple(x-y for x,y in zip(prefix(sigma[a],ai),
                                   prefix(sigma[b],bi)))
    current=(0,0,0)
    for index,d in enumerate((low,high)):
        input_vec=tuple(x+y for x,y in zip(current,d))
        current=cramers(matrix(k,t),input_vec)
        if current is None:
            return False,index,None
    return True,-1,current


@pytest.mark.parametrize("k,t",[(0,0),(1,0),(0,1)])
def test_all_literal_sigma_two_path_pairs_against_cramer(k,t):
    sigma=words(k,t)
    flat=[addressed_prefixes(sigma,a) for a in range(3)]
    m2=power(matrix(k,t),2)
    positives=first_fail=second_fail=0
    for a,b in product(range(3),repeat=2):
        for apath,first,_ in flat[a]:
            for bpath,second,_ in flat[b]:
                diff=tuple(x-y for x,y in zip(first,second))
                direct=cramers(m2,diff)
                valid,fail,parent=carry_pair(sigma,k,t,a,b,apath,bpath)
                assert valid==(direct is not None)
                if valid:
                    assert parent==direct
                    assert matvec(m2,parent)==diff
                    positives+=1
                elif fail==0:
                    first_fail+=1
                else:
                    assert fail==1
                    second_fail+=1
    assert min(positives,first_fail,second_fail)>0
    # Independent full-word/Cramer scratch replay at 2026-11-02; exact
    # small-member counts, not bounds for any general parameter.
    assert (positives,first_fail,second_fail)=={
        (0,0):(3794,3154,3456),
        (1,0):(7851,5612,7562),
        (0,1):(8900,6240,8576),
    }[(k,t)]


def test_local_digit_kind_agreement_does_not_force_global_hit():
    sigma=words(0,0)
    # Both LAST-LEVEL paths choose FIRST at index zero; only the
    # *second* parity carry fails. This is a literal Class-A example,
    # not a counterexample to any universal BH theorem.
    ok,stage,parent=carry_pair(sigma,0,0,0,0,(0,0),(1,0))
    assert not ok and stage==1 and parent is None
    full=addressed_prefixes(sigma,0)
    positions={p:vec for p,vec,_ in full}
    D=tuple(x-y for x,y in zip(positions[(0,0)],positions[(1,0)]))
    assert cramers(power(matrix(0,0),2),D) is None


def actual_level_word(sigma,root,depth):
    out=(root,)
    for _ in range(depth):
        out=expand_once(out,sigma)
    return out


def root_to_leaf_prefix_position(sigma,root,path):
    """Address in sigma^depth(root), using exact smaller-block lengths."""
    depth=len(path)
    lengths=[(1,1,1)]
    for _ in range(depth):
        prior=lengths[-1]
        lengths.append(tuple(sum(prior[b] for b in sigma[a])
                             for a in range(3)))
    letter=root
    pos=0
    for r,ordinal in enumerate(path):
        assert 0<=ordinal<len(sigma[letter])
        remaining=depth-r-1
        pos+=sum(lengths[remaining][b] for b in sigma[letter][:ordinal])
        letter=sigma[letter][ordinal]
    return pos


def genuine_paths(sigma,root,depth):
    paths=[(root,())]
    for _ in range(depth):
        next_paths=[]
        for parent,path in paths:
            choices={0,1,len(sigma[parent])-1}
            for index in sorted(choices):
                if index<len(sigma[parent]):
                    next_paths.append((sigma[parent][index],path+(index,)))
        paths=next_paths
    return [path for _,path in paths]


def path_carry(sigma,k,t,a,b,apath,bpath):
    assert len(apath)==len(bpath)
    corrections=[]
    top=a
    bottom=b
    for i,j in zip(apath,bpath):
        assert i<len(sigma[top]) and j<len(sigma[bottom])
        corrections.append(tuple(x-y for x,y in zip(
            prefix(sigma[top],i),prefix(sigma[bottom],j))))
        top=sigma[top][i]
        bottom=sigma[bottom][j]
    carry=(0,0,0)
    for j,correction in enumerate(reversed(corrections)):
        val=tuple(x+y for x,y in zip(carry,correction))
        carry=cramers(matrix(k,t),val)
        if carry is None:
            return False,j,None
    return True,-1,carry


@pytest.mark.parametrize("k,t",[(0,0),(1,0),(0,1)])
def test_three_level_actual_paths_match_full_expansion_and_cramer(k,t):
    sigma=words(k,t)
    full=[actual_level_word(sigma,a,3) for a in range(3)]
    paths=[genuine_paths(sigma,a,3) for a in range(3)]
    mp=power(matrix(k,t),3)
    passes=refusals=0
    for a,b in product(range(3),repeat=2):
        for pa in paths[a]:
            pi=root_to_leaf_prefix_position(sigma,a,pa)
            for pb in paths[b]:
                pj=root_to_leaf_prefix_position(sigma,b,pb)
                diff=tuple(x-y for x,y in zip(
                    prefix(full[a],pi),prefix(full[b],pj)))
                expected=cramers(mp,diff)
                good,fail,got=path_carry(sigma,k,t,a,b,pa,pb)
                assert good==(expected is not None)
                if good:
                    assert got==expected
                    passes+=1
                else:
                    assert 0<=fail<3
                    refusals+=1
    assert passes>0 and refusals>0

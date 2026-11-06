from collections import Counter
from copy import deepcopy
from itertools import combinations, product
from pathlib import Path
import json
import os
import random
import subprocess
import sys
import pytest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'oracles'))
import two_tail_uniform as t

# This literal implementation uses no DAG query or producer-derived mass.
def source(a,b,tail):return ('01','1'*a+'2'+'1'*b,tail)
def expand(s,w,n):
    for _ in range(n):w=''.join(s[int(c)] for c in w)
    return w

def cuts(u,v):
    require=Counter(u)==Counter(v)
    if not require:raise ValueError('unbalanced test pair')
    left,right=Counter(),Counter();start=0;out=[]
    for end,(a,b) in enumerate(zip(u,v),1):
        left[a]+=1;right[b]+=1
        if left==right:out.append((start,end,u[start:end],v[start:end]));start=end
    if start!=len(u) or start!=len(v):raise ValueError('unfinished factorization')
    return out

def direct_certificate(s,c):
    n,p=c['generation'],c['cut'];mass=tuple(c['prefix_parikh']);z=str(c['next_letter'])
    words=[expand(s,str(i),n) for i in c['letters']]
    for w in words:
        assert p<len(w) and w[p]==z
        actual=Counter(w[:p]);assert tuple(actual[str(i)]for i in range(3))==mass
    return words

@pytest.mark.parametrize('tail',['102','120'])
def test_compressed_grid_exact_formulas_and_fifth_level(tail):
    count=0
    for a in range(21):
        for b in range(21):
            if not a+b:continue
            for pair in t.PAIRS:
                c=t.witness(a,b,tail,pair)
                assert t.verify(c)['cached_images']<=18
                d=t.to_fifth(c)
                assert t.verify(d)['cached_images']<=18 and d['generation']==5
                count+=1
    assert count==1320

@pytest.mark.parametrize('tail',['102','120'])
def test_independent_literal_grid_and_actual_root_factorization(tail):
    count=0
    for a in range(6):
        for b in range(6-a):
            if not a+b:continue
            s=source(a,b,tail)
            for pair in t.PAIRS:
                c=t.witness(a,b,tail,pair);direct_certificate(s,c)
                c5=t.to_fifth(c);direct_certificate(s,c5)
            for u,v in [('01','10'),('02','20'),('12','21'),('012','210'),('0112','2101')]:
                c=t.root_certificate(a,b,tail,u,v)
                top,bottom=expand(s,u,5),expand(s,v,5)
                p,z=c['cut'],str(c['next_letter'])
                assert (p,p+1,z,z) in cuts(top,bottom)
                count+=1
    assert count==100

@pytest.mark.parametrize('tail',['102','120'])
def test_all_positive_chamber_block_words(tail):
    for a in range(1,6):
        for b in range(6):
            s=source(a,b,tail);A,B,C=s
            F,G=A+B,B*a+C+B*b
            H=B+A+C if tail=='102' else B+C+A
            U,V=F+G,G*a+H+G*b
            W=G+F+H if tail=='102' else G+H+F
            actual=[expand(s,str(i),4) for i in range(3)]
            assert actual==[U+V,V*a+W+V*b,V+U+W if tail=='102' else V+W+U]
            if tail=='102':prefixes=[F+G*a,G*a+B+A,G*a+B+A]
            else:prefixes=[F+G*a+B*a+C,G*a+H+B*a,G*a+H+B*a]
            c=t.witness(a,b,tail,(0,1))
            for w,pref in zip(actual,prefixes):
                assert w.startswith(pref+'1')
                assert len(pref)==c['cut']
                assert tuple(pref.count(z)for z in '012')==tuple(c['prefix_parikh'])


def test_120_zero_left_boundary_word_identities():
    for b in range(1,13):
        s=source(0,b,'120');A,B,C=s;F=A+B;G=C+B*b;H=B+C+A
        assert F.endswith('1') and G.endswith('1') and H.endswith('1')
        cases=[((1,2),3,[H+G[:-1],G+H[:-1]]),
               ((0,1),4,[F+G+H[:-1],G+H+F[:-1]]),
               ((0,2),5,[F+G+H[:-1],G+H+F[:-1]])]
        for pair,n,prefixes in cases:
            c=t.witness(0,b,'120',pair)
            assert c['generation']==n
            for a,pref in zip(pair,prefixes):
                assert expand(s,str(a),n).startswith(pref+'1')
                assert len(pref)==c['cut']
                assert tuple(pref.count(z)for z in '012')==tuple(c['prefix_parikh'])


def test_102_zero_left_large_boundary_word_identity():
    for b in range(3,13):
        s=source(0,b,'102');A,B,C=s;F=A+B;G=C+B*b;H=B+A+C
        U,V,W=F+G,H+G*b,G+F+H
        X,Y,Z=U+V,W+V*b,V+U+W
        prefixes=[Z+G+A+'2',G+F+H+H+G*b+H+G*2]
        c=t.witness(0,b,'102',(1,2))
        for a,pref in zip((1,2),prefixes):
            assert expand(s,str(a),5).startswith(pref+'1')
            assert len(pref)==c['cut']
            assert tuple(pref.count(z)for z in '012')==tuple(c['prefix_parikh'])
        assert Counter(F+A+'2')==Counter(H)


def test_102_zero_left_small_pairs_and_exceptions():
    for b in range(1,20):
        s=source(0,b,'102');A,B,C=s
        f,h=A+B,B+A+C
        assert f.startswith('012') and (C+B*b).startswith('102')
        assert f.startswith('012'+'1'*(b-1)+'1')
        assert h.startswith(B+'0'+'1')
        for pair in ((0,1),(0,2)):direct_certificate(s,t.witness(0,b,'102',pair))
    literal={1:('1022101212101102210110210221','2101102102210121102211022101'),
             2:('102211211012112110110221101102102211211102211211211',
                '211011021022112111022112110121110221121110221121101')}
    for b,prefixes in literal.items():
        c=t.witness(0,b,'102',(1,2));s=source(0,b,'102')
        words=direct_certificate(s,c)
        assert tuple(w[:c['cut']+1]for w in words)==prefixes


def test_small_witness_does_not_extend_across_its_domain_boundary():
    # The n=5 polynomial for b>=3 has next letter 0 on one side at b=2.
    b=2
    c={'a':0,'b':b,'tail':'102','letters':[1,2],'generation':5,
       'cut':b**3+4*b*b+10*b+30,
       'prefix_parikh':[b+10,b**3+3*b*b+5*b+10,b*b+4*b+10], 'next_letter':1}
    with pytest.raises(t.Invalid):t.verify(c)

@pytest.mark.parametrize('tail',['102','120'])
def test_large_parameters_do_not_materialize_images(tail):
    for a,b in t.LARGE_CASES:
        for pair in t.PAIRS:
            c=t.to_fifth(t.witness(a,b,tail,pair))
            result=t.verify(c)
            assert result['cached_images']<=18
            assert max(result['word_lengths'])>10**100
        ex=t.Expansion(a,b,tail)
        with pytest.raises(t.Budget):t.materialize(ex.image(1,5))


def test_dag_queries_agree_with_literal_counters():
    for tail in ('102','120'):
        for a,b in ((0,1),(0,3),(1,0),(1,1),(3,2)):
            ex=t.Expansion(a,b,tail);s=source(a,b,tail)
            for n in range(5):
                for c in range(3):
                    w=ex.image(c,n);direct=expand(s,str(c),n)
                    assert t.materialize(w)==direct
                    for p in range(len(direct)+1):
                        assert t.prefix_mass(w,p)==tuple(direct[:p].count(z)for z in '012')
                        if p<len(direct):assert t.char_at(w,p)==int(direct[p])


def test_depth_five_is_sharp_for_source_pair_uniform_bound():
    s=('01','211','120')
    expected=[[(0,'0','1')],[(0,'0','2')],[(0,'0','1'),(3,'1','2')],
              [(0,'0','2'),(8,'2','1'),(10,'1','0'),(29,'1','2')]]
    for n in range(1,5):
        u,v=expand(s,'0',n),expand(s,'2',n)
        actual=[]
        for p in range(min(len(u),len(v))):
            if Counter(u[:p])==Counter(v[:p]):actual.append((p,u[p],v[p]))
        assert actual==expected[n-1]
        assert all(x!=y for _,x,y in actual)
    direct_certificate(s,t.witness(0,2,'120',(0,2)))


def test_same_initial_letter_roots_and_track_swaps():
    for tail in ('102','120'):
        for a,b in ((0,1),(1,0),(2,3)):
            c=t.root_certificate(a,b,tail,'012','021')
            assert c['cut']==0
            c=t.root_certificate(a,b,tail,'0112','2101')
            d=t.root_certificate(a,b,tail,'2101','0112')
            assert c['cut']==d['cut'] and c['next_letter']==d['next_letter']


def test_false_positive_certificates_refuse():
    c=t.witness(2,3,'120',(0,1))
    mutations=[]
    for key,value in [('generation',0),('generation',6),('generation',True),('cut',-1),
                      ('cut',c['cut']+1),('next_letter',0),('next_letter',3),('next_letter',True),
                      ('letters',[0,0]),('letters',[False,1]),('tail','201'),('a',-1),('b',True)]:
        z=deepcopy(c);z[key]=value;mutations.append(z)
    q=deepcopy(c);q['prefix_parikh'][0]+=1;q['prefix_parikh'][1]-=1;mutations.append(q)
    q=deepcopy(c);q['prefix_parikh']=[1,2];mutations.append(q)
    q=deepcopy(c);q['extra']='untrusted';mutations.append(q)
    for q in mutations:
        with pytest.raises(t.Invalid):t.verify(q)


def test_parameter_root_and_repeat_refusals():
    for a,b in ((0,0),(-1,2),(2,-1),(True,1),(1,1.0)):
        with pytest.raises(t.Invalid):t.witness(a,b,'102',(0,1))
    with pytest.raises(t.Budget):t.witness(1<<513,0,'120',(0,1))
    for u,v in [('', ''),('0','1'),('03','30'),('0','00'),('1'*65,'1'*65)]:
        with pytest.raises(t.Invalid):t.root_certificate(1,1,'120',u,v)
    for k in (-1,True,1.2):
        with pytest.raises(t.Invalid):t.repeat(t.letter(0),k)
    for p in (-1,True,2):
        with pytest.raises(t.Invalid):t.char_at(t.letter(0),p)
    with pytest.raises(t.Invalid):t.Expansion(1,0,'120').image(0,6)


def test_optimized_python_admission_stays_fail_closed():
    cmd=f"import sys;sys.path.insert(0,{str(ROOT/'oracles')!r});import two_tail_uniform as t;c=t.witness(2,3,'120',(0,1));c['next_letter']=0;t.verify(c);print('CERTIFIED')"
    result=subprocess.run([sys.executable,'-O','-c',cmd],capture_output=True,text=True)
    assert result.returncode!=0 and not result.stdout and 'actual next letter' in result.stderr


def test_committed_receipt_regenerates_exactly():
    assert json.loads((ROOT/'evidence/receipt.json').read_text())==t.receipt()

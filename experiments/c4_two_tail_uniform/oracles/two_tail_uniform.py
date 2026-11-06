"""Exact compressed positive certificates for two infinite Pisot run families.

Source: (01, 1^a 2 1^b, tail), tail=102 or 120; a,b>=0, a+b>=1.
The unbounded theorem is a written block-word proof, not finite extrapolation.
Production checks use explicit exceptions and integer arithmetic only.
DAG summaries are computed at construction, not imported from a certificate.
A resource cap is refusal, never a mathematical noncoincidence verdict.
"""
from __future__ import annotations
from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from typing import Iterable
import argparse
import json

MAX_PARAMETER_BITS = 512
MAX_LEVEL = 5
LITERAL_CAP = 300_000
PAIRS = tuple(combinations(range(3), 2))
SCHEMA = 'c4-two-tail-uniform-v1'

class Invalid(ValueError):
    pass
class Budget(Invalid):
    pass

def require(ok: bool, msg: str) -> None:
    if not ok:
        raise Invalid(msg)

def natural(value, label):
    require(type(value) is int and value >= 0, f'{label} must be a nonnegative integer')
    if value.bit_length() > MAX_PARAMETER_BITS:
        raise Budget(f'{label} exceeds the executable bit budget; no verdict')
    return value

def parameters(a, b, tail):
    natural(a, 'a'); natural(b, 'b')
    require(a+b >= 1, 'empty total run is outside the theorem')
    require(type(tail) is str and tail in ('102', '120'), 'unsupported tail ordering')
    return a, b, tail

def plus(x, y):
    return tuple(a+b for a,b in zip(x,y))

def scale(k, x):
    return tuple(k*a for a in x)

@dataclass(frozen=True, slots=True)
class Word:
    kind: str
    args: tuple
    length: int
    mass: tuple[int, int, int]

# All theorem-facing Words are constructed below from validated source data.
# Imported Word instances or caller-provided summary fields are never admission inputs.
def letter(c: int) -> Word:
    require(type(c) is int and 0 <= c < 3, 'letter before indexing')
    return Word('letter',(c,),1,tuple(int(i==c) for i in range(3)))

def empty() -> Word:
    return Word('concat',(),0,(0,0,0))

def concat(*parts: Word) -> Word:
    parts=tuple(p for p in parts if p.length)
    if len(parts)==1:return parts[0]
    return Word('concat',parts,sum(p.length for p in parts),
                tuple(sum(p.mass[i] for p in parts) for i in range(3)))

def repeat(part: Word, exponent: int) -> Word:
    natural(exponent,'repeat exponent')
    if exponent==0 or part.length==0:return empty()
    if exponent==1:return part
    return Word('repeat',(part,exponent),part.length*exponent,scale(exponent,part.mass))

def literal(word: str) -> Word:
    require(type(word) is str and all(c in '012' for c in word),'literal letters')
    return concat(*(letter(int(c)) for c in word))

def char_at(word: Word, position: int) -> int:
    require(type(position) is int and 0 <= position < word.length,'character index')
    if word.kind=='letter':return word.args[0]
    if word.kind=='repeat':return char_at(word.args[0],position % word.args[0].length)
    require(word.kind=='concat','unsupported word node')
    for p in word.args:
        if position<p.length:return char_at(p,position)
        position-=p.length
    raise Invalid('inconsistent word length')

def prefix_mass(word: Word, length: int) -> tuple[int,int,int]:
    require(type(length) is int and 0 <= length <= word.length,'prefix index')
    if length==0:return (0,0,0)
    if length==word.length:return word.mass
    if word.kind=='repeat':
        child,count=word.args
        whole,rest=divmod(length,child.length)
        return plus(scale(whole,child.mass),prefix_mass(child,rest))
    require(word.kind=='concat','nonterminal partial prefix expected')
    out=(0,0,0)
    for child in word.args:
        if length<=child.length:return plus(out,prefix_mass(child,length))
        out=plus(out,child.mass);length-=child.length
    raise Invalid('inconsistent word length')

class Expansion:
    """At most three cached image nodes per generation; no inflated string."""
    def __init__(self,a,b,tail):
        self.a,self.b,self.tail=parameters(a,b,tail)
        self.cache={}
    def image(self,c,n):
        require(type(c) is int and c in range(3),'source letter')
        require(type(n) is int and 0<=n<=MAX_LEVEL,'source level budget')
        key=c,n
        if key in self.cache:return self.cache[key]
        if n==0:out=letter(c)
        elif c==0:out=concat(self.image(0,n-1),self.image(1,n-1))
        elif c==1:
            out=concat(repeat(self.image(1,n-1),self.a), self.image(2,n-1),
                       repeat(self.image(1,n-1),self.b))
        else:out=concat(*(self.image(int(z),n-1) for z in self.tail))
        self.cache[key]=out
        return out
    def word(self,w,n):
        require(type(w) is str and w and all(c in '012' for c in w),'nonempty source word')
        require(len(w)<=64,'source word input budget')
        return concat(*(self.image(int(c),n) for c in w))

def incidence(a,b):
    return ((1,0,1),(1,a+b,1),(0,1,1))

def mv(m,v):
    return tuple(sum(a*b for a,b in zip(row,v)) for row in m)

def first_letter(a,b,tail,c):
    if c==0:return 0
    if c==1:return 1 if a else 2
    return int(tail[0])

def witness(a,b,tail,pair):
    parameters(a,b,tail)
    require(type(pair) in (tuple,list) and tuple(pair) in PAIRS and
            all(type(c) is int for c in pair),'ordered distinct source pair')
    i,j=pair;s=a+b;g=s*s+s+3
    if a>=1:
        n,z=4,1
        if tail=='102':
            mass=(a+1,a*(s*s+1)+s+1,a*(s+1)+1)
        else:
            mass=(a+2,a*(s*s+s+1)+s+2,a*(s+2)+2)
    elif tail=='120':
        z=1
        if (i,j)==(1,2):
            n=3;mass=(3,b*b+b+2,b+3)
        else:
            n=4 if (i,j)==(0,1) else 5
            mass=(4,b*b+2*b+3,b+4)
    elif (i,j)==(0,1):n,z,mass=2,2,(1,1,0)
    elif (i,j)==(0,2):n,z,mass=2,1,(1,b,1)
    elif b==1:n,z,mass=4,1,(7,11,9)
    elif b==2:n,z,mass=4,1,(8,27,15)
    else:n,z,mass=5,1,(b+10,b**3+3*b*b+5*b+10,b*b+4*b+10)
    return {'a':a,'b':b,'tail':tail,'letters':[i,j],'generation':n,
            'cut':sum(mass),'prefix_parikh':list(mass),'next_letter':z}

FIELDS={'a','b','tail','letters','generation','cut','prefix_parikh','next_letter'}
def verify(cert):
    """Independent of formula discovery: authenticate supplied positive cuts."""
    require(type(cert) is dict and set(cert)==FIELDS,'certificate fields')
    a,b,tail=parameters(cert['a'],cert['b'],cert['tail'])
    pair=cert['letters']
    require(type(pair) in (tuple,list) and len(pair)==2 and all(type(c)is int for c in pair)
            and tuple(pair) in PAIRS,'certificate letters')
    n,p,z=cert['generation'],cert['cut'],cert['next_letter']
    mass=cert['prefix_parikh']
    require(type(n)is int and 1<=n<=MAX_LEVEL,'positive generation budget')
    require(type(p)is int and 0<=p and p.bit_length()<=MAX_PARAMETER_BITS*MAX_LEVEL+16,'cut budget')
    require(type(z)is int and 0<=z<3,'next letter')
    require(type(mass) in (tuple,list) and len(mass)==3 and
            all(type(x)is int and x>=0 for x in mass),'prefix coordinates')
    require(sum(mass)==p,'prefix mass versus physical index')
    ex=Expansion(a,b,tail)
    words=[ex.image(c,n) for c in pair]
    for word in words:
        require(p<word.length,'cut must have an actual next letter')
        require(prefix_mass(word,p)==tuple(mass),'false actual prefix mass')
        require(char_at(word,p)==z,'false actual next letter')
    return {'word_lengths':[w.length for w in words], 'cached_images':len(ex.cache)}

def to_fifth(cert):
    verify(cert)
    result=dict(cert);result['letters']=list(cert['letters'])
    mass=tuple(cert['prefix_parikh']);z=cert['next_letter']
    for _ in range(5-cert['generation']):
        mass=mv(incidence(cert['a'],cert['b']),mass)
        z=first_letter(cert['a'],cert['b'],cert['tail'],z)
    result.update(generation=5,cut=sum(mass),prefix_parikh=list(mass),next_letter=z)
    verify(result)
    return result

def root_certificate(a,b,tail,top,bottom):
    parameters(a,b,tail)
    require(type(top)is str and type(bottom)is str and 0<len(top)==len(bottom)<=64,
            'balanced root lengths')
    require(all(c in '012' for c in top+bottom),'root letters before indexing')
    require(tuple(top.count(c) for c in '012')==tuple(bottom.count(c) for c in '012'),
            'root is not balanced')
    x,y=int(top[0]),int(bottom[0])
    ex=Expansion(a,b,tail)
    if x==y:
        p=0;mass=(0,0,0);z=char_at(ex.image(x,5),0)
    else:
        cert=to_fifth(witness(a,b,tail,tuple(sorted((x,y)))))
        p=cert['cut'];mass=tuple(cert['prefix_parikh']);z=cert['next_letter']
    for w in (ex.word(top,5),ex.word(bottom,5)):
        require(prefix_mass(w,p)==mass and char_at(w,p)==z,'failed root transfer')
        require(prefix_mass(w,p+1)==plus(mass,tuple(int(c==z)for c in range(3))),
                'failed consecutive-cut check')
    return {'generation':5,'cut':p,'prefix_parikh':list(mass),'next_letter':z,
            'top':top,'bottom':bottom,'word_lengths':[ex.word(w,5).length for w in(top,bottom)]}

def materialize(word,cap=LITERAL_CAP):
    require(type(cap)is int and 0<=cap<=LITERAL_CAP,'materialization cap')
    if word.length>cap:raise Budget('expanded word exceeds materialization budget; no verdict')
    if word.kind=='letter':return str(word.args[0])
    if word.kind=='repeat':return materialize(word.args[0],cap)*word.args[1]
    return ''.join(materialize(w,cap) for w in word.args)

LARGE_CASES=((0,10**60+7),(10**60+7,0),(1,10**60+7),
             (10**30+3,10**50+9),(10**100+7,10**100+9))
def receipt():
    out=[]
    for a,b in ((0,1),(0,2),(0,3),(1,0),(1,1),(2,0),(2,3),*LARGE_CASES):
        for tail in ('102','120'):
            rows=[]
            for pair in PAIRS:
                c=witness(a,b,tail,pair);r=verify(c)
                fifth=to_fifth(c);r5=verify(fifth)
                rows.append({'exhibited':c,'replay':r,'fifth_generation':fifth,'fifth_replay':r5})
            out.append({'a':a,'b':b,'tail':tail,'certificates':rows})
    return {'schema':SCHEMA,'scope':'two infinite literal run families; no general PSC or BPA termination',
            'bound':5,'proof':'docs/two-tail-uniform.md','examples':out}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--a',type=int);parser.add_argument('--b',type=int)
    parser.add_argument('--tail',choices=['102','120'])
    parser.add_argument('--receipt',action='store_true')
    args=parser.parse_args()
    if args.receipt:out=receipt()
    else:
        require(args.a is not None and args.b is not None and args.tail is not None,'supply a,b,tail')
        out=[]
        for pair in PAIRS:
            c=to_fifth(witness(args.a,args.b,args.tail,pair));out.append({'certificate':c,'replay':verify(c)})
    print(json.dumps(out,indent=2,sort_keys=True))

if __name__=='__main__':main()

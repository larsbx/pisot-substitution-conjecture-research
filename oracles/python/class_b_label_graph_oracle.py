"""Independent Q(beta) graph reconstruction for two pilot fixtures.
Requires the native label exports to exist; never generates its own expectation.
"""
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'reference'))
sys.path.insert(0,str(ROOT/'oracles/python'))
from psc_research.overlap_graph import OverlapGraph,first_left_aligned_depths
from class_b_label_rays import read
from fractions import Fraction
from pathlib import Path

def run(branch,g,q):
 p=3*q+12-g if branch=='plus' else 3*q-g;r=q+(1 if branch=='plus' else -1)
 sigma={1:[1]+[3]*p+[1],2:[2]+[3]*q+[1],3:[2]+[3]*r+[1]}
 graph=OverlapGraph(sigma)
 if graph.capped:raise ValueError('cap')
 # Invert the independent oracle's length basis once over Fraction.
 A=[[graph.l[j][i] for j in range(3)]+[Fraction(i==j) for j in range(3)] for i in range(3)]
 for c in range(3):
  j=next(j for j in range(c,3) if A[j][c]);A[j],A[c]=A[c],A[j]
  z=A[c][c];A[c]=[v/z for v in A[c]]
  for j in range(3):
   if j!=c:
    z=A[j][c];A[j]=[a-z*b for a,b in zip(A[j],A[c])]
 depths=first_left_aligned_depths(graph);actual=set()
 for (t,b,shift),depth in zip(graph.states,depths):
  w=[sum(A[i][j+3]*shift[j] for j in range(3)) for i in range(3)]
  if any(x.denominator!=1 for x in w) or depth<0:raise ValueError('integrality/hitting')
  actual.add((t-1,b-1,*map(int,w),depth))
 path=ROOT / f'evidence/class-b-label-rays-2026-10-23/labels/{branch}-g{g}-q{q}.labels'
 _,expected=read(path)
 if actual!=set(expected):raise ValueError(('oracle mismatch',actual^set(expected)))
 print('INDEPENDENT_GRAPH_PASS',branch,g,q,len(actual),max(depths),flush=True)
if __name__ == '__main__':
 for args in [('plus',5,7),('minus',3,11)]:run(*args)

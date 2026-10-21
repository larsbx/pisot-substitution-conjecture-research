"""Independent exact finite calibration of the two uniform Mojo strip proofs."""
from pathlib import Path
import argparse
import json
import sys

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'reference'))
from psc_research.overlap_graph import OverlapGraph, first_left_aligned_depths


def specimen(a,b,cap=20000):
    if a not in (0,1) or b<1 or b>100:
        raise ValueError('finite calibration budget: a=0,1 and 1<=b<=100')
    p,q,r=3*a+5+b,3*a+6+b,2*a+4+b
    sigma={1:(1,)+(3,)*p+(2,),2:(2,)+(3,)*q+(1,),3:(2,)+(3,)*r+(2,)}
    graph=OverlapGraph(sigma,cap)
    if graph.capped:
        raise ValueError('capped seed graph is not a verdict')
    depths=first_left_aligned_depths(graph)
    bad=[i for i,d in enumerate(depths) if d<0]
    return dict(a=a,b=b,states=len(graph.states),max_depth=max(depths),non_hitting_indices=bad)


def compare_receipts(out,path):
    lines=Path(path).read_text().splitlines()
    strips={}
    for line in lines:
        if line.startswith('MINUS_STRIP_CERTIFIED '):
            tokens=line.split();a=int(tokens[1])
            if a in strips:
                raise ValueError('duplicate strip receipt')
            strips[a]=dict(threshold=int(tokens[4]),vertices=int(tokens[6]),finite=int(tokens[8]))
    if set(strips)!={0,1}:
        raise ValueError('both distinct strip receipts are required')
    if 'CLASS_D_MINUS_RESIDUAL_BH_CERTIFIED a>=0 b>=0 components=4 universal_139=open' not in lines:
        raise ValueError('native full-quadrant receipt missing')
    for row in out['samples']:
        strip=strips[row['a']]
        if row['non_hitting_indices'] or strip['finite']!=strip['threshold']:
            raise ValueError('non-hitting state or incomplete finite prefix')
        if row['b']-1>=strip['threshold'] and row['states']!=strip['vertices']:
            raise ValueError('independent tail vertex count disagrees')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--mojo-log');args=parser.parse_args()
    out=dict(authority='independent-Q(beta)-Python',uniform_proof=False,
             samples=[specimen(a,b) for a in (0,1) for b in (1,2,73)])
    print(json.dumps(out,indent=2),flush=True)
    if args.mojo_log:
        compare_receipts(out,args.mojo_log)
    if any(row['non_hitting_indices'] for row in out['samples']):
        raise SystemExit(1)


if __name__=='__main__':main()

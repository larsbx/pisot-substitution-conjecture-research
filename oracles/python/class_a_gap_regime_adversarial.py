"""Exact fixed-gap stress checks of existing regime tables, not a uniform-gap proof.

Replay: python oracles/python/class_a_gap_regime_adversarial.py
Uses the independent Fraction/Sturm ray verifier at d=1,000,003, all l>=64.
"""
import importlib.util,sys
from pathlib import Path
root=Path(__file__).resolve().parents[2]
for eps,kind,j,j1 in [(-1,0,0,0),(-1,1,3,0),(-1,2,3,4),(1,0,1,0),(1,1,5,0),(1,2,5,6)]:
 d=1000003
 r=j if kind==0 else d-j if kind==1 else (d+j-j1)//2
 sys.argv=['oracle','--ray',f'{d},{eps},{r}']
 spec=importlib.util.spec_from_file_location('independent_ray',root/'oracles/python/class_a_carrier_closure.py')
 o=importlib.util.module_from_spec(spec);spec.loader.exec_module(o)
 sign='minus' if eps==-1 else 'plus'
 suffix=('low'+str(j)) if kind==0 else ('high'+str(j)) if kind==1 else 'middle'
 rows=o._lists(root/f'kernel/psc/class_a_gap_regime_rows_{sign}.mojo','rows_'+suffix,8)
 pieces=o._lists(root/f'kernel/psc/class_a_gap_regime_descents_{sign}.mojo','pieces_'+suffix,8)
 desc=o._lists(root/f'kernel/psc/class_a_gap_regime_descents_{sign}.mojo','descents_'+suffix,9)
 assert rows and pieces and desc
 o._check_line()
 closure=o.verify_closure(rows,d*64+r)
 descent=o.verify_descent(rows,pieces,desc,d*64+r)
 print('ADVERSARIAL_RAY',eps,kind,j,'d',d,'r',r,'l>=64',closure,descent,flush=True)

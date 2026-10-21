"""Replay the uniform family identities or export one complete finite graph.

  mojo run -I . class_a_run_index.mojo [last_n=24]
  mojo run -I . class_a_run_index.mojo export N
  mojo run -I . class_a_run_index.mojo family N
"""
from std.sys import argv
from psc.class_a_run_index import verify_symbolic_identities, replay_family, probe


def main() raises:
    var args=argv()
    verify_symbolic_identities()
    if len(args)==3 and args[1]=="export":
        _=probe(Int(args[2]),True)
        return
    if len(args)==3 and args[1]=="family":
        _=replay_family(Int(args[2]),True)
        return
    if len(args)>2:
        raise Error("usage: [last_n] | export N | family N")
    var last=24 if len(args)==1 else Int(args[1])
    if last<4 or last>64:
        raise Error("complete-graph survey budget requires 4<=last_n<=64")
    for n in range(1,last+1):
        _=probe(n)
        if n>=4:
            _=replay_family(n,True)
    print("FINITE_SURVEY_COMPLETE",last,"universal_BH=false")

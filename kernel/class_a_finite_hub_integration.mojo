"""Export complete finite hub graphs for independent full adjacency comparison."""
from std.sys import argv
from psc.class_a_finite_hub_integration import finite_hub_audit

def main() raises:
    var args=argv()
    if len(args)!=4:raise Error("usage: MODE(4|9) K T; k,t=0..3 only")
    var result=finite_hub_audit(Int(args[1]),Int(args[2]),Int(args[3]),6000,True)
    var line="AUDIT"
    for v in result:line+=" "+String(v)
    print(line)

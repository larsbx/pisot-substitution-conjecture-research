"""Candidate certificate: entire minus b=0 line, conditional on successful execution.
Tail a>=2 uses polynomial inequalities; a=0,1 use complete exact seed graphs.
"""
from psc.class_d_minus_certificate import certify_minus_tail
from psc.class_d_boundary import boundary_probe


def main() raises:
    var tail = certify_minus_tail()
    print("minus b=0 a>=2: states targets seeds closure_candidates max_rank:", tail)
    for a in range(2):
        var row = boundary_probe(-1,a)
        if row[5] != 0:
            raise Error("base member has a target-free vertex")
        print("minus base a=",a,"states=",row[3],"max_half_depth=",row[4])
    print("certificate=MINUS_B0_ALL_A; positive_branch=OPEN; universal_PSC=OPEN")

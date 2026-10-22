"""Exact finite d=2 typed profiles and parity candidates. Not a theorem."""
from std.sys import argv
from psc.class_a_d2_parity_carrier import exact_profile, finite_parity_study


def main() raises:
    var args=argv()
    if len(args)==3 and args[1]=="export":
        _=exact_profile(Int(args[2]),True)
    elif len(args)==1:
        finite_parity_study()
    else:
        raise Error("usage: no args (finite parity study) or export N")

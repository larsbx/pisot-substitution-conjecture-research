"""Class-A d=2 plus line (n+2,n,n+1): assembled boundary-hitting theorem and per-n witnesses.

  mojo run -I . class_a_d2_plus_line.mojo theorem        # finite base, both rays, least floors, = #312 carriers
  mojo run -I . class_a_d2_plus_line.mojo witness N      # every step of the certificate at one n, 13<=N<=24
"""
from std.sys import argv
from psc.class_a_d2_plus_line import theorem, witness


def main() raises:
    var args = argv()
    if len(args) == 2 and args[1] == "theorem":
        theorem()
        return
    if len(args) == 3 and args[1] == "witness":
        _ = witness(Int(args[2]))
        return
    raise Error("usage: theorem | witness N")

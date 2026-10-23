"""Replay the class-A rectangular cover countermodel: [N=4], 4<=N<=256."""
from std.sys import argv
from psc.class_a_cover_obstruction import verify_cover_identities, replay_cover_escape

def main() raises:
    var args=argv()
    if len(args)>2:
        raise Error("usage: class_a_cover_obstruction [N]")
    var n=4 if len(args)==1 else Int(args[1])
    verify_cover_identities()
    replay_cover_escape(n)

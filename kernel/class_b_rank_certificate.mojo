"""Class-B piecewise rank certificate: all-parameter check and finite graph replay.

  check  CERT          every condition of psc.class_b_rank_certificate, all t >= 0
  replay CERT EXPORT   the two graph hypotheses on one native `edges` export

Neither mode is a boundary-hitting certificate on its own; see the module docs.
"""
from std.sys import argv
from std.collections import Dict, Set
from psc.class_b_rank_certificate import RankCertificate, check_rank_certificate, piece_of, child_label


def _read(path: String) raises -> String:
    with open(path, "r") as f:
        return f.read()


def _key(row: List[Int], start: Int) -> String:
    var out = String("")
    for h in range(start, start + 5):
        out += String(row[h]) + " "
    return out^


def replay(cert: RankCertificate, export: String) raises -> String:
    var lines = export.splitlines()
    var h = lines[0].split(" ")
    if len(h) != 4 or String(h[0]) != "M":
        raise Error("invalid export header")
    var q = Int(h[1])
    if q < cert.q0 or (q - cert.q0) % cert.gap != 0:
        raise Error("export member is not on the certificate ray")
    var t = (q - cert.q0) // cert.gap
    var vertices = List[List[Int]]()
    var known = Set[String]()
    var actual = Set[String]()
    for line in lines[1:]:
        var p = line.split(" ")
        var row = List[Int]()
        for x in p[1:]:
            row.append(Int(x))
        if String(p[0]) == "V":
            known.add(_key(row, 0))
            vertices.append(row^)
        elif String(p[0]) == "E":
            actual.add(_key(row, 0) + "| " + _key(row, 5))
    if len(vertices) != Int(h[2]):
        raise Error("export vertex count mismatch")
    # Hypothesis 1 at this member: every vertex lies in a piece.
    var held = List[Int](length=len(cert.pieces), fill=0)
    for v in vertices:
        var i = piece_of(cert, t, v)
        if i < 0:
            raise Error("REPLAY_REFUSED vertex outside every piece: " + _key(v, 0))
        held[i] += 1
    var missing = 0
    for i in range(len(cert.pieces)):
        missing += cert.pieces[i].hi.at(t) - cert.pieces[i].lo.at(t) + 1 - held[i]
    # Hypothesis 2 at this member: every chosen symbolic edge is an actual edge
    # at every lattice point of its domain whose parent is a vertex.
    var checked = 0
    for e in range(len(cert.edges)):
        ref p = cert.pieces[cert.edges[e].parent]
        for k in range(cert.edges[e].lo.at(t), cert.edges[e].hi.at(t) + 1):
            var parent: List[Int] = [p.top, p.bottom, k, 3 * k + p.d, p.s - 6 * k - p.d]
            if _key(parent, 0) not in known:
                continue
            var child = child_label(cert, e, k)
            if _key(parent, 0) + "| " + _key(child, 0) not in actual:
                raise Error("REPLAY_REFUSED symbolic edge is not an actual edge at " + _key(parent, 0))
            if cert.potential(cert.edges[e].child, t, child[2]) >= cert.potential(cert.edges[e].parent, t, k):
                raise Error("potential does not decrease on a replayed edge")
            checked += 1
    return ("RANK_REPLAY_PASS q " + String(q) + " vertices " + String(len(vertices)) + " edges_checked "
            + String(checked) + " carrier_points_without_vertex " + String(missing))


def main() raises:
    var args = argv()
    if len(args) == 3 and String(args[1]) == "check":
        var cert = RankCertificate(_read(String(args[2])))
        var horizon = check_rank_certificate(cert)
        print("RANK_CERT_PASS pieces", len(cert.pieces), "edges", len(cert.edges), "coverage_horizon_t", horizon,
              "; conditional on carrier inclusion and actual symbolic edges for every t")
    elif len(args) == 4 and String(args[1]) == "replay":
        var cert = RankCertificate(_read(String(args[2])))
        _ = check_rank_certificate(cert)
        print(replay(cert, _read(String(args[3]))))
    else:
        raise Error("usage: check CERT | replay CERT EXPORT")

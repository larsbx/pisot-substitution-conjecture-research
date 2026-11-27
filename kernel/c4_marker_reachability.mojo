"""Replay a specified periodic seam pair or check a saved certificate."""

from std.sys import argv
from psc.c4_marker_reachability import (
    MarkerRayDecision, Seam, SeamPair, decide_marker_ray, verify_marker_certificate,
)
from psc.symmetry import word_key
from substitution_dynamics.symmetry import parse_substitution_key


def _seam(key: String) raises -> Seam:
    var bytes = key.as_bytes()
    if len(bytes) != 2 or bytes[0] < 48 or bytes[0] > 50 or bytes[1] < 48 or bytes[1] > 50:
        raise Error("a seam is two letter digits, for example 00")
    return Seam(Int(bytes[0]) - 48, Int(bytes[1]) - 48)


def _ints(values: List[Int]) -> String:
    var fields = List[String]()
    for value in values:
        fields.append(String(value))
    return String(",").join(fields)


def _emit(result: MarkerRayDecision, side: String):
    if result.violation:
        ref v = result.violation.value()
        print("violation", side, len(v.top_word), word_key(v.top_word), word_key(v.bottom_word),
              v.top_next, v.bottom_next, _ints(v.balance), v.top_markers, v.bottom_markers,
              v.required_parity, Int(v.same_last_group), Int(v.same_next_group),
              _ints(v.top_path), _ints(v.bottom_path), sep="\t")
    else:
        print("certificate", side, _ints(result.certificate), sep="\t")


def _check(path: String) raises:
    var saved: String
    with open(path, "r") as file:
        saved = file.read()
    var lines = saved.strip().split("\n")
    var header = lines[0].split("\t")
    if len(header) != 5 or String(header[0]) != "c4-marker-v1":
        raise Error("unrecognized marker certificate header")
    var source = String(header[1])
    var sigma = parse_substitution_key(source, len(source.split("/")))
    var pair = SeamPair(_seam(String(header[2])), _seam(String(header[3])), _seam(String(header[4])))
    var right = False
    var left = False
    for i in range(1, len(lines)):
        var row = lines[i].split("\t")
        if len(row) != 3 or String(row[0]) != "certificate" or (
            String(row[1]) != "right" and String(row[1]) != "left"
        ):
            raise Error("expected a marker certificate row")
        var leftward = String(row[1]) == "left"
        if (leftward and left) or (not leftward and right):
            raise Error("duplicate certificate for one direction")
        var states = List[Int]()
        for key in row[2].split(","):
            states.append(atol(String(key)))
        if not verify_marker_certificate(sigma, pair, leftward, states):
            raise Error("invalid marker reachability certificate")
        left = left or leftward
        right = right or not leftward
    if not (left or right):
        raise Error("no marker certificate rows")
    if left and right:
        print("verified both directions")
    else:
        print("verified", "left" if left else "right", "direction")


def main() raises:
    var args = argv()
    if len(args) == 3 and args[1] == "check":
        _check(String(args[2]))
        return
    if len(args) != 5 and len(args) != 6:
        raise Error("usage: c4_marker_reachability IMAGES MARKER TOP BOTTOM [right|left|both], or check FILE")
    var source = String(args[1])
    var sigma = parse_substitution_key(source, len(source.split("/")))
    var pair = SeamPair(_seam(String(args[2])), _seam(String(args[3])), _seam(String(args[4])))
    var side = String(args[5]) if len(args) == 6 else String("both")
    if side != "right" and side != "left" and side != "both":
        raise Error("direction must be right, left, or both")
    print("c4-marker-v1", source, args[2], args[3], args[4], sep="\t")
    if side != "left":
        var right = decide_marker_ray(sigma, pair)
        _emit(right, "right")
        if right.violation:
            return
    if side != "right":
        _emit(decide_marker_ray(sigma, pair, leftward=True), "left")

"""Export complete bounded matrix quotients, literal marks and support profiles.

No line authenticates compact tiles, all-level equality, or compact overlap
measure.  The previous physical forward-leak calibration is replayed unchanged.
"""

from finite_linear_algebra.madic_ball import contains
from psc.c4_bounded_cover import forward_leak_control
from psc.c4_madic_residue import (
    ResidueLevel, residue_fixture, residue_summary, verify_madic_residue,
    residue_class, profile_intersection, residue_refusal,
)


def _line(kind: String, prefix: List[Int], values: List[Int]) -> String:
    var result = kind.copy()
    for value in prefix:
        result += String(" ")+String(value)
    for value in values:
        result += String(" ")+String(value)
    return result^


def _level(fixture: Int, level: ResidueLevel) raises:
    var q = level.depth
    print(_line("level",[fixture,q],[level.determinant,level.index,level.candidates]))
    print(_line("power",[fixture,q],level.matrix.e))
    print(_line("adjugate",[fixture,q],level.adjugate.e))
    print(_line("smith",[fixture,q],level.smith))
    for identity in range(level.index):
        print(_line("representative",[fixture,q,identity],level.representatives[identity]))
    for identity in range(level.index):
        print(_line("add",[fixture,q,identity],level.addition[identity]))
    print(_line("generators",[fixture,q],level.generators))
    print(_line("inverse",[fixture,q],level.inverse))
    print(_line("orders",[fixture,q],level.orders))
    print(_line("action",[fixture,q],level.action))
    print(_line("reduce",[fixture,q],level.reduction))
    for source in range(3):
        print(_line("word",[fixture,q,source,len(level.words[source])],level.words[source]))
    for identity in range(len(level.occurrences)):
        print(_line("occurrence",[fixture,q,identity],level.occurrences[identity]))
    for row in level.counts:
        print(_line("count",[fixture,q],row))
    for letter in range(3):
        print(_line("profile",[fixture,q,letter,len(level.profiles[letter])],level.profiles[letter]))
    print(_line("summary",[fixture,q],residue_summary(level)))


def main() raises:
    print("schema c4-madic-residue-v1")
    print("limits",6,64,192,729,2187)
    var levels = 0
    var classes = 0
    var occurrences = 0
    for fixture in range(4):
        var certificate = residue_fixture(fixture)
        verify_madic_residue(certificate)
        print(_line("fixture",[fixture],[certificate.depth,certificate.determinant,
            certificate.index_cap,certificate.candidate_cap,certificate.word_cap,certificate.occurrence_cap]))
        for source in range(3):
            print(_line("image",[fixture,source,len(certificate.images[source])],certificate.images[source]))
        print(_line("incidence",[fixture],certificate.matrix.e))
        for level in certificate.levels:
            _level(fixture,level)
            levels += 1
            classes += level.index
            occurrences += len(level.occurrences)
    var named = residue_fixture(0)
    var level2 = named.levels[2].copy()
    print(_line("control noncyclic",[0,2],level2.orders))
    var collision = -1
    for identity in range(1,level2.index):
        if level2.action[identity] == 0:
            collision = identity
            break
    if collision < 1:
        raise Error("named finite-action collision disappeared")
    print("control action_collision",0,2,0,collision,0)
    for query in range(2):
        var shift: List[Int] = [query,0,0]
        var intersection = profile_intersection(level2,2,2,shift)
        print(_line("profile_query",[0,2,2,2,shift[0],shift[1],shift[2],len(intersection)],intersection))
    # At q=2 every class has order <=2, so those queries alone cannot
    # distinguish the overlap's +shift convention from its negative.
    for sign in range(2):
        var shift: List[Int] = [1 if sign == 0 else -1,0,0]
        var intersection = profile_intersection(named.levels[3],0,0,shift)
        print(_line("profile_query",[0,3,0,0,shift[0],shift[1],shift[2],len(intersection)],intersection))
    var transposed: List[Int] = [named.matrix.at(0,0),named.matrix.at(1,0),named.matrix.at(2,0),
        named.matrix.at(0,1),named.matrix.at(1,1),named.matrix.at(2,1),
        named.matrix.at(0,2),named.matrix.at(1,2),named.matrix.at(2,2)]
    var column_witness = False
    for axis in range(3):
        var column: List[Int] = [named.levels[4].matrix.at(0,axis),
            named.levels[4].matrix.at(1,axis),named.levels[4].matrix.at(2,axis)]
        if not contains(transposed,3,4,column):
            if not contains(named.matrix.e,3,4,column):
                raise Error("actual power column is missing from column lattice")
            print(_line("control column_lattice",[0,4,axis],column))
            column_witness = True
            break
    if not column_witness:
        raise Error("named row/column lattice countercontrol disappeared")
    var doubled = residue_fixture(3)
    var lower = residue_class(doubled.levels[1],[2,0,0])
    var upper = residue_class(doubled.levels[2],[2,0,0])
    if lower != 0 or upper == 0:
        raise Error("finite-depth alias countercontrol disappeared")
    print("control finite_alias",3,1,2,0,0,lower,upper)
    var unit = residue_fixture(2)
    print("control unit_alias",2,3,1,0,0,residue_class(unit.levels[3],[1,0,0]))
    for control in range(8):
        residue_refusal(control)
        print("refusal",control,1)
    var leak = forward_leak_control()
    print(_line("control forward_leak",[],leak))
    print("total",4,levels,classes,occurrences)

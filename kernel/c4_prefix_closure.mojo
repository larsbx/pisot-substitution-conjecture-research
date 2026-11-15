"""Export complete finite prefix windows and every literal occurrence address.

No packet authenticates a compact stable enclosure or compact overlap measure.
The existing inverse-closed forward-leak calibration is replayed unchanged.
"""

from psc.c4_bounded_cover import forward_leak_control
from psc.c4_prefix_closure import (
    PrefixClosure, prefix_fixture, verify_prefix_closure, prefix_summary,
    lookup_prefix_address, prefix_same_residue_control, prefix_refusal,
)


def _line(kind: String, prefix: List[Int], values: List[Int]) -> String:
    var result = kind.copy()
    for value in prefix:
        result += String(" ")+String(value)
    for value in values:
        result += String(" ")+String(value)
    return result^


def _certificate(fixture: Int, certificate: PrefixClosure) raises:
    print(_line("fixture",[fixture],[certificate.period,certificate.generations,
        certificate.word_cap,certificate.occurrence_cap]))
    for source in range(3):
        print(_line("image",[fixture,source,len(certificate.images[source])],certificate.images[source]))
    print(_line("incidence",[fixture],certificate.matrix))
    for source in range(3):
        print(_line("block_image",[fixture,source,len(certificate.block_images[source])],certificate.block_images[source]))
    print(_line("block_incidence",[fixture],certificate.block_matrix))
    print(_line("seed",[fixture,len(certificate.seed)],certificate.seed))
    for identity in range(len(certificate.marks)):
        print(_line("mark",[fixture,identity],certificate.marks[identity]))
        print(_line("mark_before",[fixture,identity,len(certificate.mark_before[identity])],certificate.mark_before[identity]))
        print(_line("mark_after",[fixture,identity,len(certificate.mark_after[identity])],certificate.mark_after[identity]))
    for generation in range(len(certificate.windows)):
        print(_line("window",[fixture,generation,certificate.period*generation,
            len(certificate.windows[generation])],certificate.windows[generation]))
    for generation in range(certificate.generations):
        ref transition = certificate.transitions[generation]
        for cut in transition.cuts:
            print(_line("cut",[fixture,generation],cut))
        for identity in range(len(transition.occurrences)):
            print(_line("address",[fixture,generation,identity],transition.occurrences[identity]))
        print(_line("summary",[fixture,generation],prefix_summary(certificate,generation)))


def main() raises:
    print("schema c4-prefix-closure-v1")
    print("limits",3,3,3,32,4096,12288)
    var windows = 0
    var transitions = 0
    var marks = 0
    var occurrences = 0
    for fixture in range(4):
        var certificate = prefix_fixture(fixture)
        verify_prefix_closure(certificate)
        _certificate(fixture,certificate)
        windows += len(certificate.windows)
        transitions += len(certificate.transitions)
        marks += len(certificate.marks)
        for transition in certificate.transitions:
            occurrences += len(transition.occurrences)
    print(_line("control same_residue",[],prefix_same_residue_control()))
    var named = prefix_fixture(0)
    var source_length = len(named.windows[0])
    print(_line("control truncated_successor",[0,0,source_length,len(named.windows[1])],
        lookup_prefix_address(named,0,source_length)))
    print(_line("control terminal_cut",[0,0],named.transitions[0].cuts[source_length]))
    var doubled = prefix_fixture(3)
    var final_summary = prefix_summary(doubled,2)
    print(_line("control finite_letter_support",[3,3],
        [final_summary[7],final_summary[8],final_summary[9]]))
    for control in range(14):
        prefix_refusal(control)
        print("refusal",control,1)
    print(_line("control forward_leak",[],forward_leak_control()))
    print("total",4,windows,transitions,marks,occurrences)

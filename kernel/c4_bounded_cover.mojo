"""Export complete bounded inverse histories and arithmetic countercontrols."""

from psc.c4_bounded_cover import fixture_cover, cover_summary, cover_countercontrols


def _line(kind: String, fixture: Int, identity: Int, values: List[Int]) -> String:
    var result = kind+String(" ")+String(fixture)+String(" ")+String(identity)
    for value in values:
        result += String(" ")+String(value)
    return result^


def main() raises:
    print("schema c4-bounded-cover-v1")
    print("limits",6,27,64,4096,20000,200000,100000)
    var total_nodes = 0
    var total_candidates = 0
    var total_leaves = 0
    for fixture in range(4):
        var cover = fixture_cover(fixture)
        print("fixture",fixture,cover.depth,cover.determinant)
        for letter in range(3):
            var word: List[Int] = [len(cover.images[letter])]
            for selected in cover.images[letter]:
                word.append(selected)
            print(_line("image",fixture,letter,word))
        for root in range(len(cover.roots)):
            print(_line("root",fixture,root,cover.roots[root]))
        for state in range(len(cover.domain)):
            print(_line("domain",fixture,state,cover.domain[state]))
        for digit in range(len(cover.digits)):
            print(_line("digit",fixture,digit,cover.digits[digit]))
        for node in range(len(cover.nodes)):
            print(_line("node",fixture,node,cover.nodes[node]))
        for candidate in cover.candidates:
            print("candidate",fixture,candidate[0],candidate[1],candidate[2],candidate[3],candidate[4])
        var summary = cover_summary(cover)
        var line = String("summary ")+String(fixture)
        for value in summary:
            line += String(" ")+String(value)
        print(line)
        total_nodes += summary[0]
        total_candidates += summary[1]
        total_leaves += summary[4]
    var controls = cover_countercontrols()
    var names: List[String] = ["missing_reflection","physical_not_compact","false_enclosure","boundary_contact","redundant_occurrence","missing_piece","internally_complete_not_cover","forward_leak"]
    for i in range(len(controls)):
        var line = String("control ")+names[i]
        for value in controls[i]:
            line += String(" ")+String(value)
        print(line)
    print("total",4,total_nodes,total_candidates,total_leaves)

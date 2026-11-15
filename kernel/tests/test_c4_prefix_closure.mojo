"""Full finite-window addressing, productive seed premises, and failed extensions."""

from std.testing import assert_equal, assert_true, assert_false
from mojo_smoke.claims import require_contract
from substitution_dynamics.substitution import Substitution
from psc.words import parikh
from psc.c4_bounded_cover import forward_leak_control
from psc.c4_madic_residue import residue_fixture_images
from psc.c4_prefix_closure import (
    PrefixClosure, build_prefix_closure, bind_prefix_windows, verify_prefix_closure,
    prefix_fixture, prefix_summary, lookup_prefix_address,
    prefix_same_residue_control, prefix_refusal,
)


def _slice(word: List[Int], start: Int, end: Int) -> List[Int]:
    var result = List[Int]()
    for position in range(start,end):
        result.append(word[position])
    return result^


def _reject(certificate: PrefixClosure) raises:
    var refused = False
    try:
        verify_prefix_closure(certificate)
    except:
        refused = True
    assert_true(refused)


def test_complete_windows_and_full_literal_marks() raises:
    var windows = 0
    var transitions = 0
    var marks = 0
    var occurrences = 0
    for fixture in range(4):
        var certificate = prefix_fixture(fixture)
        verify_prefix_closure(certificate)
        var rebound = bind_prefix_windows(certificate.images,certificate.period,
            certificate.seed,certificate.windows)
        assert_equal(rebound.windows[3],certificate.windows[3])
        var tau = Substitution.checked(certificate.block_images)
        for mark_id in range(len(certificate.marks)):
            ref mark = certificate.marks[mark_id]
            var reconstructed = certificate.mark_before[mark_id].copy()
            reconstructed.append(mark[2])
            for letter in certificate.mark_after[mark_id]:
                reconstructed.append(letter)
            assert_equal(reconstructed,certificate.block_images[mark[0]])
            assert_equal(len(certificate.mark_before[mark_id]),mark[1])
        for generation in range(certificate.generations):
            ref source = certificate.windows[generation]
            ref target = certificate.windows[generation+1]
            ref transition = certificate.transitions[generation]
            assert_equal(len(transition.cuts),len(source)+1)
            assert_equal(len(transition.occurrences),len(target))
            assert_equal(transition.cuts[len(source)][1],len(target))
            for global_position in range(len(target)):
                var row = lookup_prefix_address(certificate,generation,global_position)
                assert_equal(row[4],global_position)
                assert_equal(row[1],source[row[0]])
                assert_equal(row[5],target[global_position])
                ref mark = certificate.marks[row[2]]
                assert_equal(mark[0],row[1])
                assert_equal(mark[1],row[3])
                assert_equal(mark[2],row[5])
                # Test the literal before AND after identity independently of
                # the constructor's streaming prefix Parikh recurrence.
                var before = tau.apply(_slice(source,0,row[0]))
                for letter in certificate.mark_before[row[2]]:
                    before.append(letter)
                var after = certificate.mark_after[row[2]].copy()
                var expanded_after = tau.apply(_slice(source,row[0]+1,len(source)))
                for letter in expanded_after:
                    after.append(letter)
                assert_equal(before,_slice(target,0,global_position))
                assert_equal(after,_slice(target,global_position+1,len(target)))
                assert_equal(parikh(before),[row[15],row[16],row[17]])
                assert_equal(parikh(_slice(source,0,row[0])),[row[6],row[7],row[8]])
            occurrences += len(transition.occurrences)
        windows += len(certificate.windows)
        transitions += len(certificate.transitions)
        marks += len(certificate.marks)
        print("C4_PREFIX_FIXTURE",fixture,certificate.period,len(certificate.windows[3]))
    assert_equal(windows,16)
    assert_equal(transitions,12)
    assert_equal(marks,41)
    assert_equal(occurrences,221)
    print("C4_PREFIX_COMPLETE_INVENTORY",windows,transitions,marks,occurrences)


def test_period_scale_endpoints_and_distinct_addresses() raises:
    var named = prefix_fixture(0)
    assert_equal(named.block_images[0],[0,2,1])
    assert_equal(named.block_images[1],[1,0,0,1,0,2,1])
    assert_equal(named.block_images[2],[1,1,0,2,1])
    assert_equal(named.block_matrix,[1,3,1,1,3,3,1,1,1])
    assert_equal(prefix_summary(named,0),[1,3,2,3,1,0,0,1,1,1])
    assert_equal(prefix_summary(named,1),[3,15,4,15,1,1,1,5,7,3])
    assert_equal(prefix_summary(named,2),[15,79,16,79,5,7,3,29,35,15])
    assert_equal(named.transitions[2].cuts[15],[15,79,5,7,3,29,35,15])
    assert_equal(named.marks[6],[1,3,1,2,1,0,1,1,1])
    assert_equal(lookup_prefix_address(named,2,29),
        [5,0,0,0,29,0,1,3,1,11,13,5,0,0,0,11,13,5])
    assert_equal(prefix_same_residue_control(),[0,2,2,0,29,0,5,0,0,0])
    # Each nonterminal parent boundary belongs to the next block at local 0.
    for cut in range(len(named.windows[2])):
        var global_position = named.transitions[2].cuts[cut][1]
        var address = lookup_prefix_address(named,2,global_position)
        assert_equal(address[0],cut)
        assert_equal(address[3],0)
    # U is a genuine prefix of tau(U), but using U as its full child window
    # would omit the actual position |U|.  The terminal position is different.
    var first_missing = lookup_prefix_address(named,0,len(named.windows[0]))
    assert_equal(first_missing[0],0)
    assert_equal(first_missing[3],1)
    assert_equal(first_missing[4],1)
    assert_equal(first_missing[5],2)
    var reordered = prefix_fixture(1)
    assert_equal(named.matrix,reordered.matrix)
    assert_equal(named.block_matrix,reordered.block_matrix)
    assert_false(named.windows[1] == reordered.windows[1])
    # Singular incidence is allowed: the prefix identity needs no inverse.
    var singular = build_prefix_closure([[0,0],[0,0],[0,0]],1,[0],3)
    assert_equal(len(singular.windows[3]),8)
    var longer_seed = build_prefix_closure(residue_fixture_images(2),1,[0,1],3)
    assert_equal(len(longer_seed.windows[3]),13)
    var doubled = prefix_fixture(3)
    assert_equal(prefix_summary(doubled,2),[4,8,5,8,4,0,0,8,0,0])
    # This reports finite letter support only; the generic constructor never
    # infers all-letter occurrence or infinite absence from a finite window.
    print("C4_PREFIX_PERIOD_AND_ADDRESS_SCOPE",2,0,29,0)


def test_every_submitted_field_is_authenticated() raises:
    var canonical = prefix_fixture(0)
    for mutation in range(32):
        var altered = canonical.copy()
        if mutation == 0:
            altered.matrix[0] += 1
        elif mutation == 1:
            altered.block_matrix[0] += 1
        elif mutation == 2:
            altered.block_images[0] = [0,1,2]
        elif mutation == 3:
            altered.marks[6][1] = 6
        elif mutation == 4:
            altered.marks[6][3] += 1
        elif mutation == 5:
            altered.mark_before[6][0] = 2
        elif mutation == 6:
            altered.mark_after[6][0] = 2
        elif mutation == 7:
            _ = altered.marks.pop()
        elif mutation == 8:
            altered.marks.append(altered.marks[6].copy())
        elif mutation == 9:
            _ = altered.windows[1].pop()
        elif mutation == 10:
            altered.windows[1] = [0,1,2]
        elif mutation == 11:
            altered.windows[3].append(0)
        elif mutation == 12:
            _ = altered.windows.pop()
        elif mutation == 13:
            _ = altered.transitions[2].cuts.pop()
        elif mutation == 14:
            altered.transitions[1].cuts[1][1] += 1
        elif mutation == 15:
            altered.transitions[2].cuts[5][2] += 1
        elif mutation == 16:
            altered.transitions[2].occurrences[29][0] = 0
        elif mutation == 17:
            altered.transitions[2].occurrences[29][2] = 1
        elif mutation == 18:
            altered.transitions[2].occurrences[29][3] = 1
        elif mutation == 19:
            altered.transitions[2].occurrences[29][4] = 30
        elif mutation == 20:
            altered.transitions[2].occurrences[29][5] = 1
        elif mutation == 21:
            altered.transitions[2].occurrences[29][6] += 1
        elif mutation == 22:
            altered.transitions[2].occurrences[29][9] += 1
        elif mutation == 23:
            altered.transitions[2].occurrences[29][12] += 1
        elif mutation == 24:
            altered.transitions[2].occurrences[29][15] += 1
        elif mutation == 25:
            _ = altered.transitions[2].occurrences.pop()
        elif mutation == 26:
            altered.transitions[2].occurrences.append(altered.transitions[2].occurrences[29].copy())
        elif mutation == 27:
            # Same selected letter and same residue; still a different mark.
            altered.transitions[2].occurrences[0] = altered.transitions[2].occurrences[29].copy()
        elif mutation == 28:
            altered.transitions[2].generation = 0
        elif mutation == 29:
            _ = altered.transitions.pop()
        elif mutation == 30:
            altered.transitions[2].cuts[5][5] += 1
        else:
            altered.seed = []
        _reject(altered)
    print("C4_PREFIX_INVENTORY_MUTATIONS",32)


def test_constructor_restrictions_and_complete_budget_refusals() raises:
    for control in range(14):
        prefix_refusal(control)
    var exact = build_prefix_closure(residue_fixture_images(0),2,[0],3,
        word_cap=79,occurrence_cap=97)
    assert_equal(len(exact.windows[3]),79)
    for control in range(20):
        var refused = False
        try:
            if control == 0:
                _ = build_prefix_closure([[0,0],[1]],1,[0],1)
            elif control == 1:
                _ = build_prefix_closure([[0,0,0,0],[1],[2]],1,[0],1)
            elif control == 2:
                _ = build_prefix_closure([[0,3],[1],[2]],1,[0],1)
            elif control == 3:
                _ = build_prefix_closure(residue_fixture_images(0),2,[-1],1)
            elif control == 4:
                _ = build_prefix_closure(residue_fixture_images(0),2,[3],1)
            elif control == 5:
                var seed = List[Int](length=33,fill=0)
                _ = build_prefix_closure(residue_fixture_images(3),1,seed,1)
            elif control == 6:
                _ = build_prefix_closure(residue_fixture_images(0),0,[0],1)
            elif control == 7:
                _ = build_prefix_closure(residue_fixture_images(0),-1,[0],1)
            elif control == 8:
                _ = build_prefix_closure(residue_fixture_images(0),2,[0],0)
            elif control == 9:
                _ = build_prefix_closure(residue_fixture_images(0),2,[0],-1)
            elif control == 10:
                _ = build_prefix_closure(residue_fixture_images(0),2,[0],1,word_cap=0)
            elif control == 11:
                _ = build_prefix_closure(residue_fixture_images(0),2,[0],1,word_cap=4097)
            elif control == 12:
                _ = build_prefix_closure(residue_fixture_images(0),2,[0],1,occurrence_cap=0)
            elif control == 13:
                _ = build_prefix_closure(residue_fixture_images(0),2,[0],1,occurrence_cap=12289)
            elif control == 14:
                _ = bind_prefix_windows(residue_fixture_images(0),2,[0],[])
            elif control == 15:
                var named = prefix_fixture(0)
                var skipped = List[List[Int]]()
                skipped.append(named.windows[0].copy())
                skipped.append(named.windows[2].copy())
                _ = bind_prefix_windows(named.images,2,[0],skipped)
            elif control == 16:
                _ = bind_prefix_windows(residue_fixture_images(0),2,[0],[[1],[0,2,1]])
            elif control == 17:
                _ = lookup_prefix_address(prefix_fixture(0),0,-1)
            elif control == 18:
                _ = lookup_prefix_address(prefix_fixture(0),3,0)
            else:
                _ = lookup_prefix_address(prefix_fixture(0),2,79)
        except:
            refused = True
        assert_true(refused)
    assert_equal(forward_leak_control(),[4,2,2])
    print("C4_PREFIX_REFUSALS",14,20)
    print("C4_PREFIX_FORWARD_LEAK",4,2,2)


def main() raises:
    test_complete_windows_and_full_literal_marks()
    test_period_scale_endpoints_and_distinct_addresses()
    test_every_submitted_field_is_authenticated()
    test_constructor_restrictions_and_complete_budget_refusals()
    require_contract("C4 bounded full prefix windows retain every literal parent/local address and exact incidence transport")
    require_contract("C4 prefix constructor refuses incomplete windows and preserves period, terminal-cut, residue-multiplicity and forward-leak controls")

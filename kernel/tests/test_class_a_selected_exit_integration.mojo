"""Universal integer recipe guards plus independent native literal geometry."""
from std.testing import assert_true
from mojo_smoke.claims import require_contract
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, selected_overlap_child, interior_overlap_cached
from psc.class_a_selected_recipe_tables import recipe_rows, recipe_sources
from psc.class_a_selected_exit_integration import certify_selected_recipes, verify_selected_recipe_path, certify_selected_label, first_choice_source, first_choice_allowed
from psc.class_a_boundary_children import geometric_state, BoundaryLabel
from psc.class_a_boundary_u_children import reverse_label
from psc.perron_field3 import CubicElt
from std.collections import Dict


def main() raises:
    var rows=recipe_rows()
    var symbolic=certify_selected_recipes(rows)
    assert_true(symbolic>0)
    var actual=0
    for k in range(5):
        for t in range(4):
            var n=k+t+3
            var d=k+2*t+5
            var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n-1))
            for family in range(3):
                var cache=Dict[CubicElt,Int]()
                var candidates=recipe_sources(family)
                for flip in range(2):
                    var label=first_choice_source(family)
                    var state=geometric_state(tables,reverse_label(label) if flip==1 else label)
                    var accepted=0
                    for i in range(len(tables.sigma[state.top])):
                        for j in range(len(tables.sigma[state.bottom])):
                            var child=selected_overlap_child(tables,state,i,j)
                            var allowed=first_choice_allowed(family,k,t,j if flip==1 else i,i if flip==1 else j)
                            assert_true(interior_overlap_cached(tables,cache,child)==allowed)
                            if not allowed:continue
                            accepted+=1
                            var found=False
                            for candidate in candidates:
                                var oriented=reverse_label(candidate) if flip==1 else candidate
                                found=found or geometric_state(tables,oriented)==child
                            assert_true(found)
                    assert_true(accepted==(2*n+1 if family==0 else (4 if family==1 else 2*n+3)))
                for source in range(len(candidates)):
                    for flip in range(2):
                        verify_selected_recipe_path(tables,rows,family,source,k,t,flip)
                        actual+=1
    # A changed ordinal or typed target must fail a universal identity/guard.
    rows[0][4]+=1
    var refused=False
    try:
        _=certify_selected_recipes(rows,False)
    except:
        refused=True
    assert_true(refused)
    rows=recipe_rows()
    rows[0][0]=99
    refused=False
    try:
        _=certify_selected_recipes(rows,False)
    except:
        refused=True
    assert_true(refused)
    refused=False
    try:
        certify_selected_label(BoundaryLabel(0,0,0,0,100))
    except:
        refused=True
    assert_true(refused)
    print("CLASS_A_SELECTED_EXIT_INTEGRATION symbolic_oriented_edges",symbolic,"native_paths",actual)
    require_contract("minus class-A CY/CC/X selected tails: 12 exhaustive rectangular integer chambers, all affine actual-prefix coefficient identities and word guards, strict labels on inherited Perron polygon, typed coincidence terminals, bounded native occurrence/geometry/reversal cross-checks and corrupted-ordinal refusal; complete-star arguments remain separately scoped; no all-later-choice or general PSC theorem")

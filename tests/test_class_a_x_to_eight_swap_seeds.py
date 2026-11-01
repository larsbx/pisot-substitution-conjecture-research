"""Universal X-to-eight swap paths; S1/E6 remains distinct."""
from pathlib import Path
import runpy
import pytest
source=runpy.run_path(str(Path(__file__).resolve().parents[1]/
    'oracles/python/class_a_x_to_eight_swap_seeds.py'))

def test_all_parameter_affine_word_transport_and_strict_margins():
    r=source['symbolic_certificate']()
    assert r['eight_swap_seeds']==8
    assert r['unique_affine_transitions']==18
    assert r['exact_symbolic_oriented_path_edges']==70
    assert r['base_path_states']==19
    assert r['oriented_path_states']==30
    assert r['strict_physical_margins']==60
    assert r['max_X_to_seed_depth']==6
    assert r['S1_in_X_SCC_unproved']
    assert r['all_descendants_reach_X_unproved']
    assert not r['universal_BH']

def test_independent_fraction_word_oracle_117_parameter_specimens():
    assert source['literal_probe']()==dict(exact_Fraction_specimens=117,
                                         actual_oriented_forward_edges=8190)

def test_real_reversal_and_every_selected_seed_not_s1():
    eight=source['EIGHT']
    assert len(eight)==8 and source['S1'] not in eight
    assert set(eight)==set(source['SEEDS'])-{source['S1']}
    for seed in eight:
        steps=source['path'](seed)
        assert steps[-1][2]==seed
        state=source['X']
        for i,j,target in steps:
            source['base']['certified_transport'](state,i,j,target)
            source['base']['certified_transport'](source['reverse'](state),j,i,source['reverse'](target))
            state=target
        assert state==seed
    with pytest.raises(ValueError):source['path'](source['S1'])

def test_bad_affine_index_and_wrong_target_refused():
    old=source['X']
    with pytest.raises(AssertionError):
        source['base']['certified_transport'](old,source['Aff'](k=-1,c=999),0,
                                            (2,0,0,-1,0))
    with pytest.raises(AssertionError):
        source['base']['certified_transport'](old,source['Aff'](1,2,7),0,
                                            (2,0,0,-1,1))
    with pytest.raises(AssertionError):
        source['base']['strict']((0,0,0,0,999))

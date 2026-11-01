"""Independent verifier of proof-carrying finite quotient rank forests."""
from pathlib import Path
import runpy
import pytest

m=runpy.run_path(str(Path(__file__).resolve().parents[1]/
                     'oracles/python/class_a_reversal_rank_certificate.py'))
EXPECTED_X={
 (0,0):(393,391,7),(0,1):(506,504,8),(0,2):(611,609,8),
 (0,3):(720,718,8),(1,0):(219,217,4),(1,1):(322,320,6),
 (1,2):(323,321,5),(1,3):(419,417,5),(2,0):(190,188,5),
 (2,1):(195,193,4),(2,2):(298,296,5),(2,3):(284,282,4),
 (3,0):(176,174,4),(3,1):(171,169,4),(3,2):(181,179,4),
 (3,3):(274,272,4),
}
EXPECTED_S18={
 (0,0):(393,391,7),(0,1):(506,504,8),(0,2):(611,609,8),
 (0,3):(721,719,8),(1,0):(219,217,4),(1,1):(322,320,6),
 (1,2):(324,322,5),(1,3):(419,417,5),(2,0):(190,188,5),
 (2,1):(196,194,4),(2,2):(298,296,5),(2,3):(285,283,4),
 (3,0):(177,175,4),(3,1):(172,170,4),(3,2):(182,180,4),
 (3,3):(275,273,4),
}

def test_complete_x_quotient_has_verified_finite_integer_rank_certificate():
    for (k,t),want in EXPECTED_X.items():
        r=m['certify'](k,t,'X')
        assert (r['quotient_vertices'],r['chosen_occurrence_edges'],r['maximum_rank'])==want
        assert r['terminal_orbits']==2
        assert r['actual_lifts']['all_states_hit_typed_coincidence']
        assert not r['universal_parameterized_rank']

def test_complete_18_source_quotient_has_verified_finite_rank_certificate():
    for (k,t),want in EXPECTED_S18.items():
        r=m['certify'](k,t,'S18')
        assert (r['quotient_vertices'],r['chosen_occurrence_edges'],r['maximum_rank'])==want
        assert r['terminal_orbits']==2
        assert r['actual_lifts']['all_states_hit_typed_coincidence']
        assert not r['universal_parameterized_rank']

def test_original_all_state_word_lifts_and_pinned_full_witness_manifest():
    a=m['certify'](3,0,'X'); b=m['certify'](3,0,'S18')
    assert a['manifest_sha256']=='8cd230e84bad9b4193fda3e9a00943b29dd4698e192685db7357d55173c14722'
    assert b['manifest_sha256']=='6e1dd938571c1bfe71e841fb694a30653eb565b5f327ac4588ff653dfa12973b'
    assert a['actual_lifts']['actual_indexed_lift_edges']==822
    assert b['actual_lifts']['actual_indexed_lift_edges']==826
    z=m['export'](3,0,'S18')
    assert len(z['rows'])==177 and z['max_rank']==4
    assert z['manifest_sha256']==b['manifest_sha256']

def test_missing_state_modified_child_rank_and_unproductive_cycle_refused():
    g,states,q=m['build_complete'](3,0,'X')
    rows=m['produce'](q)
    assert m['verify_rank'](q,rows)['selected_edges']==174
    with pytest.raises(m['InvalidRankCertificate']):
        m['verify_rank'](q,rows[:-1])
    idx=next(i for i,r in enumerate(rows) if r['edge'] is not None)
    corrupted=[dict(r) for r in rows]
    corrupted[idx]['rank']+=2
    with pytest.raises(m['InvalidRankCertificate']):
        m['verify_rank'](q,corrupted)
    corrupted=[dict(r) for r in rows]
    corrupted[idx]['edge']=[100000,0,corrupted[idx]['edge'][2]]
    with pytest.raises(m['InvalidRankCertificate']):
        m['verify_rank'](q,corrupted)
    X=m['qmod']['X'];rev=m['qmod']['reverse'](X);C=(2,2,0,0,0)
    qbad=m['qmod']['quotient']([X,rev,C],{X:0,rev:1,C:2},
                                 [[(0,0,0)],[(1,0,0)],[]])
    with pytest.raises(m['UnproductiveQuotient']):
        m['produce'](qbad)

def test_capped_graph_and_invalid_parameters_fail_closed():
    with pytest.raises(m['qmod']['IncompleteGraph']):
        m['build_complete'](3,0,cap=10)
    with pytest.raises(ValueError):
        m['certify'](-1,0)
    with pytest.raises(ValueError):
        m['certify'](3,0,'unsupported')

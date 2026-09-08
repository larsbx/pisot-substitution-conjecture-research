from psc_research import boundary_sync_hits, build_bpa, endpoint_maps, recurrent_noncoincident_sccs, scc_is_productive, sync_pairs

TRIBONACCI = {1: (1, 2), 2: (1, 3), 3: (1,)}
FLIPPED_TRIBONACCI = {1: (2, 1), 2: (3, 1), 3: (1,)}
SMITH = {1: (2,), 2: (1, 3), 3: (1, 3, 1, 2)}


def is_globally_synchronizing(endpoint_map):
    size = len(endpoint_map)
    return len(sync_pairs(endpoint_map)) == size * size


def test_tribonacci_prefix_map_is_synchronizing():
    plus, minus = endpoint_maps(TRIBONACCI)
    assert is_globally_synchronizing(plus)
    assert not is_globally_synchronizing(minus)


def test_flipped_tribonacci_suffix_map_is_synchronizing():
    plus, minus = endpoint_maps(FLIPPED_TRIBONACCI)
    assert not is_globally_synchronizing(plus)
    assert is_globally_synchronizing(minus)


def test_smith_not_globally_endpoint_synchronizing_but_bsl_catches():
    plus, minus = endpoint_maps(SMITH)
    assert not is_globally_synchronizing(plus)
    assert not is_globally_synchronizing(minus)

    graph = build_bpa(SMITH, max_states=2000)
    comps = recurrent_noncoincident_sccs(graph)
    assert comps
    for comp in comps:
        assert scc_is_productive(SMITH, comp, max_iterate=1)
        assert boundary_sync_hits(SMITH, comp, max_iterate=1)


def test_core_examples_bsl_catches_all_recurrent_noncoincident_sccs():
    for sigma in [TRIBONACCI, FLIPPED_TRIBONACCI, SMITH]:
        graph = build_bpa(sigma, max_states=2000)
        for comp in recurrent_noncoincident_sccs(graph):
            assert boundary_sync_hits(sigma, comp, max_iterate=1)

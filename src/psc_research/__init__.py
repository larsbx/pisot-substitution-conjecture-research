"""Reusable tooling for PSC balanced-pair experiments."""

from .bpa import (
    BoundaryHit,
    State,
    Substitution,
    apply_substitution,
    apply_substitution_n,
    boundary_sync_hits,
    build_bpa,
    coincidence_boundaries,
    decompose_pair,
    endpoint_maps,
    normalize_state,
    parikh,
    recurrent_noncoincident_sccs,
    scc_is_productive,
    sync_pairs,
)

__all__ = [
    "BoundaryHit",
    "State",
    "Substitution",
    "apply_substitution",
    "apply_substitution_n",
    "boundary_sync_hits",
    "build_bpa",
    "coincidence_boundaries",
    "decompose_pair",
    "endpoint_maps",
    "normalize_state",
    "parikh",
    "recurrent_noncoincident_sccs",
    "scc_is_productive",
    "sync_pairs",
]

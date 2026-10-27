"""Show exact all-parameter spectral chamber and typed-word proofs."""
from psc.class_a_boundary_signs import certify_all_chambers
from psc.class_a_boundary_occurrences import certify_all_typed_occurrences
from psc.class_a_boundary_run_pairs import certify_run_pair_chambers


def main() raises:
    certify_all_chambers()
    certify_all_typed_occurrences()
    certify_run_pair_chambers()

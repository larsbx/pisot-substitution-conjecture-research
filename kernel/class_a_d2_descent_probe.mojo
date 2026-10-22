"""Finite class-A d2 exact descent evidence, not a universal hitting claim."""
from psc.class_a_d2_descent_probe import (
    finite_d2_descent_replay,uniform_centered_slice_replay,
    certify_d2_uniform_center_paths,replay_d2_center_paths,
)


def main() raises:
    uniform_centered_slice_replay()
    _=certify_d2_uniform_center_paths()
    replay_d2_center_paths(8)
    finite_d2_descent_replay()

"""Replay the exact shared-parameter negative control, without CycleSum promotion."""
from psc.class_d_minus_shared_cycles import verify_documented_negative_control, verify_negative_cycle


def main() raises:
    verify_documented_negative_control()
    verify_negative_cycle()
    print("CLASS_D_MINUS_SHARED_CYCLE_CONTROLS_OK CycleSum=separate_seed_cover")

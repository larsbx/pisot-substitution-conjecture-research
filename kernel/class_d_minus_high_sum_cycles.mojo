"""Replay the unbounded formal-cycle negative control, without a seed claim."""
from psc.class_d_minus_high_sum_cycles import verify_high_sum_ray, high_sum_seed_sample


def main() raises:
    verify_high_sum_ray()
    for k in [2,3,8]:
        var report = high_sum_seed_sample(k)
        if report[1] != 0:
            raise Error("seed-reachable high-sum counterexample; replay printed above")
    print("HIGH_SUM_CONTROLS_OK specimens=3 formal_ray=unbounded CycleSum=separate_seed_cover")

"""Fixed exact grid, independent of the conditional CycleSum superset."""
from psc.class_d_minus_recurrent_support import recurrent_report


def main() raises:
    var failed = False
    for a in range(2,9):
        for b in range(1,9):
            var row = recurrent_report(a,b)
            failed = failed or row[6] != 0 or row[7] > 1
    if failed:
        raise Error("unexplained recurrent labels or finite CycleSum counterexamples; see replay records")
    print("CLASS_D_MINUS_RECURRENT_FINITE_CALIBRATION_OK specimens=56 uniform_theorem=false")

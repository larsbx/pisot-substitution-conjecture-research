"""The seed-patch overlap census over the total-length PIP class.

Runs the survey of `swap_overlap_census.mojo` unchanged over the 24486 PIP
substitutions on {0,1,2} whose images have total length at most
`TOTAL_LENGTH_CAP = 8` (`psc.corpus.pip_corpus_total_length`), the domain of
a lost earlier sweep (docs/lost-depth-indexed-formulation-2026-10-01.md).
The standing 4554 corpus is its max-image <= 3 slice, so the totals here
contain that census's.  A clean run is finite evidence only: it does not
reconstruct the lost sweep's criterion and does not close any level.
"""

from psc.corpus import TOTAL_LENGTH_CAP, pip_corpus_total_length
from swap_overlap_census import survey


def main() raises:
    survey(pip_corpus_total_length(TOTAL_LENGTH_CAP))

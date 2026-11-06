"""Exact packed-row field bounds and occurrence order, including duplicates."""
from std.testing import assert_equal
from mojo_smoke.claims import require_contract
from c4_overlap_lean_export import lean_row, pack_row
from finite_exact.exact_decimal import bigz_decimal


def main() raises:
    assert_equal(lean_row(List[Int]()),"[]")
    assert_equal(lean_row([1,1,2,0]),"[1,1,2,0,]")
    # Independent decimal calibrations for the documented radix layout.
    assert_equal(bigz_decimal(pack_row([0,1,0,0,0],1,[])),"18156239804432385")
    assert_equal(bigz_decimal(pack_row([0,1,0,0,0],1,[1,1,2,0])),"19343403463829462328541185")
    var refused = 0
    try:
        _ = pack_row([0,1,0,0,0],0,[])
    except:
        refused += 1
    try:
        _ = pack_row([0,1,0,0,0],1,[16384])
    except:
        refused += 1
    try:
        _ = pack_row([0,1,41,0,0],1,[])
    except:
        refused += 1
    assert_equal(refused,3)
    require_contract("Lean overlap exporter preserves packed fields, occurrence order and parallel multiplicity; refuses out-of-budget fields rather than truncating")

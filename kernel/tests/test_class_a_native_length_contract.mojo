"""Exact native class-A normalization, sublattice and literal-child checks."""
from std.testing import assert_equal, assert_true
from mojo_smoke.claims import require_contract
from psc.overlap_seed_patch import (
    build_seed_overlap_tables_screened, SeedOverlapTables,
)
from psc.perron_field3 import CubicElt, cubic_mul
from psc.class_a_parikh_field_bridge import class_a_lengths
from psc.class_a_native_length_contract import (
    expected_native_lengths, native_scale, verify_native_length_normalization,
    native_parikh_shift, decode_native_parikh_shift, verify_native_indexed_child,
)

def sigma_minus(n: Int,d: Int) -> List[List[Int]]:
    var A=n+d
    var x=List[Int]([0])
    for _ in range(A): x.append(2)
    x.append(0)
    var c=List[Int]([1])
    for _ in range(n): c.append(2)
    c.append(0)
    var y=List[Int]([0])
    for _ in range(n-1): y.append(2)
    y.append(1)
    var sigma=List[List[Int]]()
    sigma.append(x^)
    sigma.append(c^)
    sigma.append(y^)
    return sigma^

def refuses_bad_native_scale(tables: SeedOverlapTables,n: Int,d: Int) -> Bool:
    try:
        _=verify_native_length_normalization(tables,n,d)
        return False
    except:
        return True

def refuses_bad_index(tables: SeedOverlapTables,n: Int,d: Int,i: Int,j: Int) -> Bool:
    try:
        _=verify_native_indexed_child(tables,n,d,0,0,1,0,-1,i,j)
        return False
    except:
        return True

def main() raises:
    var checked=0
    for k in range(5):
        for t in range(4):
            var n=k+t+3
            var d=k+2*t+5
            var tables=build_seed_overlap_tables_screened(sigma_minus(n,d))
            var factor=verify_native_length_normalization(tables,n,d)
            var expected=expected_native_lengths(n,d)
            var canon=class_a_lengths(d)
            assert_equal(factor,native_scale(n,d))
            for i in range(3):
                assert_equal(tables.lengths.at(i),expected.at(i))
                assert_equal(cubic_mul(tables.field,factor,canon.at(i)),expected.at(i))
            for p in range(-2,3):
                for q in range(-2,3):
                    for r in range(-2,3):
                        var shift=native_parikh_shift(n,d,p,q,r)
                        var decoded=decode_native_parikh_shift(n,d,shift)
                        assert_equal(decoded[0],p)
                        assert_equal(decoded[1],q)
                        assert_equal(decoded[2],r)
                        assert_equal(shift.is_zero(),p==0 and q==0 and r==0)
                        checked+=1
            # X(d+1,0)->Q and Q(1,2)->typed C: real occurrences.
            var first=verify_native_indexed_child(
                tables,n,d,0,0,1,0,-1,d+1,0)
            assert_equal(first,List[Int]([2,0,0,-1,1]))
            var last=verify_native_indexed_child(
                tables,n,d,2,0,0,-1,1,1,2)
            assert_equal(last,List[Int]([2,2,0,0,0]))
            # Missing literal occurrences and a geometrically nonstrict
            # selected child must be refused by the real native adapter.
            assert_true(refuses_bad_index(tables,n,d,-1,0))
            assert_true(refuses_bad_index(tables,n,d,len(tables.sigma[0]),0))
            assert_true(refuses_bad_index(tables,n,d,0,len(tables.sigma[0])))
            assert_true(refuses_bad_index(tables,n,d,0,0))
            # Y0(n,k+2) reaches CY; the index is a real c-image RUN.
            var child=verify_native_indexed_child(
                tables,n,d,2,2,1,-1,-1,n,k+2)
            assert_equal(child,List[Int]([1,2,0,-2,2]))
            # A genuine E6 child source from the old research stack.
            var e6=verify_native_indexed_child(
                tables,n,d,0,0,0,1,0,n+2,0)
            assert_equal(e6,List[Int]([2,0,0,1,-1]))
            var bad=False
            try:
                _=decode_native_parikh_shift(n,d,CubicElt(1,0,0))
            except:
                bad=True
            assert_true(bad)
            bad=False
            try:
                _=decode_native_parikh_shift(n,d,CubicElt(0,d,0))
            except:
                bad=True
            assert_true(bad)
            # Native positive cofactor lengths and beta(beta-1)
            # normalized research lengths are DIFFERENT; reject a caller
            # who supplies the wrong scale under real native tables.
            var mismatched=SeedOverlapTables(
                tables.sigma,tables.field,class_a_lengths(d),
                tables.prefix_starts,tables.prefix_positions)
            assert_true(refuses_bad_native_scale(mismatched,n,d))
            # Non-class-A literal ordering must be refused even when the
            # field and length vectors remain algebraically valid.
            var wrong_sigma=tables.sigma.copy()
            wrong_sigma[0][0]=2
            var corrupted=SeedOverlapTables(
                wrong_sigma,tables.field,tables.lengths,
                tables.prefix_starts,tables.prefix_positions)
            assert_true(refuses_bad_native_scale(corrupted,n,d))
    assert_equal(checked,5*4*5*5*5)
    print('CLASS_A_NATIVE_LENGTH_CONTRACT_PASS',checked)
    require_contract("minus class-A regression specimens: actual native cofactor scale, Parikh lattice inverse with both divisibility guards, selected literal strict-overlap children and wrong-scale/order refusal")

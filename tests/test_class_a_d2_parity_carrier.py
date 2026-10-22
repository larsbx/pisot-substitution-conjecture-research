"""Independent exact Q(beta) evidence for d2 parity, with corrupt-row refusal."""
from pathlib import Path
import importlib.util
import pytest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location(
    "d2_parity", ROOT/"oracles/python/class_a_d2_parity_carrier.py")
oracle=importlib.util.module_from_spec(spec)
spec.loader.exec_module(oracle)


@pytest.mark.parametrize("n,states,intervals,maxhit",[
    (4,183,87,4),(5,193,85,5),(6,225,91,5),
    (7,231,87,5),(8,265,93,5),(9,271,87,6),
])
def test_exact_complete_graph(n,states,intervals,maxhit):
    p=oracle.reference_profile(n)
    assert p["states"]==states and len(p["intervals"])==intervals
    assert p["max_hit"]==maxhit
    assert p["seeds"]==9


def test_even_odd_affine_candidates_are_distinct():
    def fit(a,b):
        first=oracle.reference_profile(a)["intervals"]
        last=oracle.reference_profile(b)["intervals"]
        assert len(first)==len(last)
        out=[]
        for left,right in zip(first,last):
            assert left[:4]==right[:4]
            dl,du=right[4]-left[4],right[5]-left[5]
            assert dl%2==0 and du%2==0
            sl,su=dl//2,du//2
            out.append((*left[:4],sl,left[4]-sl*(a//2),su,left[5]-su*(a//2)))
        return out
    even,odd=fit(8,12),fit(9,13)
    assert len(even)==93 and len(odd)==87
    # These are finite comparisons at independent held-out parameters.
    for n,template in [(10,even),(11,odd)]:
        predicted=[]
        for t,b,s,y,al,bl,au,bu in template:
            predicted.append((t,b,s,y,al*(n//2)+bl,au*(n//2)+bu))
        assert predicted==oracle.reference_profile(n)["intervals"]
    # False cross-parity reuse must be rejected.
    assert even!=odd


def test_export_parser_rejects_missing_or_mutated_rows(tmp_path):
    profile=oracle.reference_profile(8)
    lines=[f'D2_FINITE_SUMMARY 8 states {profile["states"]} intervals {len(profile["intervals"])} max_first_hit {profile["max_hit"]} all_states_hitting=true universal=false']
    lines += ['D2_INTERVAL 8 '+' '.join(map(str,row)) for row in profile["intervals"]]
    path=tmp_path/"profile.log"
    path.write_text("\n".join(lines)+"\n")
    assert oracle.calibrate(path)["ordered_typed_intervals_equal"]
    path.write_text("\n".join(lines[:-1])+"\n")
    with pytest.raises(ValueError):
        oracle.calibrate(path)
    damaged=lines.copy()
    fields=damaged[-1].split()
    fields[-1]=str(int(fields[-1])+1)
    damaged[-1]=" ".join(fields)
    path.write_text("\n".join(damaged)+"\n")
    with pytest.raises(ValueError):
        oracle.calibrate(path)

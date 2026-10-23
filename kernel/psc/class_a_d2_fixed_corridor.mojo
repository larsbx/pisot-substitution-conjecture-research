"""Uniform four-step hitting corridor for 80 explicit Class-A d=2 states.

All states have integral offset sum s=k+c+y=0. Hence under incidence M_n
the term n*s vanishes *identically*, not just on the observed finite graph.
Chosen proper-prefix indices are <=4 and thus valid for every n>=4 in
all three substitution images. Every row is independently checked as a
strict physical overlap for all 0<h<1/5 with exact positive-coefficient
quadratic certificates. Each chosen child matches the named row exactly
and its integer depth strictly drops. Eight rows have offset zero.

The corridor was *discovered* from a complete n=8 graph. Its proof
does NOT assume discovery completeness, seed reachability for all n,
all-child closure of this subset, or productivity of the whole carrier.
"""
from psc.class_a_d2_fixed_corridor_data import corridor_rows
from psc.class_a_d2_parity_carrier import inferred_template


def _positive_quadratic(poly: List[Int]) raises:
    """25*(1+t)^2*f(t/(5*(1+t))) coefficients nonnegative and not all zero.

    The d2 plus positive root h satisfies 0<h<1/5 for every n>=4:
    P_2(0)=1, P_2(1/5)=(88-30n)/125<0, P_2 strictly decreasing.
    """
    if len(poly)!=3:
        raise Error("d2 fixed corridor requires a quadratic overlap margin")
    var a=poly[0]
    var b=poly[1]
    var c=poly[2]
    var coefficients=List[Int]([25*a,50*a+5*b,25*a+5*b+c])
    var positive=False
    for coeff in coefficients:
        if coeff<0:
            raise Error("d2 fixed corridor strict Perron sign unproved")
        if coeff>0:
            positive=True
    if not positive:
        raise Error("d2 fixed corridor boundary touching is not strict")


def _length(letter: Int) raises -> List[Int]:
    if letter==0:
        return [1,2,2]
    if letter==1:
        return [1,0,0]
    if letter==2:
        return [1,1,0]
    raise Error("invalid d2 corridor letter")


def _strict_all_n(row: List[Int]) raises:
    if len(row)!=9:
        raise Error("invalid d2 corridor table width")
    var t=row[0]
    var b=row[1]
    var k=row[2]
    var c=row[3]
    var y=row[4]
    if k+c+y!=0:
        raise Error("d2 fixed corridor cannot cancel the n*s term")
    var shift=List[Int]([0,2*k+y,2*k])
    var lt=_length(t)
    var lb=_length(b)
    var left=List[Int]()
    var right=List[Int]()
    for i in range(3):
        left.append(lb[i]+shift[i])
        right.append(lt[i]-shift[i])
    _positive_quadratic(left)
    _positive_quadratic(right)


def _prefix(letter: Int, index: Int) raises -> List[Int]:
    if letter<0 or letter>2 or index<0 or index>4:
        raise Error("d2 fixed corridor index must be a uniformly legal prefix 0..4")
    if index==0:
        return [0,0,0]
    return [0 if letter==1 else 1,1 if letter==1 else 0,index-1]


def _child_letter(letter: Int, index: Int) raises -> Int:
    _=_prefix(letter,index)
    if index==0:
        return 1 if letter==1 else 0
    return 2


def _child_label(row: List[Int]) raises -> List[Int]:
    if len(row)!=9 or row[5]<=0:
        raise Error("cannot inflate a zero-rank corridor target")
    var s=row[2]+row[3]+row[4]
    if s!=0:
        raise Error("chosen uniform child retains unwanted n dependence")
    var a=_prefix(row[0],row[6])
    var b=_prefix(row[1],row[7])
    return [
        _child_letter(row[0],row[6]),
        _child_letter(row[1],row[7]),
        row[2]+s+b[0]-a[0],
        s-row[2]+b[1]-a[1],
        2*row[2]+row[4]+b[2]-a[2],
    ]


def certify_corridor_rows(rows: List[List[Int]]) raises -> List[Int]:
    """All-n physical reality and exact chosen descending occurrences."""
    if len(rows)!=80:
        raise Error("d2 uniform fixed corridor must have exactly 80 rows")
    var histogram=List[Int]([0,0,0,0,0])
    var selected=0
    for i in range(len(rows)):
        var row=rows[i].copy()
        if len(row)!=9 or row[5]<0 or row[5]>4:
            raise Error("malformed d2 corridor row or rank")
        for earlier_i in range(i):
            var previous=rows[earlier_i].copy()
            var equal=True
            for q in range(5):
                if previous[q]!=row[q]:
                    equal=False
            if equal:
                raise Error("duplicate d2 fixed corridor label")
        _strict_all_n(row)
        histogram[row[5]]+=1
        if row[5]==0:
            if row[2]!=0 or row[3]!=0 or row[4]!=0 or row[6]!=-1 or (
                row[7]!=-1 or row[8]!=-1):
                raise Error("d2 zero-rank target must have exactly zero offset")
            continue
        if row[8]<0 or row[8]>=len(rows):
            raise Error("chosen d2 fixed corridor child index absent")
        var child=rows[row[8]].copy()
        if child[5]!=row[5]-1:
            raise Error("d2 chosen actual child does not decrease rank")
        var expected=_child_label(row)
        for j in range(5):
            if expected[j]!=child[j]:
                raise Error("d2 chosen child differs from exact integral prefix update")
        selected+=1
    if histogram!=List[Int]([8,20,26,22,4]) or selected!=72:
        raise Error("d2 uniform fixed corridor rank census changed")
    print("CLASS_A_D2_FIXED_CORRIDOR", "states",80,"targets",8,
          "actual_decreasing_edges",72,"maximum_hitting_steps",4,
          "strict_margins",160,"all_n_ge_4=true",
          "whole_d2_carrier_hitting=not_proved")
    return [80,8,72,4,160]


def _contains_at_all_m(
    parity_rows: List[List[Int]], m0: Int, target: List[Int],
) raises -> Bool:
    var s=target[2]+target[3]+target[4]
    for row in parity_rows:
        if len(row)!=8:
            raise Error("malformed imported d2 parity candidate")
        if row[0]!=target[0] or row[1]!=target[1] or (
            row[2]!=s or row[3]!=target[4]):
            continue
        if row[4]<=0 and row[6]>=0 and (
            m0*row[4]+row[5]<=target[2] and
            target[2]<=m0*row[6]+row[7]
        ):
            return True
    return False


def certify_uniform_candidate_inclusion(rows: List[List[Int]]) raises -> List[Int]:
    """Extra all-n inclusion relative to the proven parity *candidate* rows.

    Even n>=8 has m>=4, odd n>=7 has m>=3. Intervals monotone-expand
    around every fixed corridor label; no graph-size or reachability claim.
    """
    if len(rows)!=80:
        raise Error("d2 uniform inclusion requires all fixed corridor labels")
    var even=inferred_template(8,12)
    var odd=inferred_template(9,13)
    for i in range(len(rows)):
        var state=rows[i].copy()
        if not _contains_at_all_m(even.copy(),4,state.copy()):
            raise Error("fixed corridor label omitted on an even parameter ray")
        if not _contains_at_all_m(odd.copy(),3,state.copy()):
            raise Error("fixed corridor label omitted on an odd parameter ray")
    print("CLASS_A_D2_FIXED_CORRIDOR_IN_CANDIDATES", "all_80=true",
          "even_n>=8", "odd_n>=7","reachability_not_proved=true")
    return [80,80]


def certify_uniform_fixed_corridor() raises -> List[Int]:
    var rows=corridor_rows()
    var shape=certify_corridor_rows(rows)
    _=certify_uniform_candidate_inclusion(rows)
    return shape

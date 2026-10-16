"""Exact finite arithmetic certificate for every minus b=0 member with a>=2.

See the boundary progress note section 4i. Input proposals are verified, never
accepted by sample agreement. All variables here are bounded certificate data,
NOT the unbounded parameter a. With <=1000 rows and offsets/index coefficients
bounded by 100, every intermediate integer has absolute value below 10^8;
thus native Int arithmetic is exact. No floating-point root approximation.
"""
from std.collections import Dict
from psc.class_d_minus_spine_data import minus_spine_rows


def _key(top: Int, bottom: Int, x: Int, c: Int, y: Int) -> String:
    return String(top) + ":" + String(bottom) + ":" + String(x) + "," + String(c) + "," + String(y)


def _length(letter: Int) -> List[Int]:
    # 2(1+t)*ell_letter, coefficients of 1,t,t^2, t=1/beta in (0,1/10).
    if letter == 0:
        return [3,-2,-4]
    if letter == 1:
        return [3,0,-2]
    return [2,2,0]


def _positive(c: Int, b: Int, a: Int) -> Bool:
    # 100 times the three Bernstein coefficients on [0,1/10].
    var b0 = 100*c
    var b1 = 100*c+5*b
    var b2 = 100*c+10*b+a
    return min(b0,min(b1,b2)) >= 0 and max(b0,max(b1,b2)) > 0


def _nonpositive(c: Int, b: Int, a: Int) -> Bool:
    return max(100*c,max(100*c+5*b,100*c+10*b+a)) <= 0


def _interior(top: Int, bottom: Int, x: Int, c: Int, y: Int) -> Bool:
    var lt = _length(top)
    var lb = _length(bottom)
    var z0 = 3*x+3*c+2*y
    var z1 = -2*x+2*y
    var z2 = -4*x-2*c
    return _positive(z0+lb[0],z1+lb[1],z2+lb[2]) and _positive(lt[0]-z0,lt[1]-z1,lt[2]-z2)


def _impossible(top: Int, bottom: Int, x: Int, c: Int, y: Int) -> Bool:
    # A failed positivity test is not a proof of impossibility.
    var lt = _length(top)
    var lb = _length(bottom)
    var z0 = 3*x+3*c+2*y
    var z1 = -2*x+2*y
    var z2 = -4*x-2*c
    return _nonpositive(z0+lb[0],z1+lb[1],z2+lb[2]) or _nonpositive(lt[0]-z0,lt[1]-z1,lt[2]-z2)


def _affine_nonnegative(m: Int, b: Int) -> Bool:
    return m >= 0 and 2*m+b >= 0


def _run(letter: Int) -> List[Int]:
    if letter == 0:
        return [3,5]
    if letter == 1:
        return [3,6]
    return [2,4]


def _prefix(letter: Int, m: Int, b: Int) raises -> List[Int]:
    # child letter, slope of y-prefix, constant x,c,y-prefix coordinates.
    var run = _run(letter)
    var start = 0 if letter == 0 else 1
    var end = 0 if letter == 1 else 1
    if m == 0 and b == 0:
        return [start,0,0,0,0]
    var px = 1 if start == 0 else 0
    var pc = 1 if start == 1 else 0
    if m == run[0] and b == run[1]+1:
        return [end,run[0],px,pc,run[1]]
    if not _affine_nonnegative(m,b-1) or not _affine_nonnegative(run[0]-m,run[1]-b):
        raise Error("occurrence leaves its run for some a>=2")
    return [2,m,px,pc,b-1]


def _segment(letter: Int, kind: Int) -> List[Int]:
    # child letter; prefix x,c; y-prefix lower slope/constant, upper slope/constant.
    var run = _run(letter)
    var start = 0 if letter == 0 else 1
    var end = 0 if letter == 1 else 1
    var px = 1 if start == 0 else 0
    var pc = 1 if start == 1 else 0
    if kind == 0:
        return [start,0,0,0,0,0,0]
    if kind == 1:
        return [2,px,pc,0,0,run[0],run[1]-1]
    return [end,px,pc,run[0],run[1],run[0],run[1]]


def verify_minus_spine(rows: List[List[Int]]) raises -> List[Int]:
    if len(rows) == 0 or len(rows) > 1000:
        raise Error("empty cover or table budget exceeded")
    var cover = Dict[String, Int]()
    for i in range(len(rows)):
        ref r = rows[i]
        if len(r) != 11:
            raise Error("row must have eleven fields")
        if r[0] < 0 or r[0] >= 3 or r[1] < 0 or r[1] >= 3 or r[5] < 0 or r[5] > 1000:
            raise Error("invalid letters or rank")
        for j in [2,3,4,7,8,9,10]:
            if r[j] < -100 or r[j] > 100:
                raise Error("coefficient exceeds exact native-integer budget")
        var key = _key(r[0],r[1],r[2],r[3],r[4])
        if key in cover:
            raise Error("duplicate label")
        cover[key] = i
        if not _interior(r[0],r[1],r[2],r[3],r[4]):
            raise Error("interior inequality unproved")
    var seeds = 0
    for a in range(3):
        for b in range(a+1,3):
            var ea = List[Int]([0,0,0])
            var eb = List[Int]([0,0,0])
            ea[a] = 1
            eb[b] = 1
            var candidates = List[List[Int]]()
            candidates.append([a,b,0,0,0])
            candidates.append([a,a,eb[0],eb[1],eb[2]])
            candidates.append([b,b,-ea[0],-ea[1],-ea[2]])
            candidates.append([b,a,eb[0]-ea[0],eb[1]-ea[1],eb[2]-ea[2]])
            for v in candidates:
                if _impossible(v[0],v[1],v[2],v[3],v[4]):
                    continue
                if _key(v[0],v[1],v[2],v[3],v[4]) not in cover:
                    raise Error("seed escapes cover")
                seeds += 1
    var candidates = 0
    for row in rows:
        var top = row[0]
        var bottom = row[1]
        var x = row[2]
        var c = row[3]
        var y = row[4]
        if top == bottom and x == 0 and c == 0 and y == 0:
            continue  # coincidence is terminal in the exact seed graph
        var m0 = x+c
        var m1 = x+c+2*y
        var z_slope = 3*x+3*c+2*y
        var z_const = 5*x+6*c+4*y
        for kt in range(3):
            var st = _segment(top,kt)
            for kb in range(3):
                var sb = _segment(bottom,kb)
                var u = m0+sb[1]-st[1]
                var v = m1+sb[2]-st[2]
                var lo_m = z_slope+sb[3]-st[5]
                var lo_b = z_const+sb[4]-st[6]
                var hi_m = z_slope+sb[5]-st[3]
                var hi_b = z_const+sb[6]-st[4]
                var bound = 3*(abs(u)+abs(v)+1)//2+1
                for z in range(-bound,bound+1):
                    candidates += 1
                    if _affine_nonnegative(lo_m,lo_b-z-1) or _affine_nonnegative(-hi_m,z-hi_b-1):
                        continue
                    if _impossible(st[0],sb[0],u,v,z):
                        continue
                    if _key(st[0],sb[0],u,v,z) not in cover:
                        raise Error("child escapes cover")
    var targets = 0
    var maximum = 0
    for row in rows:
        var rank = row[5]
        var nxt = row[6]
        maximum = max(maximum,rank)
        if row[2] == 0 and row[3] == 0 and row[4] == 0:
            if rank != 0 or nxt != -1 or row[7] != 0 or row[8] != 0 or row[9] != 0 or row[10] != 0:
                raise Error("invalid offset-zero target row")
            targets += 1
            continue
        if rank == 0 or nxt < 0 or nxt >= len(rows):
            raise Error("missing descent row")
        if rows[nxt][5] >= rank:
            raise Error("non-strict rank descent")
        var pt = _prefix(row[0],row[7],row[8])
        var pb = _prefix(row[1],row[9],row[10])
        ref child = rows[nxt]
        if pt[0] != child[0] or pb[0] != child[1]:
            raise Error("wrong occurrence letters")
        var x = row[2]
        var c = row[3]
        var y = row[4]
        if 3*x+3*c+2*y+pb[1]-pt[1] != 0:
            raise Error("affine offset slope does not vanish")
        if x+c+pb[2]-pt[2] != child[2] or x+c+2*y+pb[3]-pt[3] != child[3] or 5*x+6*c+4*y+pb[4]-pt[4] != child[4]:
            raise Error("wrong affine child offset")
    return [len(rows),targets,seeds,candidates,maximum]


def certify_minus_tail() raises -> List[Int]:
    return verify_minus_spine(minus_spine_rows())

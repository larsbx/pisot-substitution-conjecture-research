"""Exact physical hub-completion area on balanced two-track words.

Uses positive INTEGER duration weights for executable replay, with no
floating approximation to the Perron vector. The algebraic area identity
works for EVERY positive weight row, and can therefore later be applied
to the exact Perron row in a written theorem.

A negative hub-completion interval is a physical crossing, NOT a
one-step synchronizing newborn. No directed-path or PSC claim is made.
"""
from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.words import Pair, parikh, k2


struct HubPhysicalProfile(Copyable, Movable):
    var area: Int
    var negative_length: Int
    var positive_length: Int
    var negative_intervals: Int
    var total_length: Int
    var noncrossing: Bool

    def __init__(out self, area: Int, neg: Int, pos: Int,
                 intervals: Int, total: Int):
        self.area=area
        self.negative_length=neg
        self.positive_length=pos
        self.negative_intervals=intervals
        self.total_length=total
        self.noncrossing=neg==0


def weighted_hub_profile(pair: Pair, hub: Int,
                         weights: List[Int]) raises -> HubPhysicalProfile:
    """Exact merged endpoint sweep; all equal-time events are simultaneous."""
    if len(weights)!=3 or hub<0 or hub>=3:
        raise Error("three positive letter widths and valid hub required")
    for weight in weights:
        if weight<=0:
            raise Error("nonpositive tile width")
    var n=pair.length()
    if n<2 or n>4096 or len(pair.u)!=len(pair.v):
        raise Error("nonempty equal-length balanced words required")
    if pair.u[0]!=hub or pair.v[0]==hub:
        raise Error("hub must occur initially on top only")
    for i in range(n):
        if pair.u[i]<0 or pair.u[i]>=3 or pair.v[i]<0 or pair.v[i]>=3:
            raise Error("word contains invalid ternary letter")
    if parikh(pair.u)!=parikh(pair.v):
        raise Error("input pair is not Parikh balanced")
    var i=0
    var j=0
    var time=0
    var top_end=weights[pair.u[0]]
    var bottom_end=weights[pair.v[0]]
    var H=0
    var area=0
    var neg=0
    var pos=0
    var intervals=0
    var top_done=False
    var bottom_done=False
    while i<n or j<n:
        var next_end=0
        if i==n:
            next_end=bottom_end
        elif j==n:
            next_end=top_end
        else:
            next_end=min(top_end,bottom_end)
        var dt=checked_sub(next_end,time)
        if dt<=0:
            raise Error("endpoint order lost strict positive physical widths")
        area=checked_add(area,checked_mul(H,dt))
        if H<0:
            neg=checked_add(neg,dt)
            intervals=checked_add(intervals,1)
        elif H>0:
            pos=checked_add(pos,dt)
        time=next_end
        if i<n and top_end==time:
            if pair.u[i]==hub:
                H=checked_add(H,1)
            i+=1
            if i<n:
                top_end=checked_add(top_end,weights[pair.u[i]])
            else:
                top_done=True
        if j<n and bottom_end==time:
            if pair.v[j]==hub:
                H=checked_sub(H,1)
            j+=1
            if j<n:
                bottom_end=checked_add(bottom_end,weights[pair.v[j]])
            else:
                bottom_done=True
    if H!=0 or not top_done or not bottom_done or top_end!=bottom_end:
        raise Error("unbalanced final hub counts or physical lengths")
    var counts=k2(pair)
    var wedge_area=0
    for letter in range(3):
        wedge_area=checked_add(wedge_area,
                    checked_mul(weights[letter],counts[3*hub+letter]))
    if wedge_area!=area:
        raise Error("physical completion area disagrees with degree-two scattered defect")
    # A non-crossing hub-oriented word starts with one hub on top and
    # a nonhub below. No bottom hub can finish before its first nonhub
    # plus one full hub width. Top has already finished its first hub.
    if neg==0 and area<weights[pair.v[0]]:
        raise Error("positive initial hub plateau missing")
    return HubPhysicalProfile(area,neg,pos,intervals,time)

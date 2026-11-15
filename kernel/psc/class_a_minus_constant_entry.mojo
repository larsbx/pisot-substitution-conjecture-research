"""Actual central RUN paths in minus Class A, d>=5 and n>=d+1.

The exact nearest-integer recurrence has constant periodic tails U_H, not
zero-only tails. Three original RUN occurrences lower a positive height by
one; swapping the two indices gives the negative-height path. The separate
written density proof supplies entrance from arbitrary strict sources.

Every returned path stops at its first full integral zero. All its letters
are y, so that endpoint is also a typed coincidence. Caps, arithmetic
overflow and inconsistent bindings refuse without a mathematical verdict.
"""

from finite_exact.checked_int import checked_add, checked_sub, checked_mul
from psc.class_a_boundary_children import (
    BoundaryLabel, BoundaryEdge, _prefix, _letter, geometric_state,
)
from psc.class_a_central_entry import is_central, _zero, _abs_checked
from psc.class_a_native_length_contract import check_literal_minus_class_a_words
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import (
    SeedOverlapTables, interior_overlap, selected_overlap_child,
)
from psc.perron_field3 import (
    CubicElt, cubic_add_checked, cubic_sub_checked, cubic_scale_checked,
    cubic_mul_beta, sign_at_perron,
)


def _parameters(n: Int, d: Int) raises:
    if d < 5 or n < checked_add(d, 1):
        raise Error("constant-entry chamber requires d>=5 and n>=d+1")
    _ = checked_add(checked_add(n, d), 2)


def _bind(tables: SeedOverlapTables, n: Int, d: Int) raises:
    """Bind the full ordered words, cubic, positive scale and prefix cache.

    The old upper-chamber binder is deliberately not weakened or called.
    This new chamber has n+1<beta<n+2 and admits arbitrary n>=d+1.
    """
    _parameters(n, d)
    check_literal_minus_class_a_words(tables, n, d)
    if (tables.field.chi0 != 2 or
        tables.field.chi1 != checked_sub(checked_sub(n, d), 1) or
        tables.field.chi2 != checked_sub(0, checked_add(n, 2))):
        raise Error("constant-entry field does not match the literal family")
    if (sign_at_perron(tables.field,
            CubicElt(checked_sub(0, checked_add(n, 1)), 1, 0)) <= 0 or
        sign_at_perron(tables.field,
            CubicElt(checked_sub(0, checked_add(n, 2)), 1, 0)) >= 0):
        raise Error("constant-entry field has the wrong Perron-root chamber")
    if len(tables.prefix_starts) != 4:
        raise Error("constant-entry prefix cache has the wrong parent count")
    var total = 0
    for a in range(3):
        total = checked_add(total, len(tables.sigma[a]))
    if len(tables.prefix_positions) != total:
        raise Error("constant-entry prefix cache has the wrong occurrence count")
    var start = 0
    for a in range(3):
        if sign_at_perron(tables.field, tables.lengths.at(a)) <= 0:
            raise Error("constant-entry tile length is not positive")
        if tables.prefix_starts[a] != start:
            raise Error("constant-entry prefix cache has a shifted parent start")
        var cursor = CubicElt()
        for i in range(len(tables.sigma[a])):
            if tables.prefix_positions[checked_add(start, i)] != cursor:
                raise Error("constant-entry prefix cache differs from the actual word")
            cursor = cubic_add_checked(cursor, tables.lengths.at(tables.sigma[a][i]))
        if cursor != cubic_mul_beta(tables.field, tables.lengths.at(a)):
            raise Error("constant-entry words and lengths fail exact inflation scaling")
        start = checked_add(start, len(tables.sigma[a]))
    if tables.prefix_starts[3] != start:
        raise Error("constant-entry prefix cache has the wrong final endpoint")


def member_transport(n: Int, d: Int, parent: BoundaryLabel,
                     i: Int, j: Int) raises -> BoundaryLabel:
    """Actual literal ordinals and full checked Parikh transport.

    This algebraic function accepts disjoint children too; geometric edge
    acceptance is a separate check below. It preserves all three offsets.
    """
    _parameters(n, d)
    var top = _prefix(-1, n, d, parent.top, i)
    var bottom = _prefix(-1, n, d, parent.bottom, j)
    var x = checked_add(checked_add(checked_mul(2, parent.x), parent.c), parent.y)
    var c = checked_add(parent.c, parent.y)
    var y = checked_add(
        checked_add(checked_mul(checked_add(n, d), parent.x),
                    checked_mul(n, parent.c)),
        checked_mul(checked_sub(n, 1), parent.y))
    return BoundaryLabel(_letter(-1, n, d, parent.top, i),
        _letter(-1, n, d, parent.bottom, j),
        checked_add(x, checked_sub(bottom[0], top[0])),
        checked_add(c, checked_sub(bottom[1], top[1])),
        checked_add(y, checked_sub(bottom[2], top[2])))


def _verify_bound_edge(tables: SeedOverlapTables, n: Int, d: Int,
                       parent: BoundaryLabel, i: Int, j: Int,
                       target: BoundaryLabel) raises:
    """Check one edge after the caller has bound these exact tables."""
    if member_transport(n, d, parent, i, j) != target:
        raise Error("constant-entry child changed its type or integral offset")
    var source = geometric_state(tables, parent)
    if not interior_overlap(tables, source):
        raise Error("constant-entry parent is not a strict overlap")
    var actual = selected_overlap_child(tables, source, i, j)
    if actual != geometric_state(tables, target):
        raise Error("constant-entry Parikh and actual-prefix transports disagree")
    if not interior_overlap(tables, actual):
        raise Error("constant-entry literal child is not a strict overlap")


def verify_member_edge(tables: SeedOverlapTables, n: Int, d: Int,
                       parent: BoundaryLabel, i: Int, j: Int,
                       target: BoundaryLabel) raises:
    _bind(tables, n, d)
    _verify_bound_edge(tables, n, d, parent, i, j, target)


def _nearest_bound(tables: SeedOverlapTables, n: Int, d: Int,
                   source: BoundaryLabel) raises -> BoundaryEdge:
    if not is_central(tables, source):
        raise Error("constant-entry nearest RUN requires a central y/y source")
    var twice = cubic_scale_checked(cubic_mul_beta(
        tables.field, geometric_state(tables, source).shift), 2)
    var radius = checked_sub(n, 2)
    var low = checked_sub(0, radius)
    var high = radius
    # Least integer gap g satisfying 2 beta u <= (2g+1) L_y.
    # The exact irreducible cubic excludes actual half-integer ties.
    while low < high:
        var middle = checked_add(low, checked_sub(high, low) // 2)
        var odd = checked_add(checked_mul(2, middle), 1)
        if sign_at_perron(tables.field, cubic_sub_checked(twice,
                cubic_scale_checked(tables.lengths.l2, odd))) <= 0:
            high = middle
        else:
            low = checked_add(middle, 1)
    var gap = low
    var i = checked_add(1, max(gap, 0))
    var j = checked_add(1, max(checked_sub(0, gap), 0))
    if i < 1 or i > checked_sub(n, 1) or j < 1 or j > checked_sub(n, 1):
        raise Error("constant-entry nearest choice is not an actual RUN pair")
    var child = member_transport(n, d, source, i, j)
    if not is_central(tables, child):
        raise Error("constant-entry nearest choice left its exact central interval")
    _verify_bound_edge(tables, n, d, source, i, j, child)
    return BoundaryEdge(i, j, child)


def nearest_run_child(tables: SeedOverlapTables, n: Int, d: Int,
                      source: BoundaryLabel) raises -> BoundaryEdge:
    _bind(tables, n, d)
    return _nearest_bound(tables, n, d, source)


def _append(tables: SeedOverlapTables, n: Int, d: Int,
            mut path: List[BoundaryEdge], mut source: BoundaryLabel,
            i: Int, j: Int, expected: BoundaryLabel, step_cap: Int) raises:
    if _zero(source):
        raise Error("constant-entry path must stop at its first integral zero")
    if len(path) >= step_cap:
        raise Error("constant-entry step cap exhausted: no verdict")
    if i < 1 or i > checked_sub(n, 1) or j < 1 or j > checked_sub(n, 1):
        raise Error("constant-height descent selected a non-RUN ordinal")
    var child = member_transport(n, d, source, i, j)
    if child != expected:
        raise Error("constant-height descent lost a full intermediate Parikh coordinate")
    _verify_bound_edge(tables, n, d, source, i, j, child)
    path.append(BoundaryEdge(i, j, child))
    source = child


def _cycle_bound(tables: SeedOverlapTables, n: Int, d: Int, height: Int,
                 flip: Bool, step_cap: Int) raises -> List[BoundaryEdge]:
    if height <= 0 or step_cap < 0:
        raise Error("constant-height exit requires positive height and nonnegative cap")
    var total_steps = checked_mul(3, height)
    if total_steps > step_cap:
        raise Error("constant-height exit step cap exhausted: no verdict")
    if checked_mul(checked_mul(2, d), height) > n:
        raise Error("constant-height source is outside 2dH<=n")
    var source = BoundaryLabel(2, 2, height, checked_sub(0, height), 0)
    if flip:
        source = reversed_label(source)
    if not is_central(tables, source):
        raise Error("constant-height source is outside the exact central interval")
    var path = List[BoundaryEdge]()
    var H = height
    while H > 0:
        var dH = checked_mul(d, H)
        var lower = checked_sub(H, 1)
        var last_gap = checked_sub(checked_mul(d, lower), 2)
        var addresses: List[List[Int]] = [
            [checked_add(dH, 2), 1],
            [1, checked_sub(checked_add(n, 2), dH)],
            [checked_add(1, max(last_gap, 0)),
             checked_add(1, max(checked_sub(0, last_gap), 0))],
        ]
        var expected: List[BoundaryLabel] = [
            BoundaryLabel(2, 2, H, checked_sub(0, H), -1),
            BoundaryLabel(2, 2, lower, checked_sub(checked_sub(0, H), 1), 2),
            BoundaryLabel(2, 2, lower, checked_sub(0, lower), 0),
        ]
        for index in range(3):
            var i = addresses[index][0]
            var j = addresses[index][1]
            var target = expected[index]
            if flip:
                var original_i = i
                i = j
                j = original_i
                target = reversed_label(target)
            _append(tables, n, d, path, source, i, j, target, step_cap)
        if not is_central(tables, source):
            raise Error("constant-height macrostep did not return to the central interval")
        H = lower
    if not _zero(source) or source.top != source.bottom or len(path) != total_steps:
        raise Error("constant-height descent did not finish at its typed integral zero")
    return path^


def cycle_escape(tables: SeedOverlapTables, n: Int, d: Int, height: Int,
                 flip: Bool = False, step_cap: Int = 10000) raises -> List[BoundaryEdge]:
    """Exactly 3H actual RUN edges from +/- U_H to typed integral zero."""
    _bind(tables, n, d)
    return _cycle_bound(tables, n, d, height, flip, step_cap)


def central_escape(tables: SeedOverlapTables, n: Int, d: Int,
                   source: BoundaryLabel, step_cap: Int = 10000) raises -> List[BoundaryEdge]:
    """Follow the positive-coefficient recurrence, then its constant exit.

    The checked integer-pair guard implements a conservative finite bound.
    Neither that guard nor the caller cap can turn a partial transcript into
    a positive result. The written theorem proves eventual constant entry.
    """
    _bind(tables, n, d)
    if step_cap < 0 or not is_central(tables, source):
        raise Error("constant-entry escape requires a central y/y source and nonnegative cap")
    var path = List[BoundaryEdge]()
    if _zero(source):
        return path^
    var next_x = checked_add(checked_add(checked_mul(2, source.x), source.c), source.y)
    var numerator = checked_add(n, 1)
    var denominator = checked_mul(2, d)
    var ceiling = checked_add(numerator // denominator,
                              1 if numerator % denominator != 0 else 0)
    var C = max(max(_abs_checked(source.x), _abs_checked(next_x)), ceiling)
    var width = checked_add(checked_mul(2, C), 1)
    var pair_budget = checked_add(checked_mul(width, width), 2)
    var w = source
    for _ in range(pair_budget):
        if _zero(w):
            return path^
        var following_x = checked_add(checked_add(checked_mul(2, w.x), w.c), w.y)
        if _abs_checked(w.x) > C or _abs_checked(following_x) > C:
            raise Error("constant-entry recurrence violated its checked integer-pair bound")
        if w.c == checked_sub(0, w.x) and w.y == 0:
            var tail = _cycle_bound(tables, n, d, _abs_checked(w.x),
                                    w.x < 0, checked_sub(step_cap, len(path)))
            for edge in tail:
                path.append(edge)
            return path^
        if len(path) >= step_cap:
            raise Error("constant-entry recurrence step cap exhausted: no verdict")
        var edge = _nearest_bound(tables, n, d, w)
        if edge.target.c != checked_sub(edge.target.x, checked_mul(2, w.x)):
            raise Error("constant-entry recurrence lost full-state reconstruction")
        path.append(edge)
        w = edge.target
    raise Error("constant-entry integer-pair guard exhausted: no verdict")

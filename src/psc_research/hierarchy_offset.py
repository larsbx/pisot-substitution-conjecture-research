"""Relative position of asynchronous cut ancestry in the derived BPA hierarchy.

A multi-level zero-return ancestry becomes asynchronous below its top level: at
source depth k the top and bottom prefix cuts can lie at different physical
positions in ``sigma^k(T)``.  PR #32 gives that pair a common zero-return block
partition, namely the letters of ``tau_C^k(T)``.  This module locates both
asynchronous cuts in that common derived partition.

Absolute block indices grow with k and are intentionally discarded.  Their
difference is finite-state: every derived block has positive integral length,
so

    |block_index_top - block_index_bottom| <= |top_cut-bottom_cut|
                                               = |sum(source_difference)|.

PR #30 makes the ancestry defect range finite in the PIP strict regime.  Block
labels, Z/2 occurrence orientations, in-block offsets, finite derived contexts,
and the outgoing correction digit are finite as well.  Thus a fixed-radius
relative hierarchy-offset state is finite-state independently of ancestry depth.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from .bpa import State, Substitution, alphabet_size, apply_substitution_n
from .birth_event import oriented_derived_word
from .derived_factorization import DerivedSubstitution, strict_derived_substitution
from .prefix_ancestry import AncestryPath, AncestryStep
from .prefix_difference import Vector, asynchronous_prefix_difference


OrientedSymbol = tuple[State, int]
ContextSymbol = OrientedSymbol | None


@dataclass(frozen=True)
class DerivedBlockPosition:
    """Right-continuous address of one physical cut in an oriented derived word."""

    block_index: int
    offset: int
    state: State | None
    orientation: int | None

    @property
    def terminal(self) -> bool:
        return self.state is None


@dataclass(frozen=True)
class RelativeHierarchyOffset:
    """Depth-free finite state for one asynchronous ancestry transition."""

    source_difference: Vector
    correction: Vector
    cut_delta: int
    block_index_delta: int
    top_offset: int
    bottom_offset: int
    top_state: State | None
    bottom_state: State | None
    top_orientation: int | None
    bottom_orientation: int | None
    top_left_context: tuple[ContextSymbol, ...]
    top_right_context: tuple[ContextSymbol, ...]
    bottom_left_context: tuple[ContextSymbol, ...]
    bottom_right_context: tuple[ContextSymbol, ...]

    @property
    def aligned_physical_cut(self) -> bool:
        return self.cut_delta == 0

    @property
    def same_derived_block_address(self) -> bool:
        return self.block_index_delta == 0 and self.top_offset == self.bottom_offset


@dataclass(frozen=True)
class LevelledHierarchyOffset:
    source_depth: int
    state: RelativeHierarchyOffset


def _block_length(symbol: OrientedSymbol) -> int:
    state, orientation = symbol
    if orientation not in (-1, 1):
        raise ValueError("derived occurrence orientation must be +/-1")
    u, v = state
    if len(u) != len(v):
        raise ValueError("derived state sides must have equal length")
    if not u:
        raise ValueError("derived blocks must be nonempty")
    return len(u)


def oriented_block_boundaries(word: Sequence[OrientedSymbol]) -> tuple[int, ...]:
    cuts = [0]
    for symbol in word:
        cuts.append(cuts[-1] + _block_length(symbol))
    return tuple(cuts)


def locate_cut_in_oriented_derived_word(
    word: Sequence[OrientedSymbol],
    cut: int,
) -> DerivedBlockPosition:
    """Locate a physical cut; an exact internal boundary belongs to the right block."""
    boundaries = oriented_block_boundaries(word)
    total = boundaries[-1]
    if cut < 0 or cut > total:
        raise ValueError("cut lies outside derived word")
    if cut == total:
        return DerivedBlockPosition(len(word), 0, None, None)

    # The words in this project are finite and the state count is modest; the
    # linear scan keeps the boundary convention explicit and dependency-free.
    index = 0
    while index + 1 < len(boundaries) and boundaries[index + 1] <= cut:
        index += 1
    state, orientation = word[index]
    offset = cut - boundaries[index]
    if offset < 0 or offset >= _block_length(word[index]):
        raise AssertionError("derived block locator produced a noncanonical offset")
    return DerivedBlockPosition(index, offset, state, orientation)


def oriented_derived_context(
    word: Sequence[OrientedSymbol],
    block_index: int,
    radius: int,
) -> tuple[tuple[ContextSymbol, ...], tuple[ContextSymbol, ...]]:
    """Fixed-radius context around a right-continuous derived block address."""
    if radius < 0:
        raise ValueError("derived context radius must be nonnegative")
    if block_index < 0 or block_index > len(word):
        raise ValueError("derived block index lies outside word")
    left_raw = tuple(word[max(0, block_index - radius) : block_index])
    right_raw = tuple(word[block_index : min(len(word), block_index + radius)])
    left = (None,) * (radius - len(left_raw)) + left_raw
    right = right_raw + (None,) * (radius - len(right_raw))
    return left, right


def relative_hierarchy_offset(
    sigma: Substitution,
    comp: Sequence[State],
    parent: State,
    source_depth: int,
    top_cut: int,
    bottom_cut: int,
    *,
    correction: Sequence[int],
    radius: int,
    parent_orientation: int = 1,
    tau: DerivedSubstitution | None = None,
) -> RelativeHierarchyOffset:
    """Construct the finite relative state of two source cuts at one depth."""
    if source_depth < 0:
        raise ValueError("source_depth must be nonnegative")
    if radius < 0:
        raise ValueError("radius must be nonnegative")
    if parent_orientation not in (-1, 1):
        raise ValueError("parent orientation must be +/-1")
    if tau is None:
        tau = strict_derived_substitution(sigma, comp)

    top_word = apply_substitution_n(sigma, parent[0], source_depth)
    bottom_word = apply_substitution_n(sigma, parent[1], source_depth)
    if top_cut < 0 or top_cut > len(top_word) or bottom_cut < 0 or bottom_cut > len(bottom_word):
        raise ValueError("asynchronous source cut lies outside an iterated side")

    size = alphabet_size(sigma)
    defect = asynchronous_prefix_difference(top_word, bottom_word, top_cut, bottom_cut, size)
    cut_delta = top_cut - bottom_cut
    if cut_delta != sum(defect):
        raise AssertionError("cut displacement does not equal total Parikh defect")

    derived_word = oriented_derived_word(
        sigma,
        tau,
        parent,
        source_depth,
        parent_orientation=parent_orientation,
    )
    boundaries = oriented_block_boundaries(derived_word)
    if boundaries[-1] != len(top_word) or boundaries[-1] != len(bottom_word):
        raise AssertionError("derived word lengths do not reconstruct the physical iterates")

    top_pos = locate_cut_in_oriented_derived_word(derived_word, top_cut)
    bottom_pos = locate_cut_in_oriented_derived_word(derived_word, bottom_cut)
    block_delta = top_pos.block_index - bottom_pos.block_index
    if abs(block_delta) > abs(cut_delta):
        raise AssertionError("derived block-index displacement exceeds physical cut displacement")

    top_left, top_right = oriented_derived_context(derived_word, top_pos.block_index, radius)
    bottom_left, bottom_right = oriented_derived_context(derived_word, bottom_pos.block_index, radius)
    corr = tuple(correction)
    if len(corr) != size:
        raise ValueError("correction vector dimension does not match the substitution alphabet")

    return RelativeHierarchyOffset(
        source_difference=defect,
        correction=corr,
        cut_delta=cut_delta,
        block_index_delta=block_delta,
        top_offset=top_pos.offset,
        bottom_offset=bottom_pos.offset,
        top_state=top_pos.state,
        bottom_state=bottom_pos.state,
        top_orientation=top_pos.orientation,
        bottom_orientation=bottom_pos.orientation,
        top_left_context=top_left,
        top_right_context=top_right,
        bottom_left_context=bottom_left,
        bottom_right_context=bottom_right,
    )


def ancestry_hierarchy_offsets(
    sigma: Substitution,
    comp: Sequence[State],
    parent: State,
    path: AncestryPath,
    *,
    radius: int,
    parent_orientation: int = 1,
) -> tuple[LevelledHierarchyOffset, ...]:
    """Decorate every source level of an ancestry path by its relative derived address."""
    if path.depth != len(path.steps):
        raise ValueError("ancestry path depth does not match step count")
    tau = strict_derived_substitution(sigma, comp)
    out: list[LevelledHierarchyOffset] = []
    for step in path.steps:
        source_depth = step.level - 1
        state = relative_hierarchy_offset(
            sigma,
            comp,
            parent,
            source_depth,
            step.top_source_cut,
            step.bottom_source_cut,
            correction=step.correction,
            radius=radius,
            parent_orientation=parent_orientation,
            tau=tau,
        )
        if state.source_difference != step.source_difference:
            raise AssertionError("hierarchy-offset defect disagrees with ancestry step")
        out.append(LevelledHierarchyOffset(source_depth, state))
    return tuple(out)


def repeated_hierarchy_offset_levels(
    states: Sequence[LevelledHierarchyOffset],
) -> tuple[tuple[int, int], ...]:
    """Pairs of source depths carrying exactly the same finite relative state."""
    seen: dict[RelativeHierarchyOffset, list[int]] = {}
    repeats: list[tuple[int, int]] = []
    for item in states:
        prior = seen.setdefault(item.state, [])
        repeats.extend((old, item.source_depth) for old in prior)
        prior.append(item.source_depth)
    return tuple(repeats)


def hierarchy_offset_space_upper_bound(
    *,
    defect_count: int,
    correction_count: int,
    max_abs_cut_delta: int,
    component_size: int,
    max_block_length: int,
    radius: int,
) -> int:
    """Coarse finite bound for the relative hierarchy-offset alphabet."""
    values = (
        defect_count,
        correction_count,
        max_abs_cut_delta,
        component_size,
        max_block_length,
        radius,
    )
    if any(value < 0 for value in values):
        raise ValueError("state-space parameters must be nonnegative")
    if defect_count == 0 or correction_count == 0:
        return 0
    if component_size == 0 or max_block_length == 0:
        raise ValueError("nonempty state spaces require component states and positive block length")

    oriented_symbol_count = 2 * component_size + 1  # +1 exterior sentinel
    return (
        defect_count
        * correction_count
        * (2 * max_abs_cut_delta + 1)
        * max_block_length**2
        * oriented_symbol_count**2
        * oriented_symbol_count ** (4 * radius)
    )

"""The shared skeleton of the class-A minus-chamber boundary children modules.

A module `class_a_boundary_<L>_children` certifies, for each source label
`L_source(kind)` of the chamber eps=-1 member with parameters (n, d), the
complete indexed star of actual interior overlaps (i, j) admitted by its exact
guard `L_child_allowed`, each transported by `member_transport` into its
exact typed image `in_L_image`. What a module proves -- its tables, guards,
counts, paths and `certify_L_children` -- stays in the module. The three loops
every module repeated are stated once here, over a `BoundaryFamily`:

  * `append_child`: orient (i, j), refuse an occurrence the guard rejects,
    transport it, refuse a target outside the image, record the edge;
  * `verify_child_packet`: guard and image hold, then `verify_member_edge`
    replays the full Parikh transport against the seed tables;
  * `verify_child_star`: exactly `count` packets, each verified, no
    occurrence (i, j) twice.

Fail closed: every refusal raises. The duplicate check keys (i, j) by
i*(max j + 1) + j, injective on the star by construction.
"""
from finite_exact.checked_int import checked_add, checked_mul
from std.collections import Dict
from psc.class_a_boundary_children import BoundaryLabel, BoundaryEdge, member_transport, verify_member_edge
from psc.class_a_boundary_next_run import _parameters
from psc.overlap_seed_patch import SeedOverlapTables


trait BoundaryFamily(ImplicitlyCopyable):
    def name(self) -> String:
        """The label named in refusals."""
        ...

    def source(self, kind: Int) raises -> BoundaryLabel:
        """The source label of `kind`; raises for an unknown kind."""
        ...

    def parameters(self, kind: Int, k: Int, t: Int) raises -> Tuple[Int, Int]:
        """The member (n, d), after the module's own bound checks."""
        ...

    def swapped(self, kind: Int) -> Bool:
        """Whether a synthesized (i, j) of `kind` is recorded as (j, i)."""
        ...

    def allowed(self, kind: Int, k: Int, t: Int, i: Int, j: Int) raises -> Bool:
        """The module's exact occurrence guard."""
        ...

    def in_image(self, w: BoundaryLabel) raises -> Bool:
        """The module's exact typed image."""
        ...


def boundary_dimensions(k: Int, t: Int, slack: Int) raises -> Tuple[Int, Int, Int, Int]:
    """(n, d, A=n+d, n-1) of the eps=-1 member, refusing unless A+slack fits."""
    var p=_parameters(-1,k,t)
    var A=checked_add(p[0],p[1])
    _=checked_add(A,slack)
    return (p[0],p[1],A,p[0]-1)


def append_child[F: BoundaryFamily](family: F, mut out: List[BoundaryEdge], kind: Int, k: Int, t: Int, i: Int, j: Int) raises:
    var p=family.parameters(kind,k,t)
    var swap=family.swapped(kind)
    var a=j if swap else i
    var b=i if swap else j
    if not family.allowed(kind,k,t,a,b):raise Error(String("synthesized ",family.name()," guard failed"))
    var target=member_transport(-1,k,p[0],p[1],family.source(kind),a,b)
    if not family.in_image(target):raise Error(String(family.name()," target escaped image"))
    out.append(BoundaryEdge(a,b,target))


def verify_child_packet[F: BoundaryFamily](family: F, tables: SeedOverlapTables, kind: Int, k: Int, t: Int, edge: BoundaryEdge) raises:
    var p=family.parameters(kind,k,t)
    if not family.allowed(kind,k,t,edge.i,edge.j) or not family.in_image(edge.target):
        raise Error(String(family.name()," packet refused"))
    verify_member_edge(tables,-1,k,p[0],p[1],family.source(kind),edge.i,edge.j,edge.target)


def verify_child_star[F: BoundaryFamily](family: F, tables: SeedOverlapTables, kind: Int, k: Int, t: Int, edges: List[BoundaryEdge], count: Int) raises:
    _=family.source(kind)
    if len(edges)!=count:raise Error(String("incomplete ",family.name()," star"))
    for edge in edges:verify_child_packet(family,tables,kind,k,t,edge)
    if duplicate_occurrence(edges):raise Error(String("duplicate ",family.name()," occurrence"))


def duplicate_occurrence(edges: List[BoundaryEdge]) raises -> Bool:
    """Whether some occurrence (i, j) appears twice; keys i*(max j + 1) + j are injective."""
    var stride=1
    for edge in edges:
        if edge.i<0 or edge.j<0:raise Error("negative boundary occurrence")
        stride=max(stride,checked_add(edge.j,1))
    var seen=Dict[Int,Bool]()
    for edge in edges:
        var key=checked_add(checked_mul(edge.i,stride),edge.j)
        if key in seen:return True
        seen[key]=True
    return False


def extend_edges(mut out: List[BoundaryEdge], suffix: List[BoundaryEdge]):
    for edge in suffix:out.append(edge)

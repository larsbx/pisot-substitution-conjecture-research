"""Exact exploratory audit of endpoint-only gauges against BPA orientation edges.

The edge signing is the raw two-track child orientation relative to normalized
balanced-pair states. It is *not* permutation parity of a word and is not an
intrinsic invariant of the substitution. Both source and destination endpoint
profiles deliberately discard internal Parikh-return addresses.

This is a diagnostic for the proposed Branch-B Endpoint Injection Exclusion,
NOT a theorem. Complete graphs only; capped enumerations are inconclusive.
"""

from finite_graph.signing import SignedEdge, perron_phase, compatibility_potential
from psc.bpa import apply_substitution, build, decompose, normalise, recurrent_noncoincident_sccs
from psc.carrier import profile_component
from psc.endpoint_core import prefix_endpoint_map, suffix_endpoint_map
from psc.words import Pair
from substitution_dynamics.automaton import Automaton


comptime BRANCH_A = 0
comptime BRANCH_B = 1
comptime BRANCH_C = 2


def injective(h: List[Int]) -> Bool:
    for i in range(len(h)):
        for j in range(i + 1, len(h)):
            if h[i] == h[j]:
                return False
    return True


def profile_key(s: Pair, size: Int) raises -> Int:
    """Ordered external head/tail letters; at most size^4 keys."""
    if len(s.u) == 0 or len(s.v) == 0:
        raise Error("empty balanced-pair state")
    return (
        ((s.u[0] * size + s.v[0]) * size + s.u[len(s.u) - 1]) * size
        + s.v[len(s.v) - 1]
    )


def endpoint_diagonal(
    s: Pair, prefix: List[Int], suffix: List[Int]
) raises -> Bool:
    if len(s.u) == 0 or len(s.v) == 0:
        raise Error("empty balanced-pair state")
    return (
        prefix[s.u[0]] == prefix[s.v[0]]
        or suffix[s.u[len(s.u) - 1]] == suffix[s.v[len(s.v) - 1]]
    )


struct SignedComponent(Copyable, Movable):
    var branch: Int
    var states: Int
    var occurrences: Int
    var has_endpoint_diagonal: Bool
    var direct_producer: Bool
    var endpoint_gauge: Bool
    var conflicting_profile_edges: Bool
    var has_duplicate_profiles: Bool

    def __init__(
        out self, branch: Int, states: Int, occurrences: Int,
        has_endpoint_diagonal: Bool, direct_producer: Bool,
        endpoint_gauge: Bool, conflicting_profile_edges: Bool,
        has_duplicate_profiles: Bool
    ):
        self.branch = branch
        self.states = states
        self.occurrences = occurrences
        self.has_endpoint_diagonal = has_endpoint_diagonal
        self.direct_producer = direct_producer
        self.endpoint_gauge = endpoint_gauge
        self.conflicting_profile_edges = conflicting_profile_edges
        self.has_duplicate_profiles = has_duplicate_profiles


def audit_closed_component(
    sigma: List[List[Int]], graph: Automaton, comp: List[Int]
) raises -> SignedComponent:
    """Exact occurrence edges, with the orientation convention of DerivedSystem.

    Only a *noncoincident-exit-free* SCC is considered here. Coincidence
    children are retained as a productivity flag, not fed to the sign graph.
    """
    var shape = profile_component(graph, comp)
    if not shape.is_sink():
        raise Error("signed component audit requires a noncoincident-closed SCC")
    var n = len(comp)
    var index = Dict[String, Int]()
    var profiles = List[Int]()
    var prefix = prefix_endpoint_map(sigma)
    var suffix = suffix_endpoint_map(sigma)
    var diagonal = False
    var duplicate_profiles = False
    var seen_profiles = Dict[Int, Bool]()
    for i in range(n):
        ref s = graph.states[comp[i]]
        index[s.key()] = i
        var profile = profile_key(s, len(sigma))
        if profile in seen_profiles:
            duplicate_profiles = True
        else:
            seen_profiles[profile] = True
        profiles.append(profile)
        if endpoint_diagonal(s, prefix, suffix):
            diagonal = True

    var edges = List[SignedEdge]()
    var pair_sign = Dict[Int, Int]()
    var profile_sign = Dict[Int, Int]()
    var cancellation = False
    var profile_conflict = False
    for i in range(n):
        ref parent = graph.states[comp[i]]
        var u = apply_substitution(sigma, parent.u)
        var v = apply_substitution(sigma, parent.v)
        var raw_children = decompose(u, v)
        for j in range(len(raw_children)):
            var raw = raw_children[j].copy()
            var canonical = normalise(raw)
            if canonical.is_coincidence():
                continue
            var key = canonical.key()
            if key not in index:
                raise Error("noncoincident child escaped a declared closed SCC")
            var dst = index[key]
            var bit = 0 if raw == canonical else 1
            edges.append(SignedEdge(i, dst, bit))

            # A: opposite signs on the same *ordered* state-to-state edge.
            var ek = i * n + dst
            if ek in pair_sign and pair_sign[ek] != bit:
                cancellation = True
            else:
                pair_sign[ek] = bit

            # A more drastic obstruction to factoring b(e) through *only*
            # parent/child external endpoints, even before vertex gauge.
            var radix = len(sigma) * len(sigma) * len(sigma) * len(sigma)
            var pk = profiles[i] * radix + profiles[dst]
            if pk in profile_sign and profile_sign[pk] != bit:
                profile_conflict = True
            else:
                profile_sign[pk] = bit

    if len(edges) == 0:
        raise Error("recurrent component has no internal child edges")

    var branch = BRANCH_A
    var gauge = False
    if not cancellation:
        var phase = perron_phase(n, edges)
        if phase == -1:
            branch = BRANCH_C
        else:
            branch = BRANCH_B
            var potential = compatibility_potential(n, edges, phase)
            if len(potential) != n:
                raise Error("compatible signing returned no full potential")
            # Since this SCC is strongly connected, this potential is unique
            # up to a global constant for a fixed phase. Thus this test of
            # constancy on external-endpoint-profile fibers is well-defined.
            gauge = True
            var values = Dict[Int, Int]()
            for i in range(n):
                var pk = profiles[i]
                if pk in values:
                    if values[pk] != potential[i]:
                        gauge = False
                else:
                    values[pk] = potential[i]

    return SignedComponent(
        branch, n, len(edges), diagonal, shape.direct_coincidence,
        gauge, profile_conflict, duplicate_profiles
    )


struct SpikeTotals(Copyable, Movable):
    var visited: Int
    var capped: Int
    var biinjective_specimens: Int
    var closed: Int
    var branch_a: Int
    var branch_b: Int
    var branch_c: Int
    var biinjective_closed: Int
    var biinjective_a: Int
    var biinjective_b: Int
    var biinjective_c: Int
    var b_endpoint_diagonal: Int
    var b_no_endpoint_diagonal: Int
    var b_endpoint_gauge: Int
    var b_no_endpoint_gauge: Int
    var b_duplicate_profiles: Int
    var b_duplicate_profiles_endpoint_gauge: Int
    var b_max_size: Int
    var a_profile_conflict: Int
    var c_profile_conflict: Int

    def __init__(out self):
        self.visited = 0
        self.capped = 0
        self.biinjective_specimens = 0
        self.closed = 0
        self.branch_a = 0
        self.branch_b = 0
        self.branch_c = 0
        self.biinjective_closed = 0
        self.biinjective_a = 0
        self.biinjective_b = 0
        self.biinjective_c = 0
        self.b_endpoint_diagonal = 0
        self.b_no_endpoint_diagonal = 0
        self.b_endpoint_gauge = 0
        self.b_no_endpoint_gauge = 0
        self.b_duplicate_profiles = 0
        self.b_duplicate_profiles_endpoint_gauge = 0
        self.b_max_size = 0
        self.a_profile_conflict = 0
        self.c_profile_conflict = 0

    def print_summary(self):
        print(
            "ENDPOINT_SIGN_SPIKE_RESULT visited=", self.visited,
            " capped=", self.capped,
            " biinjective_specimens=", self.biinjective_specimens,
            " closed=", self.closed,
            " branch_A=", self.branch_a,
            " branch_B=", self.branch_b,
            " branch_C=", self.branch_c,
            " biinjective_closed=", self.biinjective_closed,
            " biinjective_A=", self.biinjective_a,
            " biinjective_B=", self.biinjective_b,
            " biinjective_C=", self.biinjective_c,
            " B_endpoint_diagonal=", self.b_endpoint_diagonal,
            " B_no_endpoint_diagonal=", self.b_no_endpoint_diagonal,
            " B_endpoint_gauge=", self.b_endpoint_gauge,
            " B_no_endpoint_gauge=", self.b_no_endpoint_gauge,
            " B_duplicate_profiles=", self.b_duplicate_profiles,
            " B_duplicate_profiles_endpoint_gauge=", self.b_duplicate_profiles_endpoint_gauge,
            " B_max_size=", self.b_max_size,
            " A_profile_conflict=", self.a_profile_conflict,
            " C_profile_conflict=", self.c_profile_conflict,
        )


def audit_specimen(
    sigma: List[List[Int]], state_cap: Int, label: String,
    mut totals: SpikeTotals, show_witnesses: Bool = True
) raises:
    totals.visited += 1
    var biinjective = (
        injective(prefix_endpoint_map(sigma))
        and injective(suffix_endpoint_map(sigma))
    )
    if biinjective:
        totals.biinjective_specimens += 1
    var a = build(sigma, state_cap)
    if a.capped:
        totals.capped += 1
        if show_witnesses:
            print("ENDPOINT_SIGN_INCONCLUSIVE_CAPPED specimen=", label,
                  " states_at_cap=", a.size())
        return
    var comps = recurrent_noncoincident_sccs(a)
    for k in range(len(comps)):
        if not profile_component(a, comps[k]).is_sink():
            continue
        var info = audit_closed_component(sigma, a, comps[k])
        totals.closed += 1
        if biinjective:
            totals.biinjective_closed += 1
        if info.branch == BRANCH_A:
            totals.branch_a += 1
            if biinjective:
                totals.biinjective_a += 1
            if info.conflicting_profile_edges:
                totals.a_profile_conflict += 1
        elif info.branch == BRANCH_C:
            totals.branch_c += 1
            if biinjective:
                totals.biinjective_c += 1
            if info.conflicting_profile_edges:
                totals.c_profile_conflict += 1
        else:
            totals.branch_b += 1
            if info.states > totals.b_max_size:
                totals.b_max_size = info.states
            if info.has_duplicate_profiles:
                totals.b_duplicate_profiles += 1
                if info.endpoint_gauge:
                    totals.b_duplicate_profiles_endpoint_gauge += 1
            if biinjective:
                totals.biinjective_b += 1
            if info.has_endpoint_diagonal:
                totals.b_endpoint_diagonal += 1
            else:
                totals.b_no_endpoint_diagonal += 1
            if info.endpoint_gauge:
                totals.b_endpoint_gauge += 1
            else:
                totals.b_no_endpoint_gauge += 1

        if show_witnesses and (
            (biinjective and info.branch == BRANCH_B)
            or (info.branch == BRANCH_B and not info.has_endpoint_diagonal)
            or (info.branch == BRANCH_B and not info.endpoint_gauge)
        ):
            print(
                "ENDPOINT_SIGN_WITNESS specimen=", label,
                " component=", k, " size=", info.states,
                " occurrences=", info.occurrences, " branch=", info.branch,
                " biinjective=", biinjective,
                " endpoint_diagonal=", info.has_endpoint_diagonal,
                " endpoint_gauge=", info.endpoint_gauge,
                " duplicate_profiles=", info.has_duplicate_profiles,
            )
            for z in range(len(comps[k])):
                var node = comps[k][z]
                print("ENDPOINT_SIGN_WITNESS_STATE", z, a.states[node].key())

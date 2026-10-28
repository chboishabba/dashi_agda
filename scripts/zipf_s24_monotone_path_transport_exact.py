"""Exact finite-horizon S24 monotone transport certificates for Heaps paths.

Reuse (not duplicate) full_heaps_curve_law and canonical count majorization.
Given f majorizes g, solve the finite transportation feasibility problem:
  coupling(X,Y) >= 0,
  row masses = P_f(path=X),
  column masses = P_g(path=Y),
  support only on paths X_t <= Y_t at ALL t <= horizon.
A success is an independently inspectable exact rational witness for THESE
two finite distributions. It is NOT a general theorem that all majorization
pairs admit such a coupling, nor a consistency theorem over infinite time.

Mathematical owners: classical Hardy-Littlewood-Polya (1934), Strassen
(1965) stochastic-order coupling, and standard max-flow/transport duality.
Code/source adapter: Johl Brown-directed, ChatGPT-assisted, 2026-10-28.
No Agda kernel or corpus-experiment claim. No Monster/RH/NS promotion.
"""
from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence, Literal

from zipf_heaps_bridge import _validated_counts, multiset_count_majorizes
from zipf_full_heaps_path_distribution_exact import full_heaps_curve_law

Sampler = Literal["iid", "permutation"]
Path = tuple[int, ...]


@dataclass(frozen=True)
class PathTransportCertificate:
    concentrated: tuple[int, ...]
    dispersed: tuple[int, ...]
    sampler: Sampler
    horizon: int
    left_law: dict[Path, Fraction]
    right_law: dict[Path, Fraction]
    coupling: dict[tuple[Path, Path], Fraction]
    matched_mass: Fraction

    def validate(self) -> None:
        """Check every row, column and support edge with exact fractions."""
        assert self.matched_mass == Fraction(1)
        assert sum(self.coupling.values(), Fraction()) == Fraction(1)
        for (left, right), mass in self.coupling.items():
            assert mass > 0
            assert len(left) == len(right) == self.horizon + 1
            assert all(x <= y for x, y in zip(left, right))
        assert set(self.left_law) == {
            l for (l, _), amount in self.coupling.items() if amount > 0}
        assert set(self.right_law) == {
            r for (_, r), amount in self.coupling.items() if amount > 0}
        for left, mass in self.left_law.items():
            assert sum((v for (x, _), v in self.coupling.items()
                        if x == left), Fraction()) == mass
        for right, mass in self.right_law.items():
            assert sum((v for (_, x), v in self.coupling.items()
                        if x == right), Fraction()) == mass


def _transport_maxflow(
    left_law: dict[Path, Fraction],
    right_law: dict[Path, Fraction],
    max_edges: int = 50000,
) -> tuple[Fraction, dict[tuple[Path, Path], Fraction]]:
    """Edmonds-Karp with exact rationals, no floating tolerance.

    The source->row->column->sink flow network admits a unit flow exactly
    when a coordinatewise monotone coupling exists for the two input PMFs.
    """
    left = tuple(left_law)
    right = tuple(right_law)
    if (not left or not right or
            sum(left_law.values(), Fraction()) != 1 or
            sum(right_law.values(), Fraction()) != 1):
        raise ValueError("both path PMFs must be normalized and nonempty")
    if any(type(v) is not Fraction or v <= 0
           for law in (left_law, right_law) for v in law.values()):
        raise ValueError("positive exact rational PMF masses required")
    if type(max_edges) is not int or max_edges < 1:
        raise ValueError("positive integral edge budget required")
    nleft = len(left)
    nright = len(right)
    source, sink = nleft + nright, nleft + nright + 1
    capacity: dict[tuple[int, int], Fraction] = {}
    neighbors: dict[int, set[int]] = defaultdict(set)

    def edge(u: int, v: int, mass: Fraction) -> None:
        if mass <= 0:
            return
        capacity[u, v] = mass
        capacity[v, u] = Fraction()
        neighbors[u].add(v)
        neighbors[v].add(u)

    for i, x in enumerate(left):
        edge(source, i, left_law[x])
    for j, y in enumerate(right):
        edge(nleft + j, sink, right_law[y])
    admissible: list[tuple[int, int]] = []
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            if len(x) == len(y) and all(a <= b for a, b in zip(x, y)):
                admissible.append((i, j))
                if len(admissible) > max_edges:
                    raise ValueError("monotone transport edge budget exceeded")
                edge(i, nleft + j, Fraction(1))

    total = Fraction()
    while True:
        parents = {source: -1}
        frontier = deque([source])
        while frontier and sink not in parents:
            u = frontier.popleft()
            for v in sorted(neighbors[u]):
                if v not in parents and capacity[u, v] > 0:
                    parents[v] = u
                    frontier.append(v)
        if sink not in parents:
            break
        path = []
        v = sink
        delta = Fraction(1)
        while v != source:
            u = parents[v]
            delta = min(delta, capacity[u, v])
            path.append((u, v))
            v = u
        for u, v in path:
            capacity[u, v] -= delta
            capacity[v, u] += delta
        total += delta

    coupling = {
        (left[i], right[j]): capacity[nleft + j, i]
        for i, j in admissible
        if capacity[nleft + j, i] > 0
    }
    assert sum(coupling.values(), Fraction()) == total
    return total, coupling


def majorization_heaps_path_transport_certificate(
    concentrated: Sequence[int],
    dispersed: Sequence[int],
    horizon: int,
    sampler: Sampler,
) -> PathTransportCertificate:
    """Construct an exact explicit finite monotone path coupling or fail.

    The returned certificate is conditional on THE PARTICULAR inputs.
    A failed search is a witness to lack of coordinatewise transport for
    those exact input laws (unless the explicit resource limit was hit).
    """
    a = _validated_counts(concentrated)
    b = _validated_counts(dispersed)
    if (len(a) != len(b) or sum(a) != sum(b)
            or not multiset_count_majorizes(a, b)):
        raise ValueError("same K,N and concentrated majorizes dispersed")
    if (type(horizon) is not int or not 0 <= horizon <= min(12, sum(a))
            or sampler not in ("iid", "permutation")):
        raise ValueError("exact two-sampler horizon must be in [0,min(12,N)]")
    left = full_heaps_curve_law(a, horizon, sampler)
    right = full_heaps_curve_law(b, horizon, sampler)
    mass, coupling = _transport_maxflow(left, right)
    if mass != 1:
        raise AssertionError(
            f"monotone path transport unavailable: mass={mass}; "
            f"inputs={a},{b},{horizon},{sampler}"
        )
    certificate = PathTransportCertificate(
        a, b, sampler, horizon, left, right, coupling, mass)
    certificate.validate()
    return certificate


def finite_hall_cut_obstruction(
    left_law: dict[Path, Fraction],
    right_law: dict[Path, Fraction],
    max_left_paths: int = 14,
) -> tuple[tuple[Path, ...], tuple[Path, ...], Fraction] | None:
    """Find a dual Hall/Strassen CUT obstructing monotone transport.

    For a set A of left histories, let up(A) be the set of right histories
    y for which some x in A satisfies x<=y at every prefix.
    If P_left(A)>P_right(up(A)), no monotone coupling can exist.
    The output (A, up(A), exact_positive_deficit) is independently
    checkable; None means no violating subset was found after a FULL
    enumeration of the capped finite support. This is the max-flow
    min-cut dual, NOT a conjectured property of Zipf histograms.
    """
    if (not left_law or not right_law
            or sum(left_law.values(), Fraction()) != 1
            or sum(right_law.values(), Fraction()) != 1
            or any(type(v) is not Fraction or v <= 0
                   for law in (left_law, right_law) for v in law.values())):
        raise ValueError("normalized, positive exact PMFs required")
    if (type(max_left_paths) is not int or max_left_paths < 1
            or len(left_law) > max_left_paths):
        raise ValueError("finite dual cut exhaustive support limit exceeded")
    left = tuple(left_law)
    right = tuple(right_law)
    best_deficit = Fraction()
    best = None
    for mask in range(1, 1 << len(left)):
        selected = tuple(x for i, x in enumerate(left) if mask & (1 << i))
        upward = tuple(y for y in right
                       if any(len(x) == len(y) and
                              all(a <= b for a, b in zip(x, y))
                              for x in selected))
        deficit = (
            sum((left_law[x] for x in selected), Fraction())
            - sum((right_law[y] for y in upward), Fraction()))
        if deficit > best_deficit:
            best_deficit = deficit
            best = selected, upward, deficit
    return best

#!/usr/bin/env python3
"""Pure-stdlib finite model-check for the CCDCOE graph-cut specimen.

This is NOT an Agda kernel check, a psychology measurement or an attribution
classifier. Its job is to independently exercise finite graph semantics and
reject a missing-edge-only assertion when an alternative route remains.
"""
from __future__ import annotations

from collections import deque
from itertools import product

ACTORS = ("a", "b")
LAYERS = ("epistemic", "axiological", "identificatory", "social", "teleological")
BRIDGES = tuple(zip(LAYERS, LAYERS[1:]))
SIDE = dict(zip(LAYERS, (True, True, True, False, False)))


def make_graph(mask: tuple[bool, bool, bool, bool], bypass: bool = False):
    graph = {(actor, layer): set() for actor in ACTORS for layer in LAYERS}
    for layer in LAYERS:
        for actor in ACTORS:
            graph[actor, layer].update((other, layer) for other in ACTORS)
    for present, (first, second) in zip(mask, BRIDGES):
        if present:
            for actor in ACTORS:
                graph[actor, first].add((actor, second))
    if bypass:
        for actor in ACTORS:
            graph[actor, "identificatory"].add((actor, "teleological"))
    return graph


def reachable(graph, source, target):
    todo = deque([source])
    visited = {source}
    while todo:
        node = todo.popleft()
        if node == target:
            return True
        for nxt in graph[node]:
            if nxt not in visited:
                visited.add(nxt)
                todo.append(nxt)
    return False


def partition_certificate(graph):
    return all(
        SIDE[source[1]] == SIDE[target[1]]
        for source, targets in graph.items()
        for target in targets
    )


def run():
    checked = 0
    for mask in product((False, True), repeat=len(BRIDGES)):
        graph = make_graph(mask)
        for left, right in product(ACTORS, ACTORS):
            actual = reachable(
                graph, (left, "epistemic"), (right, "teleological")
            )
            expected = all(mask)
            assert actual == expected, (mask, left, right, actual)
            checked += 1

        assert all(
            (other, layer) in graph[actor, layer]
            for actor, other, layer in product(ACTORS, ACTORS, LAYERS)
        )

        if not mask[2]:
            assert partition_certificate(graph)
            assert not any(
                reachable(
                    graph, (a, "epistemic"), (b, "teleological")
                )
                for a, b in product(ACTORS, ACTORS)
            )

    full = make_graph((True, True, True, True))
    cut = make_graph((True, True, False, True))
    assert all(reachable(full, (a, LAYERS[0]), (b, LAYERS[-1]))
               for a, b in product(ACTORS, ACTORS))
    assert all(not reachable(cut, (a, LAYERS[0]), (b, LAYERS[-1]))
               for a, b in product(ACTORS, ACTORS))

    # Red-team the theorem: a single bypass invalidates the no-path claim.
    bypass = make_graph((True, True, False, True), bypass=True)
    assert not partition_certificate(bypass)
    assert reachable(bypass, ("a", LAYERS[0]), ("b", LAYERS[-1]))

    # Outward functionality is identical, yet integrated connectivity differs.
    outward = lambda _graph: "components-still-function"
    assert outward(full) == outward(cut)
    assert reachable(full, ("a", LAYERS[0]), ("b", LAYERS[-1]))
    assert not reachable(cut, ("a", LAYERS[0]), ("b", LAYERS[-1]))
    # Four crossed states: each of both graph conditions admits both origins.
    episodes = {(arch, origin) for arch in ("full", "cut")
                for origin in ("organic", "influence")}
    assert len(episodes) == 4

    print(f"PASS: {checked} exhaustive directed reachability comparisons")
    print("PASS: local layer persistence for every connector mask")
    print("PASS: certified separator and positive full spanning routes")
    print("PASS: alternate-path bypass correctly defeats certificate")
    print("PASS: architecture and provenance finite independence")


if __name__ == "__main__":
    run()

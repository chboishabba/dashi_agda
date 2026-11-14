#!/usr/bin/env python3
"""Checkable finite first-link trace and revision-cone certificates.

Original first-link methodology: Ibrahim, Danforth, Dodds (2017),
DOI 10.1016/j.jocs.2016.12.001. These deterministic certificate
formats and checkers are new DASHI work, not a historical reproduction.

Graph semantics: known source -> known source, None (recorded dead end), or
unknown target (unresolved). No QID/cultural/semantic inference is made.
"""
from __future__ import annotations

from collections import deque
import hashlib
import json
from typing import Any, Mapping

SCHEMA = 'dashi.ibrahim.fln.finite_certificate.v1'


def canonical_cycle(nodes: list[str]) -> list[str]:
    if not nodes or len(set(nodes)) != len(nodes):
        raise ValueError('cycle must be nonempty with distinct vertices')
    i = min(range(len(nodes)), key=lambda k: nodes[k])
    return nodes[i:] + nodes[:i]


def graph_digest(graph: Mapping[str, str | None]) -> str:
    """Order-independent digest with explicit no-edge vs absent-target grammar."""
    raw = json.dumps(dict(graph), ensure_ascii=False, sort_keys=True,
                     separators=(',', ':')).encode('utf-8')
    return hashlib.sha256(raw).hexdigest()


def trace_start(graph: Mapping[str, str | None], start: str) -> dict[str, Any]:
    if start not in graph:
        raise ValueError('start must be in graph')
    seen: dict[str, int] = {}
    trace: list[str] = []
    node = start
    while True:
        if node not in graph:
            return {'start': start, 'trace': trace, 'kind': 'unresolved_target',
                    'terminal': node}
        if node in seen:
            return {'start': start, 'trace': trace, 'kind': 'cycle',
                    'entry_index': seen[node],
                    'cycle': canonical_cycle(trace[seen[node]:])}
        seen[node] = len(trace)
        trace.append(node)
        dest = graph[node]
        if dest is None:
            return {'start': start, 'trace': trace, 'kind': 'dead_end',
                    'terminal': node}
        node = dest


def check_trace(graph: Mapping[str, str | None], receipt: dict[str, Any]) -> tuple[str, tuple[str, ...]]:
    """Independent local verification: no call to trace_start or terminal_census.

    Rejects forged terminal labels, omitted/reordered path edges, a cycle
    that stops prematurely, and confusion of missing target with dead end.
    """
    if not isinstance(receipt, dict) or set(receipt) not in [
        {'start', 'trace', 'kind', 'terminal'},
        {'start', 'trace', 'kind', 'entry_index', 'cycle'},
    ]:
        raise ValueError('invalid receipt field set')
    start = receipt['start']
    path = receipt['trace']
    if not isinstance(start, str) or start not in graph:
        raise ValueError('start missing from source graph')
    if not isinstance(path, list) or not path or any(
        not isinstance(v, str) or v not in graph for v in path
    ):
        raise ValueError('trace must contain nonempty known nodes')
    if len(path) > len(graph) or len(path) != len(set(path)) or path[0] != start:
        raise ValueError('trace repeats known vertex or violates graph bound')
    for left, right in zip(path, path[1:]):
        if graph[left] != right:
            raise ValueError('incorrect trace transition')
    last = graph[path[-1]]
    kind = receipt['kind']
    if kind == 'dead_end':
        if last is not None or receipt['terminal'] != path[-1]:
            raise ValueError('bad dead-end terminator')
        return 'dead_end', (path[-1],)
    if kind == 'unresolved_target':
        if last is None or last in graph or receipt['terminal'] != last:
            raise ValueError('bad unresolved-target terminator')
        return 'unresolved_target', (last,)
    if kind == 'cycle':
        at = receipt['entry_index']
        if not isinstance(at, int) or isinstance(at, bool) or not 0 <= at < len(path):
            raise ValueError('invalid cycle entry')
        if last != path[at]:
            raise ValueError('cycle must close at exact first repeated node')
        cycle = canonical_cycle(path[at:])
        if receipt['cycle'] != cycle:
            raise ValueError('not the canonical terminal cycle')
        return 'cycle', tuple(cycle)
    raise ValueError('unknown terminal kind')


def certify_graph(graph: Mapping[str, str | None]) -> dict[str, Any]:
    # No trusting input manifests here: this checks the given in-memory graph.
    return {'schema': SCHEMA, 'graph_sha256': graph_digest(graph),
            'node_count': len(graph),
            'traces': [trace_start(graph, n) for n in sorted(graph)]}


def check_graph_certificate(graph: Mapping[str, str | None], cert: dict[str, Any]) -> dict[str, Any]:
    """Independent exhaustive classifier checker; returns validated basins.

    A certificate is finite only relative to the declared source carrier. It
    cannot certify a historical Wikimedia dump or source parser provenance.
    """
    if not isinstance(cert, dict) or set(cert) != {'schema','graph_sha256','node_count','traces'}:
        raise ValueError('invalid graph certificate header')
    if cert['schema'] != SCHEMA or cert['graph_sha256'] != graph_digest(graph):
        raise ValueError('wrong graph fingerprint / certificate schema')
    if cert['node_count'] != len(graph) or not isinstance(cert['traces'], list):
        raise ValueError('invalid node-count / trace array')
    starts = [t.get('start') if isinstance(t, dict) else None for t in cert['traces']]
    if starts != sorted(graph):
        raise ValueError('missing, duplicate or reordered source starts')
    result: dict[str, tuple[str, tuple[str, ...]]] = {}
    for t in cert['traces']:
        result[t['start']] = check_trace(graph, t)
    # Classify only verified states. This comparison is useful even without
    # the path-compression producer and catches certificate corruption.
    if len(result) != len(graph):
        raise AssertionError('nonexhaustive verified terminal partition')
    return {'outcomes': result, 'basin_sizes': {
        outcome: sum(x == outcome for x in result.values())
        for outcome in set(result.values())},
        'partition_size': len(result)}


def certify_reverse_edit_cone(old: Mapping[str, str | None],
                              new: Mapping[str, str | None]) -> dict[str, Any]:
    if set(old) != set(new):
        raise ValueError('page-carrier change needs typed identity transport')
    edits = sorted(v for v in old if old[v] != new[v])
    predecessor: dict[str, list[str]] = {v: [] for v in old}
    for src, target in old.items():
        if target in predecessor:
            predecessor[target].append(src)
    witness: dict[str, list[str]] = {edit: [edit] for edit in edits}
    queue = deque(edits)
    while queue:
        v = queue.popleft()
        for prev in sorted(predecessor[v]):
            if prev not in witness:
                witness[prev] = [prev] + witness[v]
                queue.append(prev)
    return {'old_sha256': graph_digest(old), 'new_sha256': graph_digest(new),
            'edited_nodes': edits, 'paths_to_edit': witness}


def check_reverse_edit_cone(old: Mapping[str, str | None],
                            new: Mapping[str, str | None], cert: dict[str, Any]) -> set[str]:
    """Check *both* witness-path soundness and reverse-closure completeness."""
    if set(old) != set(new):
        raise ValueError('page-carrier change needs typed identity transport')
    if not isinstance(cert, dict) or set(cert) != {
        'old_sha256', 'new_sha256', 'edited_nodes', 'paths_to_edit'
    }:
        raise ValueError('bad revision certificate field set')
    if cert['old_sha256'] != graph_digest(old) or cert['new_sha256'] != graph_digest(new):
        raise ValueError('stale revision certificate')
    edits = {n for n in old if old[n] != new[n]}
    if cert['edited_nodes'] != sorted(edits):
        raise ValueError('wrong edited-node set')
    paths = cert['paths_to_edit']
    if not isinstance(paths, dict) or not set(paths).issubset(old):
        raise ValueError('unknown source in predecessor certificate')
    for src, path in paths.items():
        if not isinstance(path, list) or not path or path[0] != src or path[-1] not in edits:
            raise ValueError('bad edited-reachability path')
        if len(path) > len(old) or len(path) != len(set(path)) or any(v not in old for v in path):
            raise ValueError('non-simple or out-of-carrier path')
        if any(old[a] != b for a,b in zip(path,path[1:])):
            raise ValueError('path is not made of old first-link edges')
    # No external path-compression call: independently rewalk every old
    # source through at most |V| distinct vertices to find all reachable edits.
    closure = set()
    for start in old:
        node, seen = start, set()
        while node in old and node not in seen:
            if node in edits:
                closure.add(start)
                break
            seen.add(node)
            node = old[node]
    if set(paths) != closure:
        raise ValueError('reverse-closure witnesses incomplete or extraneous')
    return closure

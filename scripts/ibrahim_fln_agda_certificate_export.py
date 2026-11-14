#!/usr/bin/env python3
"""Export a bounded, verified TOTAL first-link graph to an Agda proof object.

Scientific first-link method: Ibrahim, Danforth, Dodds (2017),
DOI 10.1016/j.jocs.2016.12.001. The generated proof-carrying Agda
adapter is NEW DASHI work; not an upstream authors' original theorem,
parser, corpus reconstruction, or any QID/semantic authority.

Each source first passes the independent finite trace certificate checker.
The generated `refl` equalities are rechecked by Agda reduction, not
accepted because a Python Boolean said they were true.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path
from typing import Any, Mapping

import ibrahim_fln_certificates as Certificate
from ibrahim_fln_reference_analysis import check_manifest, checked_graph

MAX_EXPORT_NODES = 64
MODULE_PATTERN = re.compile(r'^[A-Z][a-zA-Z0-9]*(?:\.[A-Z][a-zA-Z0-9]*)+$')


def agda_text(
    graph: Mapping[str, str | None],
    module: str,
    certificate: dict[str, Any] | None = None,
) -> str:
    if not isinstance(module, str) or not MODULE_PATTERN.fullmatch(module):
        raise ValueError('module must be a dotted capitalized Agda identifier')
    if not 1 <= len(graph) <= MAX_EXPORT_NODES:
        raise ValueError('bounded Agda certificate requires 1..64 source vertices')
    if any(not isinstance(k, str) or not k for k in graph):
        raise ValueError('graph source titles must be nonempty strings')
    if any(target not in graph for target in graph.values()):
        raise ValueError('total-graph Agda carrier rejects dead ends and missing targets')
    receipt = certificate if certificate is not None else Certificate.certify_graph(graph)
    verified = Certificate.check_graph_certificate(graph, receipt)
    if verified['partition_size'] != len(graph):
        raise ValueError('incomplete verified certificate')
    nodes = sorted(graph)
    name = {node: f'v{i}' for i, node in enumerate(nodes)}
    lines = [
        f'module {module} where',
        '',
        'open import DASHI.Core.Prelude',
        'import DASHI.Wikimedia.IbrahimGeneralFiniteCertificateKernelExact as General',
        'import DASHI.Wikimedia.IbrahimFiniteOrbitRevisionWeldExact as Orbit',
        '',
        '------------------------------------------------------------------------',
        '-- MACHINE-EMITTED DASHI FINITE FIRST-LINK CERTIFICATE',
        '-- Original method: Ibrahim/Danforth/Dodds (2017),',
        '-- DOI: 10.1016/j.jocs.2016.12.001.',
        '-- This generated finite proof is NOT a historical corpus replay.',
        f'-- Exact canonical source-graph SHA-256: {Certificate.graph_digest(graph)}',
        f'-- Verified source-node count: {len(graph)}',
        '-- Generated edges and repeat equalities remain subject to Agda.',
        '-- No proof holes or trust escapes; no authority promotion.',
        '------------------------------------------------------------------------',
        '',
        'data Vertex : Set where',
        '  ' + ' '.join(name.values()) + ' : Vertex',
        '',
        'next : Vertex → Vertex',
    ]
    lines += [f'next {name[node]} = {name[graph[node]]}' for node in nodes]
    lines += ['', 'allVertices : List Vertex',
              'allVertices = ' + ' ∷ '.join(name.values()) + ' ∷ []', '',
              'complete : General.CompleteFiniteCarrier Vertex',
              'complete = General.completeFiniteCarrier allVertices cover',
              '  where',
              '    cover : (vertex : Vertex) → General.Listed vertex allVertices']
    for i, node in enumerate(nodes):
        witness='General.listedHere'
        for _ in range(i):
            witness=f'General.listedThere ({witness})'
        lines.append(f'    cover {name[node]} = {witness}')
    lines += ['', 'orbitRepeat : (vertex : Vertex) → General.OrbitRepeat next vertex']
    for trace in receipt['traces']:
        node = trace['start']
        if trace['kind'] != 'cycle':
            raise ValueError('total functional graph should terminate only in a cycle')
        entry = trace['entry_index']
        period = len(trace['cycle'])
        lines.append(
            f'orbitRepeat {name[node]} = General.orbitRepeat {entry} {period - 1} refl'
        )
    lines += [
        '', 'allRepeats : General.FiniteOrbitRepeatCertificate next',
        'allRepeats = General.finiteOrbitRepeatCertificate orbitRepeat',
        '', 'checkedCensus : General.VerifiedFiniteFirstLinkCensus next',
        'checkedCensus = General.finiteFirstLinkOrbitClassifies',
        '  next complete allRepeats',
        '',
        'entrySound : (vertex : Vertex) →',
        '  Orbit.iterate next',
        '    (Orbit.entryHops (General.eventCycle checkedCensus vertex)) vertex',
        '  ≡ Orbit.representative (General.eventCycle checkedCensus vertex)',
        'entrySound = General.terminalCensusMatchesCertificate checkedCensus',
        '',
        'chosenRepresentativeBasinPartition :',
        '  General.BasinEquivalence Vertex',
        '    (General.SameRepresentativeBasin checkedCensus)',
        'chosenRepresentativeBasinPartition =',
        '  General.terminalBasinsPartition checkedCensus',
        '',
    ]
    # Keep page names only as JSON escaped comments (not proof identifiers).
    lines += ['------------------------------------------------------------------------',
              '-- Source-title coordinate ledger (navigation only):']
    lines += [f'-- {name[node]} : {json.dumps(node, ensure_ascii=True)}'
              for node in nodes]
    lines += ['']
    return '\n'.join(lines)


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--input',type=Path,required=True)
    p.add_argument('--manifest',type=Path,required=True)
    p.add_argument('--certificate',type=Path,help='verified finite graph trace JSON; optional')
    p.add_argument('--module',required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args()
    check_manifest(args.manifest,args.input)
    graph=checked_graph(json.loads(args.input.read_text(encoding='utf-8')))
    cert=None
    if args.certificate:
        data=json.loads(args.certificate.read_text(encoding='utf-8'))
        cert=data['finite_graph'] if isinstance(data,dict) and 'finite_graph' in data else data
    generated=agda_text(graph,args.module,cert)
    args.output.write_text(generated,encoding='utf-8')


if __name__=='__main__':
    main()

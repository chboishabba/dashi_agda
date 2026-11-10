#!/usr/bin/env python3
"""Admit externally exported canonical Lean declarations into provenance DAG.

THIS COMMAND NEVER CONVERTS SOURCE TEXT OR SOURCE HASHES INTO LEAN TERMS.
Input 1 is the no-checkout original source-world manifest, with complete
acquisition summary. Input 2 is a separate exporter-authored declaration JSONL
containing exact canonical type bytes and original dependencies.

For PR #1483 FibreIndex reuse:
  python3 scripts/run_lean_world_export_admission.py \
    --sources sources.jsonl --exports lean-export.jsonl \
    --index-path ../dashi_pr1483/scripts/lean_world_fibre_index.py

Exporter provenance and kernel-term serialization are external admission
obligations. A JSON row is not independently a Lean proof or kernel certificate.
"""
from __future__ import annotations
import argparse
import importlib.util
import json
from pathlib import Path
import sys

from lean_world_canonical_dag import CanonicalLeanWorld, Origin, WorldError


def jsonl(path: Path):
    with path.open("r", encoding="utf-8") as src:
        for number, line in enumerate(src, 1):
            if not line.strip():
                continue
            try:
                row=json.loads(line)
            except ValueError as exc:
                raise WorldError(f"bad JSONL at {path}:{number}") from exc
            if not isinstance(row,dict):
                raise WorldError(f"non-object row at {path}:{number}")
            yield row


def load_fibre_index(path: Path):
    spec=importlib.util.spec_from_file_location(
        "lean_world_fibre_index",path.resolve())
    if not spec or not spec.loader:
        raise WorldError("PR #1483 FibreIndex module unavailable")
    module=importlib.util.module_from_spec(spec)
    sys.modules[spec.name]=module
    spec.loader.exec_module(module)
    return module


def build(sources, exports, index_path=None):
    receipts=[]
    summaries=[]
    for record in sources:
        if record.get("kind")=="world-source-occurrence":
            receipts.append(record)
        elif record.get("kind")=="world-source-intake-summary":
            summaries.append(record)
    if len(summaries)!=1 or not summaries[0].get("source_complete"):
        raise WorldError("requires exactly one COMPLETE pinned source intake receipt")
    if summaries[0].get("skipped_sources") or (
        summaries[0].get("admitted_source_occurrences")!=len(receipts)):
        raise WorldError("source coverage incomplete or inconsistent")
    if any(x.get("repository")!=summaries[0]["repository"] or
           x.get("revision")!=summaries[0]["revision"] for x in receipts):
        raise WorldError("source corpus/revision mismatch")
    world=CanonicalLeanWorld(receipts)
    count=0
    for item in exports:
        world.admit(item)
        count+=1
    world.seal()
    old_index=world.populate_existing_fibre_index(
        load_fibre_index(Path(index_path))) if index_path else None
    return world,old_index


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--sources",type=Path,required=True)
    p.add_argument("--exports",type=Path,required=True)
    p.add_argument("--index-path",type=Path)
    p.add_argument("--profile")
    p.add_argument("--type-head")
    p.add_argument("--universe-shape")
    p.add_argument("--budget",type=int,default=20)
    p.add_argument("--context-root",nargs=3,
                   metavar=("REPOSITORY","REVISION","DECLARATION"))
    p.add_argument("--max-nodes",type=int,default=100)
    p.add_argument("--max-edges",type=int,default=200)
    args=p.parse_args()
    try:
        world,index=build(
            jsonl(args.sources),jsonl(args.exports),args.index_path)
        report={"kind":"lean-world-export-admission",
                "counts":world.counts(),
                "external_exporter_provenance_validated_by_kernel":False,
                "source_text_promoted_to_proof":False}
        if index:
            report["existing_fibre_index_counts"]=index.inventory()
        if args.profile or args.type_head or args.universe_shape:
            if not all((args.profile,args.type_head,args.universe_shape)):
                p.error("fibre query requires all 3 projection fields")
            report["fibre_query"]=world.fibre_candidates(
                args.profile,args.type_head,args.universe_shape,args.budget)
        if args.context_root:
            report["context_incidence"]=world.context_incidence(
                Origin(*args.context_root),args.max_nodes,args.max_edges)
        print(json.dumps(report,default=str,sort_keys=True,indent=2))
        return 0
    except (OSError,ValueError,TypeError,KeyError) as exc:
        print(f"LEAN_WORLD_EXPORT_INCOMPLETE: {exc}",file=sys.stderr)
        return 2


if __name__=="__main__":
    raise SystemExit(main())

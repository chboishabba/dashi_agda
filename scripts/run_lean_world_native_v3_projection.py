#!/usr/bin/env python3
"""Project a single native-v3 type from an immutable #1494 handoff.

The output is a queryable structural observation, NEVER a Lean theorem
receipt, trusted canonical world row, or complete imported environment.
"""
from __future__ import annotations
from dataclasses import asdict
from hashlib import sha256
from pathlib import Path
import argparse
import base64
import json

from lean_world_builder_contract import pending_from_manifest
from lean_world_native_v3_projection import extract_candidates, NativeV3Error
from lean_world_atomic_spool import publish_immutable

class ProjectionError(ValueError):
    pass

def project(manifest: Path, declaration: str, spool: Path):
    pending=pending_from_manifest(manifest)
    if declaration != pending.declaration:
        raise ProjectionError("requested declaration differs from original handoff")
    candidates=extract_candidates(pending.artifact)
    matches=[c for c in candidates if c.name==declaration]
    if len(matches)!=1:
        raise ProjectionError("selected original declaration absent or ambiguous")
    chosen=matches[0]
    observation={
        "schema":"dashi-lean-v3-type-projection-observation-v1",
        "status":"native-v3-type-projected-uncertified",
        "handoff_key":pending.handoff_key,
        "artifact_sha256":pending.artifact_sha256,
        "repository":pending.repository,"revision":pending.revision,
        "module":pending.module,"declaration":declaration,
        "toolchain":pending.toolchain,
        "dependency_closure_id":pending.dependency_closure_id,
        "source_closure":[list(s) for s in pending.source_closure],
        "declaration_kind":chosen.kind,
        "canonical_type_b64":base64.b64encode(chosen.canonical_type).decode("ascii"),
        "canonical_type_sha256":chosen.type_sha256,
        "direct_statement_constants":list(chosen.direct_constants),
        "proof_value_present":chosen.proof_value_present,
        "native_dag_complete":False,
        "imported_dependencies_resolved":False,
        "kernel_certified":False,
        "world_admitted":False
    }
    encoded=(json.dumps(observation,sort_keys=True,
                        separators=(",",":"))+"\n").encode()
    key=sha256(encoded).hexdigest()
    output=spool/(key+".native-type-observation.json")
    publish_immutable(output,encoded)
    return {"status":observation["status"],"observation_sha256":key,
            "path":str(output),"kernel_certified":False,
            "world_admitted":False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--manifest",required=True,type=Path)
    p.add_argument("--declaration",required=True)
    p.add_argument("--spool",required=True,type=Path)
    args=p.parse_args()
    try:
        result=project(args.manifest,args.declaration,args.spool)
    except (ValueError,OSError,KeyError,RecursionError) as exc:
        p.exit(2,"NATIVE_V3_PROJECTION_INCOMPLETE: "+str(exc)+"\n")
    print(json.dumps(result,sort_keys=True))
    return 0

if __name__=="__main__":
    raise SystemExit(main())

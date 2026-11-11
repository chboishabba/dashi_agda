#!/usr/bin/env python3
"""Native export -> immutable handoff -> pinned external checker observation.

DOES NOT parse the Lean DAG, admit mathematical objects, or certify a kernel.
A success means only that a pinned executable returned zero for exact bytes.
"""
from __future__ import annotations
from dataclasses import asdict
from hashlib import sha256
from pathlib import Path
import argparse
import json
import sys

from lean_world_native_admission_queue import enqueue
from lean_world_builder_contract import pending_from_manifest
from lean_world_external_checker import check_native_export
from lean_world_atomic_spool import publish_immutable

def observe(receipt_path: Path, spool: Path, checker: Path, checker_hash: str,
            *, timeout: int=180):
    raw_receipt=json.loads(receipt_path.read_text(encoding="utf-8"))
    handoff=enqueue(raw_receipt,spool)
    pending=pending_from_manifest(Path(handoff["manifest"]))
    check=check_native_export(
        pending,checker,expected_executable_sha256=checker_hash,
        arguments=("check","--fail-on-axiom","sorryAx"),
        timeout=timeout)
    receipt=asdict(check)
    receipt["schema"]="dashi-lean-external-check-observation-v1"
    receipt["native_manifest_key"]=handoff["handoff_key"]
    receipt["status"]="external-checker-exit-zero-uncertified"
    receipt["world_admitted"]=False
    receipt["kernel_certified"]=False
    # Deterministic immutable observation; no source bytes are repeated.
    encoded=(json.dumps(receipt,sort_keys=True,separators=(",",":"))+"\n").encode()
    observation_key=sha256(encoded).hexdigest()
    output=spool/(observation_key+".checker-observation.json")
    publish_immutable(output,encoded)
    return {"status":receipt["status"],"checker_observation_sha256":observation_key,
            "checker_observation_path":str(output),
            "handoff_key":handoff["handoff_key"],
            "kernel_certified":False,"world_admitted":False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--native-receipt",type=Path,required=True)
    p.add_argument("--spool",type=Path,required=True)
    p.add_argument("--checker-bin",type=Path,required=True)
    p.add_argument("--checker-sha256",required=True)
    p.add_argument("--timeout",type=int,default=180)
    args=p.parse_args()
    try:
        result=observe(args.native_receipt,args.spool,
                       args.checker_bin,args.checker_sha256,
                       timeout=args.timeout)
    except (ValueError,OSError,TypeError) as exc:
        p.exit(2,"LEAN_WORLD_NATIVE_CHECK_INCOMPLETE: "+str(exc)+"\n")
    print(json.dumps(result,sort_keys=True))
    return 0

if __name__=="__main__":
    raise SystemExit(main())

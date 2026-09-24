#!/usr/bin/env python3
"""Invoke the existing generic SLR source-unit PNF parser for Digital-ESD.

This wrapper exists only to freeze paths, hashes and receipts. It does not
modify SLR parser semantics.
"""

from __future__ import annotations
import argparse, hashlib, json, subprocess, sys
from pathlib import Path

def sha256_file(path:Path)->str:
    h=hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda:f.read(1024*1024),b""):
            h.update(chunk)
    return h.hexdigest()

def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument("--repo-root",type=Path,default=Path("."))
    ap.add_argument("--input-jsonl",required=True,type=Path)
    ap.add_argument("--output-dir",required=True,type=Path)
    ap.add_argument("--manifest",required=True,type=Path)
    ap.add_argument("--summary",required=True,type=Path)
    ap.add_argument("--max-source-units",type=int)
    args=ap.parse_args()

    root=args.repo_root.resolve()
    parser=root/"tools/slr-discourse-reconstruct/slr_source_unit_pnf_batch.py"
    if not parser.is_file():
        raise FileNotFoundError(parser)

    args.output_dir.mkdir(parents=True,exist_ok=True)
    args.manifest.parent.mkdir(parents=True,exist_ok=True)
    args.summary.parent.mkdir(parents=True,exist_ok=True)

    cmd=[
        sys.executable,str(parser),
        "--input-jsonl",str(args.input_jsonl),
        "--output-dir",str(args.output_dir),
        "--manifest",str(args.manifest),
        "--summary",str(args.summary),
    ]
    if args.max_source_units is not None:
        cmd += ["--max-source-units",str(args.max_source_units)]

    completed=subprocess.run(cmd,cwd=root,check=False)
    if completed.returncode!=0:
        raise SystemExit(completed.returncode)

    receipt={
        "schema":"digital-esd-generic-slr-parse-run-v1",
        "input_jsonl_reference":str(args.input_jsonl),
        "input_jsonl_sha256":sha256_file(args.input_jsonl),
        "generic_parser_reference":str(parser),
        "generic_parser_sha256":sha256_file(parser),
        "parser_summary_reference":str(args.summary),
        "parser_summary_sha256":sha256_file(args.summary),
        "parser_manifest_reference":str(args.manifest),
        "parser_manifest_sha256":sha256_file(args.manifest),
        "parser_exit_code":completed.returncode,
        "digital_esd_wrapper_changes_parser_semantics":False,
        "parser_output_creates_claim_truth":False,
        "parser_output_creates_source_audit_admission":False,
    }
    receipt_path=args.summary.with_name(args.summary.stem+".digital-esd-receipt.json")
    receipt_path.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(f"DIGITAL_ESD_GENERIC_SLR_PARSE receipt={receipt_path}")
    return 0

if __name__=="__main__":
    raise SystemExit(main())

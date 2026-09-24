#!/usr/bin/env python3
"""Run the thin Digital-ESD study-parse interop pipeline.

Stages:
  verified full-text index
    -> Digital-ESD source-unit adapter
    -> existing generic SLR PNF parser
    -> Digital-ESD 19-coordinate candidate extraction packets

This controller does not screen studies, review parser output, pay extraction
coordinates, or create SourceAuditAdmission.
"""

from __future__ import annotations
import argparse, subprocess, sys
from pathlib import Path

HERE=Path(__file__).resolve().parent

def run(cmd:list[str])->None:
    completed=subprocess.run(cmd,check=False)
    if completed.returncode!=0:
        raise SystemExit(completed.returncode)

def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument("--repo-root",type=Path,default=Path("."))
    ap.add_argument("--fulltext-index",required=True,type=Path)
    ap.add_argument("--out-dir",required=True,type=Path)
    ap.add_argument("--purpose",choices=["retained-study","screening-resolution"],default="retained-study")
    ap.add_argument("--max-source-units",type=int)
    args=ap.parse_args()

    out=args.out_dir
    out.mkdir(parents=True,exist_ok=True)
    source_units=out/"slr-source-units.jsonl"
    records=out/"slr-records"
    parser_manifest=out/"slr-parser-manifest.jsonl"
    parser_summary=out/"slr-parser-summary.json"
    packets=out/"digital-esd-packets"

    run([
      sys.executable,str(HERE/"prepare_slr_source_units.py"),
      "--fulltext-index",str(args.fulltext_index),
      "--output",str(source_units),
      "--purpose",args.purpose,
    ])

    cmd=[
      sys.executable,str(HERE/"run_slr_source_unit_parse.py"),
      "--repo-root",str(args.repo_root),
      "--input-jsonl",str(source_units),
      "--output-dir",str(records),
      "--manifest",str(parser_manifest),
      "--summary",str(parser_summary),
    ]
    if args.max_source_units is not None:
        cmd += ["--max-source-units",str(args.max_source_units)]
    run(cmd)

    run([
      sys.executable,str(HERE/"compile_study_extraction_packets.py"),
      "--source-units",str(source_units),
      "--parser-manifest",str(parser_manifest),
      "--output-dir",str(packets),
    ])

    print(
      "DIGITAL_ESD_STUDY_PARSE_PIPELINE "
      f"purpose={args.purpose} source_units={source_units} packets={packets}"
    )
    return 0

if __name__=="__main__":
    raise SystemExit(main())

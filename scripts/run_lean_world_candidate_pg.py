#!/usr/bin/env python3
"""Complete SOURCE-VERIFIED candidate intake to PostgreSQL; NOT proof certification.

Use with existing #1484 source-world JSONL and separately produced
lean-elaborated-export JSONL. This DOES NOT parse or certify Lean native-v3.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import sys

from run_lean_world_export_admission import build, jsonl
from lean_world_postgres_candidate import persist_candidate_world

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources",required=True,type=Path)
    parser.add_argument("--exports",required=True,type=Path)
    parser.add_argument("--acknowledge-unverified-candidates",
                        action="store_true",required=True)
    args=parser.parse_args(argv)
    if not args.acknowledge_unverified_candidates:
        parser.error("explicit candidate-only acknowledgement required")
    try:
        import psycopg
        world,_=build(jsonl(args.sources),jsonl(args.exports))
        # PG* environment is the only credential source; no connection string
        # is accepted from the export or untrusted source material.
        with psycopg.connect("") as connection:
            result=persist_candidate_world(connection,world)
        print(json.dumps(result,sort_keys=True))
        return 0
    except (OSError,ValueError,KeyError,ImportError) as exc:
        print("LEAN_WORLD_CANDIDATE_INCOMPLETE: "+str(exc),file=sys.stderr)
        return 2

if __name__=="__main__":
    raise SystemExit(main())

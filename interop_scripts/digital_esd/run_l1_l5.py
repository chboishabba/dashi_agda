#!/usr/bin/env python3
"""Run the real Digital-ESD path through actual scholarly full-text parsing.

Thin orchestration only.  Substantive owners remain in the SLR repository.

L1-L3:
  SLR scripts/run_digital_esd_l1_l3.py

L4-L5:
  dashi thin bridge -> SLR scholarly_fulltext.py -> explicit parse receipts

The command fails if L4/L5 cannot be paid from real verified full-text bytes.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent


def resolve_slr_root(explicit: Path | None) -> Path:
    if explicit is not None:
        root = explicit.resolve()
    elif os.environ.get("SLR_REPO_ROOT"):
        root = Path(os.environ["SLR_REPO_ROOT"]).resolve()
    else:
        root = (Path(__file__).resolve().parents[3] / "slr").resolve()
    if not (root / "scripts" / "run_digital_esd_l1_l3.py").exists():
        raise SystemExit(f"SLR Digital-ESD runtime not found: {root}")
    return root


def run(cmd: list[str], cwd: Path | None = None) -> None:
    print("+", " ".join(cmd), file=sys.stderr, flush=True)
    subprocess.run(cmd, cwd=cwd, check=True)


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("--slr-root", type=Path)
    ap.add_argument(
        "--artifact-root",
        type=Path,
        default=Path("artifacts/digital-esd/real-eric"),
    )
    ap.add_argument("--parse-output-dir", type=Path)
    ap.add_argument("--parse-max-items", type=int)
    ap.add_argument("--allow-partial-parse", action="store_true")

    # Everything else belongs to the generic SLR L1-L3 driver:
    # --export-root, --decision-overlay, --retrieved-manifest, etc.
    args, forwarded = ap.parse_known_args()

    slr_root = resolve_slr_root(args.slr_root)

    l1l3 = HERE / "run_l1_l3.py"
    l1l3_cmd = [
        sys.executable,
        str(l1l3),
        "--slr-root",
        str(slr_root),
        "--artifact-root",
        str(args.artifact_root),
        *forwarded,
    ]
    run(l1l3_cmd)

    parse_wrapper = HERE / "run_verified_fulltext_parse.py"
    parse_cmd = [
        sys.executable,
        str(parse_wrapper),
        "--slr-root",
        str(slr_root),
        "--artifact-root",
        str(args.artifact_root),
    ]
    if args.parse_output_dir:
        parse_cmd.extend(["--output-dir", str(args.parse_output_dir)])
    if args.parse_max_items is not None:
        parse_cmd.extend(["--max-items", str(args.parse_max_items)])
    if args.allow_partial_parse:
        parse_cmd.append("--allow-partial")

    run(parse_cmd)

    print(
        "DIGITAL_ESD_L1_L5_COMPLETE "
        "metadata_screening_fulltext_and_scholarly_parse=true "
        "parse_creates_reviewed_evidence=false "
        "parse_creates_source_audit_admission=false",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

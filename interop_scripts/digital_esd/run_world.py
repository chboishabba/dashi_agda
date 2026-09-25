#!/usr/bin/env python3
"""Zero-flag Digital-ESD corpus -> PostgreSQL world orchestration.

Normal agent entry point:

    python3 interop_scripts/digital_esd/run_world.py

Persistent world state is owned by SLR/PostgreSQL. This wrapper only:
  1. advances the existing explicit-review/retrieve/parse loop when possible;
  2. delegates world materialisation to SLR's DB-native world runtime;
  3. prints the bounded inspection receipt returned by SLR.

It deliberately does not materialise corpus-wide nodes.jsonl/edges.jsonl.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path


HERE = Path(__file__).resolve().parent
DASHI_ROOT = HERE.parents[1]
DEFAULT_ARTIFACT_REL = Path("artifacts/digital-esd/real-eric")


def resolve_slr_root() -> Path:
    if os.environ.get("SLR_REPO_ROOT"):
        root = Path(os.environ["SLR_REPO_ROOT"]).resolve()
    else:
        root = (DASHI_ROOT.parent / "slr").resolve()
    if not (root / "Cargo.toml").exists():
        raise FileNotFoundError(
            f"SLR checkout not found at {root}; set SLR_REPO_ROOT once if needed"
        )
    return root


def resolve_artifact_root(slr_root: Path) -> Path:
    if os.environ.get("DIGITAL_ESD_ARTIFACT_ROOT"):
        return Path(os.environ["DIGITAL_ESD_ARTIFACT_ROOT"]).resolve()
    return (slr_root / DEFAULT_ARTIFACT_REL).resolve()


def run(cmd: list[str], *, cwd: Path, env: dict[str, str] | None = None) -> None:
    print("+", " ".join(cmd), file=sys.stderr)
    subprocess.run(cmd, cwd=cwd, env=env, check=True)


def maybe_advance_existing_loop(slr_root: Path, artifact_root: Path) -> str:
    loop = HERE / "run_screen_review_retrieve_parse_loop.py"
    if not loop.exists():
        return "loop-wrapper-missing"

    reviewed = artifact_root / "screening_ledger_reviewed.tsv"
    base = artifact_root / "screening_ledger.tsv"
    if not reviewed.exists() and not base.exists():
        return "screening-ledger-missing"

    decisions = artifact_root / "review" / "completed-decisions.jsonl"
    if decisions.exists() and decisions.stat().st_size > 0:
        run(
            [
                sys.executable,
                str(loop),
                "advance",
                "--slr-root",
                str(slr_root),
                "--artifact-root",
                str(artifact_root),
                "--decisions",
                str(decisions),
                "--parse-verified",
            ],
            cwd=DASHI_ROOT,
        )
        return "advanced-reviewed-overlay"

    run(
        [
            sys.executable,
            str(loop),
            "prepare-review",
            "--slr-root",
            str(slr_root),
            "--artifact-root",
            str(artifact_root),
        ],
        cwd=DASHI_ROOT,
    )
    return "awaiting-explicit-review"


def main() -> int:
    slr_root = resolve_slr_root()
    artifact_root = resolve_artifact_root(slr_root)
    loop_state = maybe_advance_existing_loop(slr_root, artifact_root)

    processing_ledger = artifact_root / "slr-parse" / "study-processing-ledger.jsonl"
    if not processing_ledger.exists():
        raise FileNotFoundError(
            f"processing ledger not found after orchestration: {processing_ledger}"
        )

    env = os.environ.copy()
    env["DIGITAL_ESD_ARTIFACT_ROOT"] = str(artifact_root)

    cmd = [
        "cargo",
        "run",
        "-q",
        "-p",
        "sensiblaw-world-expansion-runtime",
        "--bin",
        "digital_esd_world",
        "--",
        "--processing-ledger",
        str(processing_ledger),
    ]
    completed = subprocess.run(
        cmd,
        cwd=slr_root,
        env=env,
        check=True,
        text=True,
        capture_output=True,
    )
    if completed.stderr:
        print(completed.stderr, file=sys.stderr, end="")

    receipt = json.loads(completed.stdout)
    receipt["orchestration_state"] = loop_state
    receipt["persistent_world_owner"] = "PostgreSQL/SLR"
    receipt["flat_json_is_canonical_runtime_state"] = False
    receipt["corpus_wide_json_graph_emitted"] = False
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

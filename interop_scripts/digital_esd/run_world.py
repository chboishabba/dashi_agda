#!/usr/bin/env python3
"""Zero-flag Digital-ESD corpus -> PostgreSQL world orchestration.

Normal agent entry point:

    python3 interop_scripts/digital_esd/run_world.py

Persistent world state is owned by SLR/PostgreSQL. This wrapper composes the
existing authority-preserving stages and returns one bounded inspection receipt.

The production path is:

    screening/review/retrieval
      -> verified/materialised scholarly text
      -> SCALE-1 DB-native source/region/parser/PNF/reconciliation pipeline
      -> SLR PostgreSQL world revision
      -> bounded agent inspection

It deliberately does not materialise corpus-wide nodes.jsonl/edges.jsonl.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path
from typing import Any


HERE = Path(__file__).resolve().parent
DASHI_ROOT = HERE.parents[1]
DEFAULT_ARTIFACT_REL = Path("artifacts/digital-esd/real-eric")
DEFAULT_SCALE1_MODEL = "en_core_web_sm"


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


def run(
    cmd: list[str],
    *,
    cwd: Path,
    env: dict[str, str] | None = None,
) -> None:
    print("+", " ".join(cmd), file=sys.stderr)
    subprocess.run(cmd, cwd=cwd, env=env, check=True)


def run_json(
    cmd: list[str],
    *,
    cwd: Path,
    env: dict[str, str] | None = None,
) -> dict[str, Any]:
    print("+", " ".join(cmd), file=sys.stderr)
    completed = subprocess.run(
        cmd,
        cwd=cwd,
        env=env,
        check=True,
        text=True,
        capture_output=True,
    )
    if completed.stderr:
        print(completed.stderr, file=sys.stderr, end="")
    value = json.loads(completed.stdout)
    if not isinstance(value, dict):
        raise RuntimeError(f"expected JSON object from {' '.join(cmd)}")
    return value


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as fh:
        for line_number, line in enumerate(fh, 1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_number}: expected JSON object")
            rows.append(row)
    return rows


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def resolve_materialized_path(
    value: str,
    *,
    slr_root: Path,
    artifact_root: Path,
) -> Path:
    raw = Path(value)
    if raw.is_absolute():
        return raw.resolve()
    candidates = [
        (artifact_root / raw).resolve(),
        (slr_root / raw).resolve(),
        raw.resolve(),
    ]
    return next((candidate for candidate in candidates if candidate.exists()), candidates[0])


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


def scale1_example_binary(slr_root: Path, env: dict[str, str]) -> Path:
    run(
        [
            "cargo",
            "build",
            "-q",
            "-p",
            "sensiblaw-pg-source-store",
            "--example",
            "scale1_long_document",
        ],
        cwd=slr_root,
        env=env,
    )
    target = Path(env.get("CARGO_TARGET_DIR", "target"))
    if not target.is_absolute():
        target = (slr_root / target).resolve()
    binary = target / "debug" / "examples" / "scale1_long_document"
    if not binary.exists():
        raise FileNotFoundError(f"SCALE-1 example binary not found after build: {binary}")
    return binary


def compile_materialized_fulltexts(
    slr_root: Path,
    artifact_root: Path,
    env: dict[str, str],
) -> dict[str, Any]:
    receipts_path = artifact_root / "slr-parse" / "materialization-receipts.jsonl"
    rows = read_jsonl(receipts_path)
    if not rows:
        return {
            "materialization_receipts": 0,
            "prepared_sources": 0,
            "finalized_sources": 0,
            "failed_sources": 0,
            "failures": [],
            "parser_model": env.get("DIGITAL_ESD_SCALE1_MODEL", DEFAULT_SCALE1_MODEL),
        }

    binary = scale1_example_binary(slr_root, env)
    model_ref = env.get("DIGITAL_ESD_SCALE1_MODEL", DEFAULT_SCALE1_MODEL)
    parser_script = env.get(
        "DIGITAL_ESD_SCALE1_PARSER",
        str(slr_root / "scripts" / "scale1_spacy_json_parser.py"),
    )
    worker_ref = env.get("DIGITAL_ESD_SCALE1_WORKER", "worker:digital-esd:run-world")
    batch_size = env.get("DIGITAL_ESD_SCALE1_BATCH_SIZE", "64")

    prepared = 0
    finalized = 0
    failures: list[dict[str, str]] = []

    for row in rows:
        source_ref = str(row.get("source_identity_reference") or "").strip()
        materialization_ref = str(
            row.get("materialization_receipt_reference")
            or row.get("source_revision_reference")
            or ""
        ).strip()
        artifact_value = str(row.get("artifact_path") or "").strip()
        expected_digest = str(row.get("content_sha256") or "").lower().removeprefix("sha256:")

        if not source_ref or not materialization_ref or not artifact_value or not expected_digest:
            failures.append({
                "source_identity_reference": source_ref or "<missing>",
                "stage": "input-validation",
                "reason": "materialization receipt lacks required identity/path/digest",
            })
            continue

        artifact = resolve_materialized_path(
            artifact_value,
            slr_root=slr_root,
            artifact_root=artifact_root,
        )
        if not artifact.exists():
            failures.append({
                "source_identity_reference": source_ref,
                "stage": "input-validation",
                "reason": f"materialized text missing: {artifact}",
            })
            continue
        observed_digest = sha256_file(artifact)
        if observed_digest != expected_digest:
            failures.append({
                "source_identity_reference": source_ref,
                "stage": "input-validation",
                "reason": (
                    "materialized text digest mismatch: "
                    f"expected={expected_digest} observed={observed_digest}"
                ),
            })
            continue

        provider_ref = "digital-esd:verified-fulltext-materialization"
        acquisition_ref = f"digital-esd:{materialization_ref}"

        try:
            prepare = run_json(
                [
                    str(binary),
                    "prepare-spacy",
                    str(artifact),
                    source_ref,
                    provider_ref,
                    acquisition_ref,
                    model_ref,
                    "{}",
                    parser_script,
                ],
                cwd=slr_root,
                env=env,
            )
            prepared += 1
            parser_run_ref = str(prepare["parser_run_ref"])

            run_json(
                [
                    str(binary),
                    "worker",
                    parser_run_ref,
                    worker_ref,
                    batch_size,
                    parser_script,
                ],
                cwd=slr_root,
                env=env,
            )

            final = run_json(
                [str(binary), "finalize", parser_run_ref],
                cwd=slr_root,
                env=env,
            )
            if final.get("unattempted_semantic_regions") != 0:
                raise RuntimeError("finalized source retained unattempted semantic regions")
            if final.get("source_region_loss_count") != 0:
                raise RuntimeError("finalized source lost canonical source regions")
            if final.get("candidate_only") is not True:
                raise RuntimeError("SCALE-1 final receipt crossed candidate-only boundary")
            if final.get("creates_semantic_authority") is not False:
                raise RuntimeError("SCALE-1 final receipt created semantic authority")
            finalized += 1
        except (subprocess.CalledProcessError, KeyError, RuntimeError, json.JSONDecodeError) as exc:
            failures.append({
                "source_identity_reference": source_ref,
                "stage": "scale1-db-native",
                "reason": str(exc),
            })

    return {
        "materialization_receipts": len(rows),
        "prepared_sources": prepared,
        "finalized_sources": finalized,
        "failed_sources": len(failures),
        "failures": failures[:100],
        "failures_bounded": len(failures) > 100,
        "parser_model": model_ref,
        "persistent_state": "PostgreSQL/SLR",
        "candidate_only": True,
        "creates_semantic_authority": False,
    }


def main() -> int:
    slr_root = resolve_slr_root()
    artifact_root = resolve_artifact_root(slr_root)
    env = os.environ.copy()
    env["DIGITAL_ESD_ARTIFACT_ROOT"] = str(artifact_root)

    loop_state = maybe_advance_existing_loop(slr_root, artifact_root)
    scale1_state = compile_materialized_fulltexts(slr_root, artifact_root, env)

    processing_ledger = artifact_root / "slr-parse" / "study-processing-ledger.jsonl"
    if not processing_ledger.exists():
        raise FileNotFoundError(
            f"processing ledger not found after orchestration: {processing_ledger}"
        )

    receipt = run_json(
        [
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
        ],
        cwd=slr_root,
        env=env,
    )
    receipt["orchestration_state"] = loop_state
    receipt["scale1_db_native"] = scale1_state
    receipt["persistent_world_owner"] = "PostgreSQL/SLR"
    receipt["flat_json_is_canonical_runtime_state"] = False
    receipt["corpus_wide_json_graph_emitted"] = False
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

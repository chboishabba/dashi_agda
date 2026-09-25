#!/usr/bin/env python3
"""Zero-flag Digital-ESD corpus -> PostgreSQL world orchestration.

Normal agent entry point:

    python3 interop_scripts/digital_esd/run_world.py

Persistent world state is owned by SLR/PostgreSQL. JSON/TSV files produced here
are bounded inspection or compatibility/census surfaces, never the canonical
semantic database.

Normal path:

    explicit screening review / retrieval
      -> verified bytes
      -> materialise UTF-8 only
      -> SCALE-1 DB-native prepare / worker / finalize
      -> thin compatibility handoff + parse receipts
      -> exact 43,996-row processing ledger refresh
      -> PostgreSQL world revision
      -> bounded agent inspection

The legacy scholarly parser remains available through
run_verified_fulltext_parse.py without --materialize-only, but is deliberately
not run by this world builder.
"""

from __future__ import annotations

import csv
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
        raise RuntimeError(f"expected one JSON object from {' '.join(cmd)}")
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


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        for row in rows:
            fh.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


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


def authoritative_ledger(artifact_root: Path) -> Path:
    reviewed = artifact_root / "screening_ledger_reviewed.tsv"
    base = artifact_root / "screening_ledger.tsv"
    if reviewed.exists():
        return reviewed
    if base.exists():
        return base
    raise FileNotFoundError(f"no screening ledger under {artifact_root}")


def maybe_advance_existing_loop(slr_root: Path, artifact_root: Path) -> str:
    loop = HERE / "run_screen_review_retrieve_parse_loop.py"
    if not loop.exists():
        return "loop-wrapper-missing"

    try:
        authoritative_ledger(artifact_root)
    except FileNotFoundError:
        return "screening-ledger-missing"

    decisions = artifact_root / "review" / "completed-decisions.jsonl"
    if decisions.exists() and decisions.stat().st_size > 0:
        # Deliberately omit --parse-verified. The canonical semantic parse is
        # SCALE-1 below; this loop owns review/retrieval/full-text verification.
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
            ],
            cwd=DASHI_ROOT,
        )
        return "advanced-reviewed-overlay"

    if (artifact_root / "screening_ledger_reviewed.tsv").exists():
        run(
            [
                sys.executable,
                str(loop),
                "resume",
                "--slr-root",
                str(slr_root),
                "--artifact-root",
                str(artifact_root),
            ],
            cwd=DASHI_ROOT,
        )
        return "resumed-retrieval-without-decision-replay"

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


def verified_fulltext_count(artifact_root: Path) -> int:
    path = artifact_root / "fulltext" / "digital_esd_fulltext_index.tsv"
    if not path.exists():
        return 0
    with path.open(newline="", encoding="utf-8") as fh:
        return sum(
            1
            for row in csv.DictReader(fh, delimiter="\t")
            if row.get("status") == "verified"
        )


def materialize_verified_fulltexts(
    slr_root: Path,
    artifact_root: Path,
) -> dict[str, Any]:
    count = verified_fulltext_count(artifact_root)
    if count == 0:
        return {
            "verified_fulltext_count": 0,
            "materialized_text_count": 0,
            "materialization_failure_count": 0,
            "legacy_scholarly_parser_invoked": False,
        }

    script = HERE / "run_verified_fulltext_parse.py"
    run(
        [
            sys.executable,
            str(script),
            "--slr-root",
            str(slr_root),
            "--artifact-root",
            str(artifact_root),
            "--materialize-only",
            "--allow-partial",
        ],
        cwd=DASHI_ROOT,
    )
    receipt_path = (
        artifact_root
        / "slr-parse"
        / "verified-fulltext-materialization-run.json"
    )
    if not receipt_path.exists():
        raise FileNotFoundError(
            f"materialisation command did not emit receipt: {receipt_path}"
        )
    receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
    if not isinstance(receipt, dict):
        raise ValueError(f"{receipt_path}: expected object")
    return receipt


def scale1_example_binary(slr_root: Path, env: dict[str, str]) -> Path:
    # Build exactly once; reuse the executable across every study.
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
        raise FileNotFoundError(
            f"SCALE-1 example binary not found after build: {binary}"
        )
    return binary


def merge_receipts_by_source(
    path: Path,
    new_rows: list[dict[str, Any]],
    *,
    invalidate_source_refs: set[str] | None = None,
) -> None:
    invalidated = invalidate_source_refs or set()
    by_ref: dict[str, dict[str, Any]] = {}
    for row in read_jsonl(path):
        ref = str(row.get("source_identity_reference") or "").strip()
        if ref and ref not in invalidated:
            by_ref[ref] = row
    for row in new_rows:
        ref = str(row.get("source_identity_reference") or "").strip()
        if not ref:
            raise ValueError("compatibility receipt lacks source identity")
        by_ref[ref] = row
    write_jsonl(path, [by_ref[ref] for ref in sorted(by_ref)])


def compile_materialized_fulltexts(
    slr_root: Path,
    artifact_root: Path,
    env: dict[str, str],
) -> dict[str, Any]:
    parse_root = artifact_root / "slr-parse"
    receipts_path = parse_root / "materialization-receipts.jsonl"
    rows = read_jsonl(receipts_path)
    if not rows:
        return {
            "materialization_receipts": 0,
            "prepared_sources": 0,
            "finalized_sources": 0,
            "failed_sources": 0,
            "failures": [],
            "parser_model": env.get(
                "DIGITAL_ESD_SCALE1_MODEL",
                DEFAULT_SCALE1_MODEL,
            ),
            "legacy_scholarly_parser_invoked": False,
        }

    binary = scale1_example_binary(slr_root, env)
    model_ref = env.get("DIGITAL_ESD_SCALE1_MODEL", DEFAULT_SCALE1_MODEL)
    parser_script = env.get(
        "DIGITAL_ESD_SCALE1_PARSER",
        str(slr_root / "scripts" / "scale1_spacy_json_parser.py"),
    )
    worker_ref = env.get(
        "DIGITAL_ESD_SCALE1_WORKER",
        "worker:digital-esd:run-world",
    )
    batch_size = env.get("DIGITAL_ESD_SCALE1_BATCH_SIZE", "64")

    prepared = 0
    finalized = 0
    failures: list[dict[str, str]] = []
    handoff_receipts: list[dict[str, Any]] = []
    parse_receipts: list[dict[str, Any]] = []
    current_sources = {
        str(row.get("source_identity_reference") or "").strip()
        for row in rows
        if str(row.get("source_identity_reference") or "").strip()
    }

    for row in rows:
        source_ref = str(row.get("source_identity_reference") or "").strip()
        materialization_ref = str(
            row.get("materialization_receipt_reference")
            or row.get("source_revision_reference")
            or ""
        ).strip()
        artifact_value = str(row.get("artifact_path") or "").strip()
        expected_digest = str(
            row.get("content_sha256") or ""
        ).lower().removeprefix("sha256:")

        if (
            not source_ref
            or not materialization_ref
            or not artifact_value
            or not expected_digest
        ):
            failures.append({
                "source_identity_reference": source_ref or "<missing>",
                "stage": "input-validation",
                "reason": (
                    "materialization receipt lacks required "
                    "identity/path/digest"
                ),
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
            source_revision_ref = str(prepare["source_revision_ref"])

            handoff_receipts.append({
                "schema": "digital-esd-scale1-db-handoff-v1",
                "source_identity_reference": source_ref,
                "source_revision_reference": source_revision_ref,
                "materialization_receipt_reference": materialization_ref,
                "parser_run_reference": parser_run_ref,
                "handoff_status": "handed-to-scale1-db",
                "handed_to_slr": True,
                "candidate_only": True,
                "creates_source_truth": False,
                "creates_source_audit_admission": False,
            })

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
                raise RuntimeError(
                    "finalized source retained unattempted semantic regions"
                )
            if final.get("source_region_loss_count") != 0:
                raise RuntimeError(
                    "finalized source lost canonical source regions"
                )
            if final.get("candidate_only") is not True:
                raise RuntimeError(
                    "SCALE-1 final receipt crossed candidate-only boundary"
                )
            if final.get("creates_semantic_authority") is not False:
                raise RuntimeError(
                    "SCALE-1 final receipt created semantic authority"
                )

            parse_receipts.append({
                "schema": "digital-esd-scale1-db-parse-receipt-v1",
                "source_identity_reference": source_ref,
                "source_revision_reference": str(
                    final.get("source_revision_ref") or source_revision_ref
                ),
                "content_sha256": expected_digest,
                "parser_run_reference": parser_run_ref,
                "parsed": True,
                "parse_success": True,
                "compiled_statement_count": int(
                    final.get("compiled_statement_count") or 0
                ),
                "candidate_pnf_count": int(
                    final.get("candidate_pnf_count") or 0
                ),
                "candidate_only": True,
                "creates_semantic_authority": False,
                "applicability_promoted": False,
                "claim_truth_promoted": False,
                "creates_source_audit_admission": False,
            })
            finalized += 1
        except (
            subprocess.CalledProcessError,
            KeyError,
            RuntimeError,
            json.JSONDecodeError,
        ) as exc:
            failures.append({
                "source_identity_reference": source_ref,
                "stage": "scale1-db-native",
                "reason": str(exc),
            })

    # These remain compatibility/census surfaces. PostgreSQL is canonical.
    merge_receipts_by_source(
        parse_root / "scale1-handoff-receipts.jsonl",
        handoff_receipts,
        invalidate_source_refs=current_sources,
    )
    merge_receipts_by_source(
        parse_root / "scale1-parse-receipts.jsonl",
        parse_receipts,
        invalidate_source_refs=current_sources,
    )

    return {
        "materialization_receipts": len(rows),
        "prepared_sources": prepared,
        "finalized_sources": finalized,
        "failed_sources": len(failures),
        "failures": failures[:100],
        "failures_bounded": len(failures) > 100,
        "scale1_compatibility_handoff_receipts_written": len(handoff_receipts),
        "scale1_compatibility_parse_receipts_written": len(parse_receipts),
        "scale1_handoff_receipts_reference": str(
            parse_root / "scale1-handoff-receipts.jsonl"
        ),
        "scale1_parse_receipts_reference": str(
            parse_root / "scale1-parse-receipts.jsonl"
        ),
        "parser_model": model_ref,
        "persistent_state": "PostgreSQL/SLR",
        "legacy_scholarly_parser_invoked": False,
        "candidate_only": True,
        "creates_semantic_authority": False,
    }


def rebuild_processing_ledger(
    artifact_root: Path,
) -> Path:
    parse_root = artifact_root / "slr-parse"
    fulltext_index = (
        artifact_root / "fulltext" / "digital_esd_fulltext_index.tsv"
    )
    if not fulltext_index.exists():
        raise FileNotFoundError(fulltext_index)

    processing = parse_root / "study-processing-ledger.jsonl"
    manifest = parse_root / "study-processing-ledger-manifest.json"
    cmd = [
        sys.executable,
        str(HERE / "build_processing_ledger.py"),
        "--screening-ledger",
        str(authoritative_ledger(artifact_root)),
        "--fulltext-index",
        str(fulltext_index),
        "--output-ledger",
        str(processing),
        "--output-manifest",
        str(manifest),
    ]
    scale1_handoff = parse_root / "scale1-handoff-receipts.jsonl"
    scale1_parse = parse_root / "scale1-parse-receipts.jsonl"
    legacy_handoff = parse_root / "slr-handoff-receipts.jsonl"
    legacy_parse = parse_root / "slr-parse-receipts.jsonl"
    handoff = scale1_handoff if scale1_handoff.exists() else legacy_handoff
    parse = scale1_parse if scale1_parse.exists() else legacy_parse

    optional = [
        ("--materialization-receipts", parse_root / "materialization-receipts.jsonl"),
        ("--slr-handoff", handoff),
        ("--slr-parse-receipts", parse),
        ("--slr-review-receipts", parse_root / "slr-review-receipts.jsonl"),
        ("--source-audit-receipts", parse_root / "source-audit-receipts.jsonl"),
    ]
    for flag, path in optional:
        if path.exists():
            cmd.extend([flag, str(path)])

    run(cmd, cwd=DASHI_ROOT)
    return processing


def main() -> int:
    slr_root = resolve_slr_root()
    artifact_root = resolve_artifact_root(slr_root)
    env = os.environ.copy()
    env["DIGITAL_ESD_ARTIFACT_ROOT"] = str(artifact_root)

    loop_state = maybe_advance_existing_loop(slr_root, artifact_root)
    materialization_state = materialize_verified_fulltexts(
        slr_root,
        artifact_root,
    )
    scale1_state = compile_materialized_fulltexts(
        slr_root,
        artifact_root,
        env,
    )
    processing_ledger = rebuild_processing_ledger(artifact_root)

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
    receipt["materialization"] = materialization_state
    receipt["scale1_db_native"] = scale1_state
    receipt["persistent_world_owner"] = "PostgreSQL/SLR"
    receipt["flat_json_is_canonical_runtime_state"] = False
    receipt["corpus_wide_json_graph_emitted"] = False
    receipt["legacy_scholarly_parser_invoked"] = False
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

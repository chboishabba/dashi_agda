#!/usr/bin/env python3
"""Thin Digital-ESD <-> SLR interoperability wrapper.

This file deliberately does not implement parsing, review, canonical evidence
semantics, or reduction.  It owns only application-side invocation and
same-object reconciliation.

Subcommands
-----------
prepare
    Validate a Digital-ESD full-text/canonical-evidence JSONL and emit a stable
    interop request JSONL.

run
    Invoke a configured external SLR command.  The command is supplied in a
    JSON config and may use {input} and {output_dir} placeholders.

verify
    Reconcile normalized SLR receipt JSONL against the prepared request and
    emit an application-side invocation receipt.

The normalized SLR receipt contract is intentionally small and canonical:
    source_identity_reference
    source_revision_ref
    content_digest_ref
    observation_ref
    candidate_only
    creates_semantic_authority
    applicability_promoted
    claim_truth_promoted

A successful process exit is never treated as evidence payment.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
from typing import Any


WRAPPER_VERSION = "digital-esd-slr-interop-v1"


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
        + "\n"
    ).encode("utf-8")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    with path.open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            if not line.strip():
                continue
            row = json.loads(line)
            if not isinstance(row, dict):
                raise ValueError(f"{path}:{line_no}: expected JSON object")
            rows.append(row)
    return rows


def write_jsonl(path: Path, rows: list[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as handle:
        for row in rows:
            handle.write(
                json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n"
            )


def first_nonempty(row: dict[str, Any], *keys: str) -> str:
    for key in keys:
        value = row.get(key)
        if isinstance(value, str) and value.strip():
            return value.strip()
    return ""


def normalize_digest(value: str) -> str:
    value = value.strip().lower()
    if value.startswith("sha256:"):
        value = value[7:]
    if len(value) != 64:
        raise ValueError(f"expected SHA-256 digest, got {value!r}")
    int(value, 16)
    return "sha256:" + value


def normalize_input_row(row: dict[str, Any], line_no: int) -> dict[str, Any]:
    source_ref = first_nonempty(
        row,
        "source_identity_reference",
        "source_ref",
        "attributed_source_reference",
    )
    revision_ref = first_nonempty(
        row,
        "source_revision_ref",
        "fullTextRevisionReference",
        "revision_ref",
    )
    digest_raw = first_nonempty(
        row,
        "content_digest_ref",
        "artifact_sha256",
        "fullTextArtifactSha256",
        "sha256",
    )
    artifact_ref = first_nonempty(
        row,
        "artifact_path",
        "fullTextArtifactReference",
        "artifact_reference",
        "text_path",
    )
    acquisition_ref = first_nonempty(
        row,
        "acquisition_receipt_ref",
        "retrieval_reference",
        "retrievalReference",
    )

    missing = [
        name
        for name, value in (
            ("source identity", source_ref),
            ("source revision", revision_ref),
            ("content digest", digest_raw),
        )
        if not value
    ]
    if missing:
        raise ValueError(f"input row {line_no}: missing {', '.join(missing)}")

    digest_ref = normalize_digest(digest_raw)

    # Fail closed if the Digital-ESD producer itself claims promotion.
    for field in (
        "creates_semantic_authority",
        "applicability_promoted",
        "claim_truth_promoted",
        "creates_source_audit_admission",
    ):
        if row.get(field) is True:
            raise ValueError(
                f"input row {line_no}: promoted field {field}=true is not admissible"
            )

    if row.get("candidate_only") is False:
        raise ValueError(
            f"input row {line_no}: candidate_only=false is not admissible"
        )

    request_basis = {
        "source_identity_reference": source_ref,
        "source_revision_ref": revision_ref,
        "content_digest_ref": digest_ref,
        "artifact_reference": artifact_ref,
        "acquisition_receipt_ref": acquisition_ref,
    }
    request_ref = "digital-esd-slr-request:" + sha256_bytes(
        canonical_json_bytes(request_basis)
    )

    return {
        "schema": "digital-esd-slr-interop-request-v1",
        "request_reference": request_ref,
        **request_basis,
        "candidate_only": True,
        "creates_semantic_authority": False,
        "applicability_promoted": False,
        "claim_truth_promoted": False,
        "creates_source_audit_admission": False,
    }


def normalize_cache_row(row: dict[str, Any], line_no: int, verify_files: bool) -> dict[str, Any]:
    source_ref = first_nonempty(row, "source_identity_reference")
    revision_ref = first_nonempty(row, "source_revision_reference", "source_revision_ref")
    digest_raw = first_nonempty(row, "artifact_sha256", "content_digest_ref", "sha256")
    artifact_ref = first_nonempty(row, "artifact_reference", "artifact_path", "text_path")

    missing = [
        name
        for name, value in (
            ("source identity", source_ref),
            ("source revision", revision_ref),
            ("artifact digest", digest_raw),
            ("artifact reference", artifact_ref),
        )
        if not value
    ]
    if missing:
        raise ValueError(f"cache row {line_no}: missing {', '.join(missing)}")

    state = str(row.get("cache_state") or "")
    if state not in {"materialised", "parsedOrReconciled", "evictable"}:
        raise ValueError(
            f"cache row {line_no}: cache_state={state!r} is not a materialised artifact"
        )

    digest_ref = normalize_digest(digest_raw)
    artifact = Path(artifact_ref)
    if verify_files:
        if not artifact.exists() or not artifact.is_file():
            raise FileNotFoundError(f"{source_ref}: {artifact}")
        observed = "sha256:" + sha256_file(artifact)
        if observed != digest_ref:
            raise RuntimeError(
                f"{source_ref}: cache/file digest mismatch expected={digest_ref} observed={observed}"
            )

    request_basis = {
        "source_identity_reference": source_ref,
        "source_revision_ref": revision_ref,
        "content_digest_ref": digest_ref,
        "artifact_reference": str(artifact),
        "artifact_path": str(artifact),
        "content_sha256": digest_ref.removeprefix("sha256:"),
        "acquisition_receipt_ref": first_nonempty(
            row, "retrieval_reference", "materialised_from_plan_reference"
        ),
        "cache_state": state,
    }
    request_ref = "digital-esd-slr-request:" + sha256_bytes(
        canonical_json_bytes(request_basis)
    )
    return {
        "schema": "digital-esd-slr-interop-request-v1",
        "request_reference": request_ref,
        **request_basis,
        "candidate_only": True,
        "creates_semantic_authority": False,
        "applicability_promoted": False,
        "claim_truth_promoted": False,
        "creates_source_audit_admission": False,
        "cache_registration_counts_as_parse": False,
    }


def cmd_prepare_cache(args: argparse.Namespace) -> int:
    rows = read_jsonl(args.cache_ledger)
    normalized = [
        normalize_cache_row(row, i, args.verify_files)
        for i, row in enumerate(rows, start=1)
        if str(row.get("cache_state") or "") in {"materialised", "parsedOrReconciled", "evictable"}
    ]

    seen: set[tuple[str, str]] = set()
    for row in normalized:
        key = (
            row["source_identity_reference"],
            row["source_revision_ref"],
        )
        if key in seen:
            raise ValueError(
                "duplicate source/revision pair in cache handoff: "
                f"{key[0]} @ {key[1]}"
            )
        seen.add(key)

    write_jsonl(args.output, normalized)
    manifest = {
        "schema": "digital-esd-slr-cache-handoff-manifest-v1",
        "wrapper_version": WRAPPER_VERSION,
        "cache_ledger_reference": str(args.cache_ledger),
        "cache_ledger_sha256": sha256_file(args.cache_ledger),
        "interop_input_reference": str(args.output),
        "interop_input_sha256": sha256_file(args.output),
        "record_count": len(normalized),
        "files_reverified": bool(args.verify_files),
        "cache_registration_counts_as_parse": False,
        "candidate_only": True,
        "creates_semantic_authority": False,
        "creates_source_audit_admission": False,
    }
    manifest_path = args.manifest or args.output.with_suffix(".manifest.json")
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


def cmd_prepare(args: argparse.Namespace) -> int:
    rows = read_jsonl(args.input)
    normalized = [
        normalize_input_row(row, i)
        for i, row in enumerate(rows, start=1)
    ]

    seen: set[tuple[str, str]] = set()
    for row in normalized:
        key = (
            row["source_identity_reference"],
            row["source_revision_ref"],
        )
        if key in seen:
            raise ValueError(
                "duplicate source/revision pair in interop input: "
                f"{key[0]} @ {key[1]}"
            )
        seen.add(key)

    write_jsonl(args.output, normalized)
    manifest = {
        "schema": "digital-esd-slr-interop-input-manifest-v1",
        "wrapper_version": WRAPPER_VERSION,
        "source_input_reference": str(args.input),
        "source_input_sha256": sha256_file(args.input),
        "interop_input_reference": str(args.output),
        "interop_input_sha256": sha256_file(args.output),
        "record_count": len(normalized),
        "candidate_only": True,
        "creates_semantic_authority": False,
        "applicability_promoted": False,
        "claim_truth_promoted": False,
        "creates_source_audit_admission": False,
    }
    manifest_path = args.manifest or args.output.with_suffix(".manifest.json")
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


def load_config(path: Path) -> dict[str, Any]:
    cfg = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(cfg, dict):
        raise ValueError("interop config must be a JSON object")
    argv = cfg.get("command")
    if not isinstance(argv, list) or not argv or not all(
        isinstance(x, str) and x for x in argv
    ):
        raise ValueError("config.command must be a non-empty string array")
    return cfg


def cmd_run(args: argparse.Namespace) -> int:
    cfg = load_config(args.config)
    args.output_dir.mkdir(parents=True, exist_ok=True)

    substitutions = {
        "{input}": str(args.input.resolve()),
        "{output_dir}": str(args.output_dir.resolve()),
    }
    argv: list[str] = []
    for token in cfg["command"]:
        for needle, value in substitutions.items():
            token = token.replace(needle, value)
        argv.append(token)

    env = os.environ.copy()
    extra_env = cfg.get("environment", {})
    if extra_env:
        if not isinstance(extra_env, dict):
            raise ValueError("config.environment must be an object")
        env.update({str(k): str(v) for k, v in extra_env.items()})

    invocation = {
        "schema": "digital-esd-slr-process-invocation-v1",
        "wrapper_version": WRAPPER_VERSION,
        "input_reference": str(args.input),
        "input_sha256": sha256_file(args.input),
        "external_tool_reference": str(
            cfg.get("tool_reference") or argv[0]
        ),
        "external_tool_revision_reference": str(
            cfg.get("tool_revision_reference") or "unrecorded"
        ),
        "argv": argv,
        "process_exit_creates_evidence_payment": False,
    }

    invocation_path = args.output_dir / "interop-invocation.json"
    invocation_path.write_text(
        json.dumps(invocation, indent=2, ensure_ascii=False, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )

    completed = subprocess.run(
        argv,
        cwd=str(args.cwd.resolve()) if args.cwd else None,
        env=env,
        check=False,
    )
    result = {
        **invocation,
        "exit_code": completed.returncode,
        "successful_process_exit_creates_evidence_payment": False,
    }
    (args.output_dir / "interop-process-result.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    if completed.returncode != 0:
        raise SystemExit(completed.returncode)
    return 0


def normalize_scholarly_output_row(
    row: dict[str, Any],
    line_no: int,
    request: dict[str, Any],
) -> dict[str, Any]:
    source_ref = first_nonempty(row, "source_identity_reference")
    revision_ref = first_nonempty(row, "source_revision_reference", "source_revision_ref")
    digest_raw = first_nonempty(row, "content_sha256", "content_digest_ref", "sha256")

    if not source_ref or not revision_ref or not digest_raw:
        raise ValueError(
            f"scholarly output row {line_no}: missing source identity/revision/digest"
        )
    if source_ref != str(request["source_identity_reference"]):
        raise ValueError(
            f"scholarly output row {line_no}: source identity mismatch"
        )
    if revision_ref != str(request["source_revision_ref"]):
        raise ValueError(
            f"scholarly output row {line_no}: source revision mismatch"
        )

    digest_ref = normalize_digest(digest_raw)
    if digest_ref != normalize_digest(str(request["content_digest_ref"])):
        raise ValueError(
            f"scholarly output row {line_no}: content digest mismatch"
        )
    if row.get("parser_success") is not True:
        raise ValueError(
            f"scholarly output row {line_no}: parser_success must be true"
        )
    if row.get("candidate_only") is not True:
        raise ValueError(
            f"scholarly output row {line_no}: candidate_only must be true"
        )
    if row.get("creates_study_truth") is not False:
        raise ValueError(
            f"scholarly output row {line_no}: creates_study_truth must be false"
        )
    if row.get("creates_source_audit_admission") is not False:
        raise ValueError(
            f"scholarly output row {line_no}: creates_source_audit_admission must be false"
        )

    document_nodes = row.get("document_nodes", [])
    study_facets = row.get("study_facets", [])
    if not isinstance(document_nodes, list) or not isinstance(study_facets, list):
        raise ValueError(
            f"scholarly output row {line_no}: document_nodes/study_facets must be lists"
        )

    node_ids = {
        str(node.get("node_id") or "")
        for node in document_nodes
        if isinstance(node, dict)
    }
    if "" in node_ids:
        raise ValueError(
            f"scholarly output row {line_no}: document node missing node_id"
        )

    for facet in study_facets:
        if not isinstance(facet, dict):
            raise ValueError(
                f"scholarly output row {line_no}: study facet must be an object"
            )
        if facet.get("candidate_only") is not True:
            raise ValueError(
                f"scholarly output row {line_no}: study facet must remain candidate-only"
            )
        if facet.get("creates_study_truth") is not False:
            raise ValueError(
                f"scholarly output row {line_no}: study facet may not create study truth"
            )
        if facet.get("creates_source_audit_admission") is not False:
            raise ValueError(
                f"scholarly output row {line_no}: study facet may not create admission"
            )

    bundle_basis = {
        "source_identity_reference": source_ref,
        "source_revision_ref": revision_ref,
        "content_digest_ref": digest_ref,
        "document_node_ids": sorted(node_ids),
        "study_facets": [
            {
                "facet_role": facet.get("facet_role"),
                "evidence_refs": facet.get("evidence_refs", []),
                "matched_terms": facet.get("matched_terms"),
            }
            for facet in study_facets
            if isinstance(facet, dict)
        ],
    }
    parse_bundle_ref = "digital-esd-scholarly-parse:" + sha256_bytes(
        canonical_json_bytes(bundle_basis)
    )

    return {
        "schema": "digital-esd-scholarly-parse-receipt-v1",
        "source_identity_reference": source_ref,
        "source_revision_ref": revision_ref,
        "content_digest_ref": digest_ref,
        "parse_bundle_reference": parse_bundle_ref,
        "format_type": row.get("format_type"),
        "document_node_count": len(document_nodes),
        "study_facet_count": len(study_facets),
        "candidate_only": True,
        "creates_semantic_authority": False,
        "applicability_promoted": False,
        "claim_truth_promoted": False,
        "creates_study_truth": False,
        "creates_reviewed_canonical_evidence": False,
        "creates_source_audit_admission": False,
    }


def cmd_verify_scholarly(args: argparse.Namespace) -> int:
    request_rows = read_jsonl(args.input)
    parser_rows = read_jsonl(args.parser_output)

    expected = {
        (
            str(row["source_identity_reference"]),
            str(row["source_revision_ref"]),
        ): row
        for row in request_rows
    }

    receipts: list[dict[str, Any]] = []
    observed: set[tuple[str, str]] = set()
    failures: list[str] = []

    for line_no, row in enumerate(parser_rows, start=1):
        key = (
            first_nonempty(row, "source_identity_reference"),
            first_nonempty(row, "source_revision_reference", "source_revision_ref"),
        )
        request = expected.get(key)
        if request is None:
            failures.append(
                f"parser output has no exact prepared request: {key[0]} @ {key[1]}"
            )
            continue
        if key in observed:
            failures.append(
                f"duplicate scholarly parser bundle: {key[0]} @ {key[1]}"
            )
            continue
        try:
            receipts.append(
                normalize_scholarly_output_row(row, line_no, request)
            )
        except (ValueError, TypeError) as exc:
            failures.append(str(exc))
            continue
        observed.add(key)

    for key in sorted(set(expected) - observed):
        failures.append(
            f"missing scholarly parser bundle for {key[0]} @ {key[1]}"
        )

    if failures:
        raise RuntimeError(
            "scholarly parser reconciliation failed:\n- "
            + "\n- ".join(failures[:50])
        )

    write_jsonl(args.output, receipts)
    manifest = {
        "schema": "digital-esd-scholarly-parse-manifest-v1",
        "wrapper_version": WRAPPER_VERSION,
        "request_reference": str(args.input),
        "request_sha256": sha256_file(args.input),
        "parser_output_reference": str(args.parser_output),
        "parser_output_sha256": sha256_file(args.parser_output),
        "parse_receipt_reference": str(args.output),
        "parse_receipt_sha256": sha256_file(args.output),
        "request_count": len(request_rows),
        "parsed_count": len(receipts),
        "same_object_reconciled": True,
        "parser_success_is_review_payment": False,
        "creates_reviewed_canonical_evidence": False,
        "creates_source_audit_admission": False,
    }
    manifest_path = args.manifest or args.output.with_suffix(".manifest.json")
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


def cmd_run_scholarly(args: argparse.Namespace) -> int:
    args.output_dir.mkdir(parents=True, exist_ok=True)

    requests = args.output_dir / "requests.jsonl"
    prepare_args = type("PrepareCacheArgs", (), {
        "cache_ledger": args.cache_ledger,
        "output": requests,
        "manifest": args.output_dir / "requests.manifest.json",
        "verify_files": True,
    })()
    cmd_prepare_cache(prepare_args)

    parser_script = (
        args.slr_root
        / "interop_scripts"
        / "digital_esd"
        / "scholarly_parser_prototype.py"
    )
    if not parser_script.exists():
        raise FileNotFoundError(
            f"SLR scholarly parser not found at {parser_script}"
        )

    parser_config = args.parser_config
    if parser_config is None:
        parser_config = (
            args.slr_root
            / "interop_scripts"
            / "digital_esd"
            / "scholarly_fulltext.prototype.json"
        )
    if not parser_config.exists():
        raise FileNotFoundError(
            f"SLR scholarly parser config not found at {parser_config}"
        )

    parser_output = args.output_dir / "parser-output.jsonl"
    argv = [
        sys.executable,
        str(parser_script),
        "--input",
        str(requests),
        "--config",
        str(parser_config),
        "--output",
        str(parser_output),
    ]

    invocation = {
        "schema": "digital-esd-scholarly-parser-invocation-v1",
        "wrapper_version": WRAPPER_VERSION,
        "slr_root": str(args.slr_root),
        "slr_revision_reference": args.slr_revision_reference,
        "parser_script": str(parser_script),
        "parser_config": str(parser_config),
        "request_sha256": sha256_file(requests),
        "argv": argv,
        "process_exit_creates_evidence_payment": False,
    }
    (args.output_dir / "scholarly-parser-invocation.json").write_text(
        json.dumps(invocation, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    completed = subprocess.run(
        argv,
        cwd=str(args.slr_root),
        check=False,
    )
    if completed.returncode != 0:
        raise SystemExit(completed.returncode)

    receipts = args.output_dir / "parse-receipts.jsonl"
    verify_args = type("VerifyScholarlyArgs", (), {
        "input": requests,
        "parser_output": parser_output,
        "output": receipts,
        "manifest": args.output_dir / "parse-receipts.manifest.json",
    })()
    return cmd_verify_scholarly(verify_args)


def normalize_output_row(row: dict[str, Any], line_no: int) -> dict[str, Any]:
    required = (
        "source_identity_reference",
        "source_revision_ref",
        "content_digest_ref",
        "observation_ref",
    )
    missing = [
        key
        for key in required
        if not isinstance(row.get(key), str) or not row[key].strip()
    ]
    if missing:
        raise ValueError(
            f"output row {line_no}: missing canonical fields {missing}"
        )

    if row.get("candidate_only") is not True:
        raise ValueError(
            f"output row {line_no}: candidate_only must be true"
        )
    for field in (
        "creates_semantic_authority",
        "applicability_promoted",
        "claim_truth_promoted",
    ):
        if row.get(field) is not False:
            raise ValueError(
                f"output row {line_no}: {field} must be false"
            )

    out = dict(row)
    out["content_digest_ref"] = normalize_digest(
        str(row["content_digest_ref"])
    )
    return out


def cmd_verify(args: argparse.Namespace) -> int:
    request_rows = read_jsonl(args.input)
    output_rows_raw = read_jsonl(args.receipts)
    output_rows = [
        normalize_output_row(row, i)
        for i, row in enumerate(output_rows_raw, start=1)
    ]

    expected: dict[tuple[str, str], dict[str, Any]] = {}
    for row in request_rows:
        key = (
            str(row["source_identity_reference"]),
            str(row["source_revision_ref"]),
        )
        expected[key] = row

    observed: dict[tuple[str, str], dict[str, Any]] = {}
    failures: list[str] = []
    for row in output_rows:
        key = (
            str(row["source_identity_reference"]),
            str(row["source_revision_ref"]),
        )
        if key in observed:
            failures.append(
                f"duplicate SLR receipt for {key[0]} @ {key[1]}"
            )
            continue
        observed[key] = row

        request = expected.get(key)
        if request is None:
            failures.append(
                "SLR receipt has no Digital-ESD request: "
                f"{key[0]} @ {key[1]}"
            )
            continue
        if normalize_digest(str(request["content_digest_ref"])) != str(
            row["content_digest_ref"]
        ):
            failures.append(
                f"digest mismatch for {key[0]} @ {key[1]}"
            )

    missing = sorted(set(expected) - set(observed))
    for source_ref, revision_ref in missing:
        failures.append(
            f"missing SLR receipt for {source_ref} @ {revision_ref}"
        )

    if failures:
        raise RuntimeError(
            "SLR interop reconciliation failed:\n- "
            + "\n- ".join(failures[:50])
        )

    receipt_basis = {
        "input_reference": str(args.input),
        "input_sha256": sha256_file(args.input),
        "output_reference": str(args.receipts),
        "output_sha256": sha256_file(args.receipts),
        "record_count": len(output_rows),
    }
    receipt = {
        "schema": "digital-esd-slr-interop-invocation-receipt-v1",
        "wrapper_version": WRAPPER_VERSION,
        **receipt_basis,
        "invocation_reference": "digital-esd-slr-interop:"
        + sha256_bytes(canonical_json_bytes(receipt_basis)),
        "source_identity_reconciled": True,
        "source_revision_reconciled": True,
        "content_digest_reconciled": True,
        "candidate_only_verified": True,
        "creates_semantic_authority": False,
        "applicability_promoted": False,
        "claim_truth_promoted": False,
        "creates_source_audit_admission": False,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False, sort_keys=True)
        + "\n",
        encoding="utf-8",
    )
    print(json.dumps(receipt, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command_name", required=True)

    prepare = sub.add_parser("prepare")
    prepare.add_argument("--input", required=True, type=Path)
    prepare.add_argument("--output", required=True, type=Path)
    prepare.add_argument("--manifest", type=Path)
    prepare.set_defaults(func=cmd_prepare)

    run = sub.add_parser("run")
    run.add_argument("--input", required=True, type=Path)
    run.add_argument("--config", required=True, type=Path)
    run.add_argument("--output-dir", required=True, type=Path)
    run.add_argument("--cwd", type=Path)
    run.set_defaults(func=cmd_run)

    prepare_cache = sub.add_parser("prepare-cache")
    prepare_cache.add_argument("--cache-ledger", required=True, type=Path)
    prepare_cache.add_argument("--output", required=True, type=Path)
    prepare_cache.add_argument("--manifest", type=Path)
    prepare_cache.add_argument("--verify-files", action="store_true")
    prepare_cache.set_defaults(func=cmd_prepare_cache)

    run_scholarly = sub.add_parser("run-scholarly")
    run_scholarly.add_argument("--cache-ledger", required=True, type=Path)
    run_scholarly.add_argument("--slr-root", required=True, type=Path)
    run_scholarly.add_argument("--slr-revision-reference", required=True)
    run_scholarly.add_argument("--parser-config", type=Path)
    run_scholarly.add_argument("--output-dir", required=True, type=Path)
    run_scholarly.set_defaults(func=cmd_run_scholarly)

    verify_scholarly = sub.add_parser("verify-scholarly")
    verify_scholarly.add_argument("--input", required=True, type=Path)
    verify_scholarly.add_argument("--parser-output", required=True, type=Path)
    verify_scholarly.add_argument("--output", required=True, type=Path)
    verify_scholarly.add_argument("--manifest", type=Path)
    verify_scholarly.set_defaults(func=cmd_verify_scholarly)

    verify = sub.add_parser("verify")
    verify.add_argument("--input", required=True, type=Path)
    verify.add_argument("--receipts", required=True, type=Path)
    verify.add_argument("--output", required=True, type=Path)
    verify.set_defaults(func=cmd_verify)

    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())

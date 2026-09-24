#!/usr/bin/env python3
"""Thin Digital-ESD scholarly full-text parser interop.

Reference contract:
  DASHI.Interop.DigitalESD.ScholarlyFullTextCrossPollinationExact

This wrapper does NOT implement PDF/HTML parsing, study semantics, review,
truth, or SourceAuditAdmission.

It owns only:
  * exact full-text artifact/revision/digest request preparation;
  * invocation of a configured external scholarly parser capability;
  * reconciliation of returned document nodes and generic study-facet
    candidates against the exact source revision;
  * verification that returned EvidenceObservation-shaped candidates remain
    candidate-only and non-promoting.

Normalized parser output is one JSON object per source revision:

{
  "source_identity_reference": "ERIC:EJ...",
  "source_revision_ref": "fulltext-sha256:...",
  "content_digest_ref": "sha256:...",
  "document_nodes": [
    {
      "node_reference": "node:...",
      "node_kind": "section|heading|paragraph|sentence|table|table_cell|figure|figure_caption|reference_entry|appendix|other",
      "span": {
        "span_ref": "span:...",
        "source_revision_ref": "fulltext-sha256:...",
        "kind": "text_range|structured_coordinate|whole_revision",
        "start": 10,
        "end": 42,
        "coordinate": "table:1:row:2:cell:3"
      },
      "parser_or_layout_receipt_reference": "..."
    }
  ],
  "study_facets": [
    {
      "facet_reference": "facet:...",
      "facet_kind": "population|sample|intervention|comparator|outcome|study_design|setting|time_period|method|limitation|funding|institution|participant_group|measurement|study|other",
      "node_reference": "node:...",
      "observation": {
        "observation_ref": "observation:...",
        "source_revision_ref": "fulltext-sha256:...",
        "span_ref": "span:...",
        "predicate_ref": "...",
        "value_ref": "...",
        "candidate_only": true,
        "creates_semantic_authority": false,
        "applicability_promoted": false,
        "claim_truth_promoted": false
      },
      "parser_or_model_receipt_reference": "...",
      "ontology_candidate_reference": "..."
    }
  ],
  "candidate_only": true,
  "creates_source_audit_admission": false
}

A parser process exiting successfully is not a review/payment receipt.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
from typing import Any


WRAPPER_VERSION = "digital-esd-scholarly-fulltext-interop-v1"
AGDA_CONTRACT = (
    "DASHI.Interop.DigitalESD."
    "ScholarlyFullTextCrossPollinationExact"
)

NODE_KINDS = {
    "section",
    "heading",
    "paragraph",
    "sentence",
    "table",
    "table_cell",
    "figure",
    "figure_caption",
    "reference_entry",
    "appendix",
    "other",
}

FACET_KINDS = {
    "study",
    "population",
    "sample",
    "intervention",
    "comparator",
    "outcome",
    "study_design",
    "setting",
    "time_period",
    "method",
    "limitation",
    "funding",
    "institution",
    "participant_group",
    "measurement",
    "other",
}

SPAN_KINDS = {"text_range", "structured_coordinate", "whole_revision"}


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
            handle.write(json.dumps(row, ensure_ascii=False, sort_keys=True) + "\n")


def nonempty(row: dict[str, Any], *keys: str) -> str:
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
        raise ValueError(f"expected 64-hex SHA-256 digest, got {value!r}")
    int(value, 16)
    return "sha256:" + value


def prepare_row(row: dict[str, Any], line_no: int, verify_files: bool) -> dict[str, Any]:
    source_ref = nonempty(
        row,
        "source_identity_reference",
        "source_ref",
        "attributed_source_reference",
    )
    revision_ref = nonempty(
        row,
        "source_revision_ref",
        "source_revision_reference",
        "fullTextRevisionReference",
        "revision_ref",
    )
    digest_raw = nonempty(
        row,
        "content_digest_ref",
        "artifact_sha256",
        "sha256",
        "fullTextArtifactSha256",
    )
    artifact_ref = nonempty(
        row,
        "artifact_reference",
        "artifact_path",
        "fullTextArtifactReference",
        "text_path",
    )
    acquisition_ref = nonempty(
        row,
        "acquisition_receipt_ref",
        "retrieval_reference",
        "retrievalReference",
        "materialisedFromPlanReference",
    )

    missing = [
        label
        for label, value in (
            ("source identity", source_ref),
            ("source revision", revision_ref),
            ("content digest", digest_raw),
            ("artifact reference", artifact_ref),
        )
        if not value
    ]
    if missing:
        raise ValueError(f"input row {line_no}: missing {', '.join(missing)}")

    digest_ref = normalize_digest(digest_raw)
    artifact_path = Path(artifact_ref)

    if verify_files:
        if not artifact_path.exists():
            raise FileNotFoundError(f"input row {line_no}: {artifact_path}")
        observed = "sha256:" + sha256_file(artifact_path)
        if observed != digest_ref:
            raise ValueError(
                f"input row {line_no}: artifact digest drift "
                f"expected={digest_ref} observed={observed}"
            )

    for field in (
        "creates_source_truth",
        "creates_semantic_authority",
        "applicability_promoted",
        "claim_truth_promoted",
        "creates_source_audit_admission",
    ):
        if row.get(field) is True:
            raise ValueError(
                f"input row {line_no}: promoted input {field}=true is inadmissible"
            )

    basis = {
        "source_identity_reference": source_ref,
        "source_revision_ref": revision_ref,
        "content_digest_ref": digest_ref,
        "artifact_reference": artifact_ref,
        "acquisition_receipt_ref": acquisition_ref,
    }
    return {
        "schema": "digital-esd-scholarly-parser-request-v1",
        "request_reference": "scholarly-parser-request:"
        + sha256_bytes(canonical_json_bytes(basis)),
        "agda_contract_reference": AGDA_CONTRACT,
        **basis,
        "requested_outputs": [
            "document_structure",
            "generic_scholarly_study_facets",
            "canonical_evidence_observations",
        ],
        "candidate_only": True,
        "parser_creates_review_payment": False,
        "parser_creates_source_truth": False,
        "parser_creates_source_audit_admission": False,
    }


def cmd_prepare(args: argparse.Namespace) -> int:
    rows = read_jsonl(args.input)
    prepared = [
        prepare_row(row, i, args.verify_files)
        for i, row in enumerate(rows, start=1)
    ]
    seen: set[tuple[str, str]] = set()
    for row in prepared:
        key = (row["source_identity_reference"], row["source_revision_ref"])
        if key in seen:
            raise ValueError(
                "duplicate source/revision in scholarly parser request: "
                f"{key[0]} @ {key[1]}"
            )
        seen.add(key)

    write_jsonl(args.output, prepared)
    manifest = {
        "schema": "digital-esd-scholarly-parser-request-manifest-v1",
        "wrapper_version": WRAPPER_VERSION,
        "agda_contract_reference": AGDA_CONTRACT,
        "input_reference": str(args.input),
        "input_sha256": sha256_file(args.input),
        "request_reference": str(args.output),
        "request_sha256": sha256_file(args.output),
        "request_count": len(prepared),
        "parser_semantics_owned_by_wrapper": False,
        "candidate_only": True,
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
        raise ValueError("parser config must be a JSON object")
    command = cfg.get("command")
    if not isinstance(command, list) or not command or not all(
        isinstance(x, str) and x for x in command
    ):
        raise ValueError("config.command must be a non-empty string array")
    return cfg


def cmd_run(args: argparse.Namespace) -> int:
    cfg = load_config(args.config)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    argv: list[str] = []
    for token in cfg["command"]:
        token = token.replace("{input}", str(args.input.resolve()))
        token = token.replace("{output_dir}", str(args.output_dir.resolve()))
        argv.append(token)

    env = os.environ.copy()
    extra_env = cfg.get("environment", {})
    if not isinstance(extra_env, dict):
        raise ValueError("config.environment must be an object")
    env.update({str(k): str(v) for k, v in extra_env.items()})

    invocation = {
        "schema": "digital-esd-scholarly-parser-invocation-v1",
        "wrapper_version": WRAPPER_VERSION,
        "agda_contract_reference": AGDA_CONTRACT,
        "input_reference": str(args.input),
        "input_sha256": sha256_file(args.input),
        "external_tool_reference": str(cfg.get("tool_reference") or argv[0]),
        "external_tool_revision_reference": str(
            cfg.get("tool_revision_reference") or "unrecorded"
        ),
        "argv": argv,
        "process_exit_creates_review_payment": False,
        "process_exit_creates_source_truth": False,
    }
    invocation_path = args.output_dir / "invocation.json"
    invocation_path.write_text(
        json.dumps(invocation, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    completed = subprocess.run(argv, env=env, cwd=cfg.get("cwd") or None)
    result = {
        **invocation,
        "exit_code": completed.returncode,
        "successful_exit_is_evidence_payment": False,
    }
    (args.output_dir / "process-result.json").write_text(
        json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return completed.returncode


def validate_span(span: dict[str, Any], revision_ref: str, context: str) -> str:
    span_ref = nonempty(span, "span_ref")
    span_revision = nonempty(span, "source_revision_ref")
    kind = nonempty(span, "kind")

    if not span_ref:
        raise ValueError(f"{context}: missing span_ref")
    if span_revision != revision_ref:
        raise ValueError(
            f"{context}: span revision drift expected={revision_ref} "
            f"observed={span_revision!r}"
        )
    if kind not in SPAN_KINDS:
        raise ValueError(f"{context}: unsupported span kind {kind!r}")

    if kind == "text_range":
        start = span.get("start")
        end = span.get("end")
        if not isinstance(start, int) or not isinstance(end, int):
            raise ValueError(f"{context}: text_range requires integer start/end")
        if start < 0 or end < start:
            raise ValueError(f"{context}: invalid text range [{start}, {end})")
    elif kind == "structured_coordinate":
        if not nonempty(span, "coordinate"):
            raise ValueError(
                f"{context}: structured_coordinate requires coordinate"
            )

    return span_ref


def ensure_candidate_flags(row: dict[str, Any], context: str) -> None:
    if row.get("candidate_only") is not True:
        raise ValueError(f"{context}: candidate_only must be true")
    for field in (
        "creates_semantic_authority",
        "applicability_promoted",
        "claim_truth_promoted",
        "creates_source_audit_admission",
    ):
        if row.get(field) is True:
            raise ValueError(f"{context}: promoted field {field}=true")


def validate_parser_bundle(
    bundle: dict[str, Any],
    request: dict[str, Any],
    line_no: int,
) -> dict[str, Any]:
    context = f"parser output row {line_no}"
    source_ref = nonempty(bundle, "source_identity_reference")
    revision_ref = nonempty(bundle, "source_revision_ref")
    digest_ref = normalize_digest(nonempty(bundle, "content_digest_ref"))

    if source_ref != request["source_identity_reference"]:
        raise ValueError(f"{context}: source identity drift")
    if revision_ref != request["source_revision_ref"]:
        raise ValueError(f"{context}: source revision drift")
    if digest_ref != request["content_digest_ref"]:
        raise ValueError(f"{context}: content digest drift")

    ensure_candidate_flags(bundle, context)
    if bundle.get("reviewed") is True:
        raise ValueError(f"{context}: parser output may not claim reviewed=true")

    document_nodes = bundle.get("document_nodes")
    study_facets = bundle.get("study_facets")
    if not isinstance(document_nodes, list):
        raise ValueError(f"{context}: document_nodes must be an array")
    if not isinstance(study_facets, list):
        raise ValueError(f"{context}: study_facets must be an array")

    node_spans: dict[str, str] = {}
    normalized_nodes: list[dict[str, Any]] = []
    for index, node in enumerate(document_nodes):
        if not isinstance(node, dict):
            raise ValueError(f"{context}: document node {index} must be object")
        node_ref = nonempty(node, "node_reference")
        node_kind = nonempty(node, "node_kind")
        if not node_ref:
            raise ValueError(f"{context}: node {index} missing node_reference")
        if node_ref in node_spans:
            raise ValueError(f"{context}: duplicate node_reference {node_ref}")
        if node_kind not in NODE_KINDS:
            raise ValueError(
                f"{context}: node {node_ref} unsupported kind {node_kind!r}"
            )
        span = node.get("span")
        if not isinstance(span, dict):
            raise ValueError(f"{context}: node {node_ref} missing span object")
        span_ref = validate_span(span, revision_ref, f"{context} node {node_ref}")
        if not nonempty(node, "parser_or_layout_receipt_reference"):
            raise ValueError(
                f"{context}: node {node_ref} missing parser/layout receipt"
            )
        node_spans[node_ref] = span_ref
        normalized_nodes.append(node)

    seen_facets: set[str] = set()
    seen_observations: set[str] = set()
    normalized_facets: list[dict[str, Any]] = []
    for index, facet in enumerate(study_facets):
        if not isinstance(facet, dict):
            raise ValueError(f"{context}: study facet {index} must be object")
        facet_ref = nonempty(facet, "facet_reference")
        facet_kind = nonempty(facet, "facet_kind")
        node_ref = nonempty(facet, "node_reference")
        if not facet_ref or facet_ref in seen_facets:
            raise ValueError(
                f"{context}: missing/duplicate facet_reference {facet_ref!r}"
            )
        if facet_kind not in FACET_KINDS:
            raise ValueError(
                f"{context}: facet {facet_ref} unsupported kind {facet_kind!r}"
            )
        if node_ref not in node_spans:
            raise ValueError(
                f"{context}: facet {facet_ref} references unknown node {node_ref!r}"
            )
        if not nonempty(facet, "parser_or_model_receipt_reference"):
            raise ValueError(
                f"{context}: facet {facet_ref} missing parser/model receipt"
            )
        if not nonempty(facet, "ontology_candidate_reference"):
            raise ValueError(
                f"{context}: facet {facet_ref} missing ontology candidate ref"
            )

        obs = facet.get("observation")
        if not isinstance(obs, dict):
            raise ValueError(f"{context}: facet {facet_ref} missing observation")
        obs_ref = nonempty(obs, "observation_ref")
        if not obs_ref or obs_ref in seen_observations:
            raise ValueError(
                f"{context}: missing/duplicate observation_ref {obs_ref!r}"
            )
        if nonempty(obs, "source_revision_ref") != revision_ref:
            raise ValueError(
                f"{context}: observation {obs_ref} revision drift"
            )
        if nonempty(obs, "span_ref") != node_spans[node_ref]:
            raise ValueError(
                f"{context}: observation {obs_ref} does not use node anchor"
            )
        if not nonempty(obs, "predicate_ref"):
            raise ValueError(f"{context}: observation {obs_ref} missing predicate")
        if not nonempty(obs, "value_ref"):
            raise ValueError(f"{context}: observation {obs_ref} missing value")
        ensure_candidate_flags(obs, f"{context} observation {obs_ref}")

        seen_facets.add(facet_ref)
        seen_observations.add(obs_ref)
        normalized_facets.append(facet)

    verified_basis = {
        "source_identity_reference": source_ref,
        "source_revision_ref": revision_ref,
        "content_digest_ref": digest_ref,
        "document_node_count": len(normalized_nodes),
        "study_facet_count": len(normalized_facets),
        "observation_refs": sorted(seen_observations),
    }
    return {
        "schema": "digital-esd-verified-scholarly-parser-bundle-v1",
        **verified_basis,
        "request_reference": request["request_reference"],
        "verified_bundle_reference": "verified-scholarly-parser-bundle:"
        + sha256_bytes(canonical_json_bytes(verified_basis)),
        "document_nodes": normalized_nodes,
        "study_facets": normalized_facets,
        "candidate_only": True,
        "reviewed": False,
        "parser_creates_review_payment": False,
        "creates_source_truth": False,
        "creates_source_audit_admission": False,
    }


def cmd_verify(args: argparse.Namespace) -> int:
    requests = read_jsonl(args.requests)
    outputs = read_jsonl(args.parser_output)

    request_by_key = {
        (r["source_identity_reference"], r["source_revision_ref"]): r
        for r in requests
    }
    if len(request_by_key) != len(requests):
        raise ValueError("prepared request contains duplicate source/revision keys")

    verified: list[dict[str, Any]] = []
    seen: set[tuple[str, str]] = set()
    for i, bundle in enumerate(outputs, start=1):
        key = (
            nonempty(bundle, "source_identity_reference"),
            nonempty(bundle, "source_revision_ref"),
        )
        request = request_by_key.get(key)
        if request is None:
            raise ValueError(
                f"parser output row {i}: no corresponding prepared request for {key}"
            )
        if key in seen:
            raise ValueError(f"parser output row {i}: duplicate bundle for {key}")
        seen.add(key)
        verified.append(validate_parser_bundle(bundle, request, i))

    missing = sorted(set(request_by_key) - seen)
    if missing and not args.allow_partial:
        raise ValueError(
            f"parser output missing {len(missing)} prepared requests; "
            "pass --allow-partial only for an explicitly bounded parse tranche"
        )

    write_jsonl(args.output, verified)
    manifest = {
        "schema": "digital-esd-scholarly-parser-verification-manifest-v1",
        "wrapper_version": WRAPPER_VERSION,
        "agda_contract_reference": AGDA_CONTRACT,
        "request_reference": str(args.requests),
        "request_sha256": sha256_file(args.requests),
        "parser_output_reference": str(args.parser_output),
        "parser_output_sha256": sha256_file(args.parser_output),
        "verified_output_reference": str(args.output),
        "verified_output_sha256": sha256_file(args.output),
        "prepared_request_count": len(requests),
        "verified_bundle_count": len(verified),
        "missing_request_count": len(missing),
        "partial_parse_explicitly_allowed": bool(args.allow_partial),
        "document_node_count": sum(len(x["document_nodes"]) for x in verified),
        "study_facet_count": sum(len(x["study_facets"]) for x in verified),
        "parser_output_candidate_only": True,
        "parser_creates_review_payment": False,
        "creates_source_truth": False,
        "creates_source_audit_admission": False,
    }
    manifest_path = args.manifest or args.output.with_suffix(".manifest.json")
    manifest_path.write_text(
        json.dumps(manifest, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    print(json.dumps(manifest, sort_keys=True))
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command_name", required=True)

    prepare = sub.add_parser("prepare")
    prepare.add_argument("--input", required=True, type=Path)
    prepare.add_argument("--output", required=True, type=Path)
    prepare.add_argument("--manifest", type=Path)
    prepare.add_argument("--verify-files", action="store_true")
    prepare.set_defaults(func=cmd_prepare)

    run = sub.add_parser("run")
    run.add_argument("--input", required=True, type=Path)
    run.add_argument("--config", required=True, type=Path)
    run.add_argument("--output-dir", required=True, type=Path)
    run.set_defaults(func=cmd_run)

    verify = sub.add_parser("verify")
    verify.add_argument("--requests", required=True, type=Path)
    verify.add_argument("--parser-output", required=True, type=Path)
    verify.add_argument("--output", required=True, type=Path)
    verify.add_argument("--manifest", type=Path)
    verify.add_argument("--allow-partial", action="store_true")
    verify.set_defaults(func=cmd_verify)

    return parser


def main() -> int:
    args = build_parser().parse_args()
    return int(args.func(args))


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Generate the Sprint133 submission readiness index from Sprint131/132 evidence."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable


AUDIT_ID = "ym_sprint133_submission_readiness_index"
DEFAULT_OUT_DIR = Path("outputs/ym_sprint133_submission_readiness_index")
JSON_NAME = f"{AUDIT_ID}.json"
MD_NAME = f"{AUDIT_ID}.md"

REQUIRED_FILES: dict[str, tuple[Path, ...]] = {
    "sprint131_final_claim": (
        Path("outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit_summary.json"),
        Path("outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit.md"),
    ),
    "sprint131_submission_packet": (
        Path("outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet_summary.json"),
        Path("outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet.md"),
    ),
    "sprint132_submission_bundle": (
        Path("outputs/ym_sprint132_submission_bundle_index/ym_sprint132_submission_bundle_index.json"),
        Path("outputs/ym_sprint132_submission_bundle_index/ym_sprint132_submission_bundle_index.md"),
    ),
    "sprint132_red_team": (
        Path("outputs/ym_sprint132_red_team_audit/ym_sprint132_red_team_audit_summary.json"),
        Path("outputs/ym_sprint132_red_team_audit/red_team_rows.json"),
        Path("outputs/ym_sprint132_red_team_audit/ym_sprint132_red_team_audit.md"),
    ),
}

JSON_REQUIRED = {
    Path("outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit_summary.json"),
    Path("outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet_summary.json"),
    Path("outputs/ym_sprint132_submission_bundle_index/ym_sprint132_submission_bundle_index.json"),
    Path("outputs/ym_sprint132_red_team_audit/ym_sprint132_red_team_audit_summary.json"),
    Path("outputs/ym_sprint132_red_team_audit/red_team_rows.json"),
}

INCOMPLETE_MARKERS: tuple[tuple[str, re.Pattern[str]], ...] = (
    ("postulate", re.compile(r"(?<![A-Za-z0-9_])post" + r"ulate(?![A-Za-z0-9_])")),
    ("todo", re.compile(r"(?<![A-Za-z0-9_])TO" + r"DO(?![A-Za-z0-9_])")),
    ("stub", re.compile(r"(?<![A-Za-z0-9_])st" + r"ub(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("skeleton", re.compile(r"(?<![A-Za-z0-9_])skele" + r"ton(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("dummy", re.compile(r"(?<![A-Za-z0-9_])dum" + r"my(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("future-proof", re.compile(r"future" + r"[\s-]*proof", re.IGNORECASE)),
    ("hole", re.compile(r"(?<![A-Za-z0-9_])ho" + r"le(?![A-Za-z0-9_])", re.IGNORECASE)),
    ("agda-hole-braces", re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}"))),
    ("rhs-meta", re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9']*\s*=\s*\?\s*$")),
)

PROMOTED_TEXT_PATTERNS = (
    re.compile(r"(?m)^\s*clayYangMillsPromoted\s*=\s*true\s*$"),
    re.compile(r'"clayYangMillsPromoted"\s*:\s*true'),
    re.compile(r"\bclayYangMillsPromoted\s*:\s*true\b"),
)
PROMOTION_KEYS = {
    "clayYangMillsPromoted",
    "clay_yang_mills_promoted",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def rel_path(repo_root: Path, path: Path) -> str:
    resolved = path.resolve()
    try:
        return resolved.relative_to(repo_root.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> tuple[Any | None, str | None]:
    try:
        return json.loads(path.read_text(encoding="utf-8")), None
    except FileNotFoundError:
        return None, "missing"
    except json.JSONDecodeError as exc:
        return None, f"invalid JSON: {exc}"


def iter_values(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from iter_values(child)
    elif isinstance(value, list):
        for child in value:
            yield from iter_values(child)


def unique_paths(value: Any) -> list[str]:
    paths: set[str] = set()
    for item in iter_values(value):
        if isinstance(item, dict) and isinstance(item.get("path"), str) and item["path"]:
            paths.add(item["path"])
        elif isinstance(item, str) and (item.startswith("DASHI/") or item.startswith("outputs/")):
            paths.add(item)
    return sorted(paths)


def evidence_rows_from_payload(source: str, payload: Any) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    def row_paths(value: Any) -> list[str]:
        paths = unique_paths(value)
        return paths if paths else [source]

    if isinstance(payload, dict):
        for key in ("internal_gate_rows", "red_team_rows", "internal_required_objection_rows"):
            value = payload.get(key)
            if isinstance(value, list):
                for index, row in enumerate(value, start=1):
                    rows.append({
                        "source": source,
                        "row_type": key,
                        "row_id": row.get("gate") or row.get("row_id") or row.get("objection_id") or str(index)
                        if isinstance(row, dict)
                        else str(index),
                        "evidence_paths": row_paths(row),
                    })
        artifact_map = payload.get("artifact_map")
        if isinstance(artifact_map, list):
            rows.append({
                "source": source,
                "row_type": "artifact_map",
                "row_id": "artifact_map",
                "evidence_paths": row_paths(artifact_map),
            })
        categories = payload.get("categories")
        if isinstance(categories, dict):
            for category, entries in categories.items():
                rows.append({
                    "source": source,
                    "row_type": "bundle_category",
                    "row_id": category,
                    "evidence_paths": row_paths(entries),
                })
    elif isinstance(payload, list):
        for index, row in enumerate(payload, start=1):
            rows.append({
                "source": source,
                "row_type": "red_team_rows_json",
                "row_id": row.get("row_id", str(index)) if isinstance(row, dict) else str(index),
                "evidence_paths": row_paths(row),
            })
    return rows


def promotion_true_hits(source: str, payload: Any) -> list[dict[str, Any]]:
    hits: list[dict[str, Any]] = []
    for item in iter_values(payload):
        if isinstance(item, dict):
            for key, value in item.items():
                if key in PROMOTION_KEYS and value is True:
                    hits.append({"source": source, "surface": "json", "key": key})
    return hits


def text_promotion_hits(repo_root: Path, rel: Path) -> list[dict[str, Any]]:
    path = repo_root / rel
    text = path.read_text(encoding="utf-8", errors="replace")
    hits: list[dict[str, Any]] = []
    for pattern in PROMOTED_TEXT_PATTERNS:
        for match in pattern.finditer(text):
            hits.append({"path": rel.as_posix(), "line": line_for_offset(text, match.start())})
    return hits


def sprint133_marker_hits(repo_root: Path) -> list[dict[str, Any]]:
    closure_dir = repo_root / "DASHI" / "Physics" / "Closure"
    if not closure_dir.is_dir():
        return []
    hits: list[dict[str, Any]] = []
    for path in sorted(closure_dir.glob("YMSprint133*.agda")):
        text = path.read_text(encoding="utf-8", errors="replace")
        rel = rel_path(repo_root, path)
        for marker, pattern in INCOMPLETE_MARKERS:
            for match in pattern.finditer(text):
                hits.append({"path": rel, "line": line_for_offset(text, match.start()), "marker": marker})
    return hits


def sprint133_modules(repo_root: Path) -> list[str]:
    closure_dir = repo_root / "DASHI" / "Physics" / "Closure"
    if not closure_dir.is_dir():
        return []
    return [rel_path(repo_root, path) for path in sorted(closure_dir.glob("YMSprint133*.agda"))]


def build_summary(repo_root: Path) -> dict[str, Any]:
    fail_reasons: list[str] = []
    artifacts: list[dict[str, Any]] = []
    json_payloads: dict[str, Any] = {}

    for category, paths in REQUIRED_FILES.items():
        for rel in paths:
            path = repo_root / rel
            if not path.is_file():
                fail_reasons.append(f"missing required file: {rel.as_posix()}")
                continue
            size = path.stat().st_size
            if size <= 0:
                fail_reasons.append(f"empty required file: {rel.as_posix()}")
                continue
            artifacts.append({
                "category": category,
                "path": rel.as_posix(),
                "size_bytes": size,
                "sha256": sha256_file(path),
            })
            if rel in JSON_REQUIRED:
                payload, error = load_json(path)
                if error is not None:
                    fail_reasons.append(f"unreadable required JSON: {rel.as_posix()}: {error}")
                else:
                    json_payloads[rel.as_posix()] = payload

    sprint133 = sprint133_modules(repo_root)
    for rel in sprint133:
        path = repo_root / rel
        artifacts.append({
            "category": "sprint133_agda_module",
            "path": rel,
            "size_bytes": path.stat().st_size,
            "sha256": sha256_file(path),
        })

    evidence_rows: list[dict[str, Any]] = []
    for source, payload in json_payloads.items():
        evidence_rows.extend(evidence_rows_from_payload(source, payload))
        for hit in promotion_true_hits(source, payload):
            fail_reasons.append(f"clayYangMillsPromoted=true in {hit['source']} ({hit['surface']}:{hit['key']})")

    empty_evidence_rows = [
        f"{row['source']}:{row['row_type']}:{row['row_id']}"
        for row in evidence_rows
        if not row["evidence_paths"]
    ]
    if not evidence_rows:
        fail_reasons.append("empty evidence: no evidence rows derived from required JSON")
    if empty_evidence_rows:
        fail_reasons.append("empty evidence rows: " + ", ".join(empty_evidence_rows))

    for category_paths in REQUIRED_FILES.values():
        for rel in category_paths:
            path = repo_root / rel
            if path.is_file():
                for hit in text_promotion_hits(repo_root, rel):
                    fail_reasons.append(f"clayYangMillsPromoted=true in {hit['path']}:{hit['line']}")

    marker_hits = sprint133_marker_hits(repo_root)
    if marker_hits:
        fail_reasons.append("forbidden incomplete markers in Sprint133 Agda modules")

    route_decision = "ready_for_submission_index" if not fail_reasons else "fail_closed"
    commands = [
        "python scripts/ym_sprint131_submission_packet_builder.py --repo-root . --out-dir outputs/ym_sprint131_submission_packet",
        "python scripts/ym_sprint132_submission_bundle_index.py --repo-root . --out-dir outputs/ym_sprint132_submission_bundle_index",
        "python scripts/ym_sprint132_red_team_audit.py --repo-root . --out-dir outputs/ym_sprint132_red_team_audit",
        "python scripts/ym_sprint133_submission_readiness_index.py --repo-root . --out-dir outputs/ym_sprint133_submission_readiness_index",
    ]
    return {
        "audit_id": AUDIT_ID,
        "generated_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
        "route_decision": route_decision,
        "clayYangMillsPromoted": False,
        "fail_reasons": fail_reasons,
        "commands": commands,
        "required_files": {key: [path.as_posix() for path in paths] for key, paths in REQUIRED_FILES.items()},
        "artifact_hashes": sorted(artifacts, key=lambda row: row["path"]),
        "evidence_rows": sorted(evidence_rows, key=lambda row: (row["source"], row["row_type"], str(row["row_id"]))),
        "sprint133_agda_modules": sprint133,
        "sprint133_incomplete_marker_hits": marker_hits,
        "counts": {
            "row_type": "readiness-counts",
            "artifacts": len(artifacts),
            "evidence_rows": len(evidence_rows),
            "sprint133_agda_modules": len(sprint133),
            "fail_reasons": len(fail_reasons),
        },
        "fail_closed_policy": {
            "missing_required_files": "reject",
            "empty_required_files": "reject",
            "empty_evidence": "reject",
            "forbidden_sprint133_incomplete_markers": "reject",
            "any_clayYangMillsPromoted_true": "reject",
        },
    }


def render_markdown(summary: dict[str, Any]) -> str:
    lines = [
        "# Sprint133 Submission Readiness Index",
        "",
        f"- Generated UTC: `{summary['generated_utc']}`",
        f"- Route decision: `{summary['route_decision']}`",
        "- clayYangMillsPromoted: `false`",
        f"- Artifact hashes: `{summary['counts']['artifacts']}`",
        f"- Evidence rows: `{summary['counts']['evidence_rows']}`",
        "",
        "## Commands",
        "",
    ]
    lines.extend(f"- `{command}`" for command in summary["commands"])
    lines.extend(["", "## Fail Reasons", ""])
    if summary["fail_reasons"]:
        lines.extend(f"- {reason}" for reason in summary["fail_reasons"])
    else:
        lines.append("- none")

    lines.extend(["", "## Artifact Hashes", "", "| Category | Path | Bytes | SHA-256 |", "| --- | --- | ---: | --- |"])
    for row in summary["artifact_hashes"]:
        lines.append(f"| {row['category']} | `{row['path']}` | {row['size_bytes']} | `{row['sha256']}` |")

    lines.extend(["", "## Evidence Rows", "", "| Source | Type | Row | Evidence paths |", "| --- | --- | --- | --- |"])
    for row in summary["evidence_rows"]:
        evidence = "<br>".join(f"`{path}`" for path in row["evidence_paths"])
        lines.append(f"| `{row['source']}` | `{row['row_type']}` | `{row['row_id']}` | {evidence} |")

    if summary["sprint133_incomplete_marker_hits"]:
        lines.extend(["", "## Sprint133 Marker Hits", "", "| Path | Line | Marker |", "| --- | ---: | --- |"])
        for hit in summary["sprint133_incomplete_marker_hits"]:
            lines.append(f"| `{hit['path']}` | {hit['line']} | `{hit['marker']}` |")
    return "\n".join(lines) + "\n"


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir if args.out_dir.is_absolute() else repo_root / args.out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    summary = build_summary(repo_root)
    (out_dir / JSON_NAME).write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    (out_dir / MD_NAME).write_text(render_markdown(summary), encoding="utf-8")
    print(rel_path(repo_root, out_dir / JSON_NAME))
    print(rel_path(repo_root, out_dir / MD_NAME))
    return 0 if summary["route_decision"] != "fail_closed" else 1


if __name__ == "__main__":
    raise SystemExit(main())

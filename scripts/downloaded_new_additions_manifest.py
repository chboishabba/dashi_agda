#!/usr/bin/env python3
"""Inventory downloaded reference additions without making authority claims."""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
from pathlib import Path
from typing import Any


SCHEMA = "dashi-downloaded-new-additions-reference-index-v1"
SCHEMA_VERSION = "1.0.0"
DEFAULT_SOURCE_DIR = Path("temp-DOWNLOADED/new additions")
DEFAULT_OUTPUT_DIR = Path("outputs/downloaded_new_additions_reference_index")

TOPIC_KEYWORDS = {
    "ym": ("ym", "yang", "mills", "clay"),
    "hodge": ("hodge",),
    "string": ("string", "calabi", "yau", "compactification", "flux"),
    "quantum": ("quantum", "qft"),
    "constants": ("constant", "constants", "si", "sprint69"),
    "path-c": ("path c", "path-c", "path_c"),
    "voxel": ("voxel", "supervoxel"),
    "dark-sector": ("dark sector", "dark-sector", "dark_sector", "portal"),
    "eta-mesic": ("eta", "η", "mesic"),
}

CLASS_BY_SUFFIX = {
    ".pdf": "pdf",
    ".png": "image",
    ".jpg": "image",
    ".jpeg": "image",
    ".webp": "image",
    ".gif": "image",
    ".svg": "image",
    ".csv": "data",
    ".json": "data",
    ".jsonl": "data",
    ".tsv": "data",
    ".py": "code",
    ".agda": "code",
    ".hs": "code",
    ".html": "html",
    ".htm": "html",
}


def utc_now_iso() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


def sha256_file(path: Path, chunk_size: int = 1024 * 1024) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(chunk_size), b""):
            digest.update(chunk)
    return digest.hexdigest()


def classify_suffix(suffix: str) -> str:
    return CLASS_BY_SUFFIX.get(suffix.lower(), "other")


def tag_topics(filename: str) -> list[str]:
    normalized = filename.casefold().replace("_", " ").replace("-", " ")
    tags: list[str] = []
    for topic, needles in TOPIC_KEYWORDS.items():
        if any(needle.casefold() in normalized for needle in needles):
            tags.append(topic)
    return tags


def inventory(source_dir: Path) -> list[dict[str, Any]]:
    if not source_dir.exists():
        raise FileNotFoundError(f"source directory does not exist: {source_dir}")
    if not source_dir.is_dir():
        raise NotADirectoryError(f"source path is not a directory: {source_dir}")

    rows: list[dict[str, Any]] = []
    for path in sorted((p for p in source_dir.iterdir() if p.is_file()), key=lambda p: p.name.casefold()):
        suffix = path.suffix.lower()
        stat = path.stat()
        rows.append(
            {
                "filename": path.name,
                "relative_path": path.as_posix(),
                "suffix": suffix,
                "artifact_class": classify_suffix(suffix),
                "size_bytes": stat.st_size,
                "sha256": sha256_file(path),
                "topic_tags": tag_topics(path.name),
                "authority_claim": False,
                "theorem_claim": False,
                "promotion_claim": False,
            }
        )
    return rows


def count_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_class: dict[str, int] = {}
    by_suffix: dict[str, int] = {}
    by_topic: dict[str, int] = {topic: 0 for topic in TOPIC_KEYWORDS}
    untagged = 0

    for row in rows:
        by_class[row["artifact_class"]] = by_class.get(row["artifact_class"], 0) + 1
        by_suffix[row["suffix"]] = by_suffix.get(row["suffix"], 0) + 1
        if row["topic_tags"]:
            for topic in row["topic_tags"]:
                by_topic[topic] += 1
        else:
            untagged += 1

    return {
        "total_files": len(rows),
        "by_class": dict(sorted(by_class.items())),
        "by_suffix": dict(sorted(by_suffix.items())),
        "by_topic": dict(sorted(by_topic.items())),
        "untagged": untagged,
    }


def build_payload(source_dir: Path, generated_at: str) -> dict[str, Any]:
    rows = inventory(source_dir)
    return {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "generated_at": generated_at,
        "source_dir": source_dir.as_posix(),
        "counts": count_rows(rows),
        "promotion_flags": {
            "authority_source_promoted": False,
            "theorem_authority_promoted": False,
            "physics_lane_promoted": False,
            "chemistry_lane_promoted": False,
            "biology_lane_promoted": False,
            "ym_clay_promoted": False,
            "terminal_unification_promoted": False,
        },
        "claim_boundary": {
            "is_reference_inventory": True,
            "contains_content_checksums": True,
            "asserts_external_authority": False,
            "asserts_theorem_result": False,
            "asserts_promotion": False,
        },
        "rows": rows,
    }


def markdown_table(payload: dict[str, Any]) -> str:
    counts = payload["counts"]
    lines = [
        "# Downloaded New Additions Reference Index",
        "",
        f"- Schema: `{payload['schema']}`",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Source dir: `{payload['source_dir']}`",
        f"- Total files: `{counts['total_files']}`",
        "- Authority claims: `false`",
        "- Theorem claims: `false`",
        "- Promotion claims: `false`",
        "",
        "## Counts By Class",
        "",
        "| class | count |",
        "|---|---:|",
    ]
    for artifact_class, count in counts["by_class"].items():
        lines.append(f"| `{artifact_class}` | {count} |")

    lines.extend(
        [
            "",
            "## Topic Counts",
            "",
            "| topic | count |",
            "|---|---:|",
        ]
    )
    for topic, count in counts["by_topic"].items():
        lines.append(f"| `{topic}` | {count} |")
    lines.append(f"| `untagged` | {counts['untagged']} |")

    lines.extend(
        [
            "",
            "## Rows",
            "",
            "| file | class | suffix | bytes | sha256 | topics |",
            "|---|---|---|---:|---|---|",
        ]
    )
    for row in payload["rows"]:
        topics = ", ".join(f"`{topic}`" for topic in row["topic_tags"]) or "`none`"
        lines.append(
            "| "
            f"`{row['filename']}` | "
            f"`{row['artifact_class']}` | "
            f"`{row['suffix']}` | "
            f"{row['size_bytes']} | "
            f"`{row['sha256']}` | "
            f"{topics} |"
        )
    lines.append("")
    return "\n".join(lines)


def write_outputs(payload: dict[str, Any], output_dir: Path) -> tuple[Path, Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "downloaded_new_additions_reference_index.json"
    markdown_path = output_dir / "downloaded_new_additions_reference_index.md"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(markdown_table(payload), encoding="utf-8")
    return json_path, markdown_path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Inventory temp-DOWNLOADED/new additions with checksums and non-promoting topic tags."
    )
    parser.add_argument("--source-dir", type=Path, default=DEFAULT_SOURCE_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument(
        "--generated-at",
        default=None,
        help="Override generated_at timestamp. Defaults to current UTC ISO-8601 time.",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print the JSON payload to stdout instead of writing output files.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    generated_at = args.generated_at or utc_now_iso()
    payload = build_payload(args.source_dir, generated_at)

    if args.dry_run:
        print(json.dumps(payload, indent=2, sort_keys=True))
    else:
        json_path, markdown_path = write_outputs(payload, args.output_dir)
        print(f"wrote {json_path}")
        print(f"wrote {markdown_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

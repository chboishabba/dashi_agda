#!/usr/bin/env python3
"""Probe downloaded PDF context without making authority or promotion claims."""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import re
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import Any


SCHEMA = "dashi-downloaded-pdf-context-probe-v1"
SCHEMA_VERSION = "1.0.0"
DEFAULT_SOURCE_DIR = Path("temp-DOWNLOADED/new additions")
DEFAULT_OUTPUT_DIR = Path("outputs/downloaded_pdf_context_probe")
DEFAULT_MAX_LINES = 8
DEFAULT_TIMEOUT_SECONDS = 30

TOPIC_KEYWORDS = {
    "biology": ("biology", "genome", "organism", "clinical"),
    "chemistry": ("chemistry", "mesic", "eta", "η", "nucleus", "thermo"),
    "clay": ("clay",),
    "dark-sector": ("dark sector", "dark-sector", "portal"),
    "formalism": ("formalism", "bridging", "mdl", "les"),
    "gr": (" gr ", "gravity", "relativity", "curvature"),
    "hodge": ("hodge", "star", "dual"),
    "maxwell": ("maxwell", "electromagnetic", "field"),
    "mysticism-boundary": ("mysticism", "breakdown"),
    "outreach": ("outreach", "draft", "rewrite"),
    "path-c": ("path c", "path-c", "path_c"),
    "physics": ("physics", "qft", "field"),
    "quantum": ("quantum",),
    "string": ("string", "calabi", "compactification", "flux"),
    "voxel": ("voxel", "supervoxel", "3d"),
    "ym": ("ym", "yang", "mills"),
}


def utc_now_iso() -> str:
    return _dt.datetime.now(_dt.UTC).replace(microsecond=0).isoformat()


def sha256_file(path: Path, chunk_size: int = 1024 * 1024) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(chunk_size), b""):
            digest.update(chunk)
    return digest.hexdigest()


def normalize_for_tags(filename: str) -> str:
    stem = Path(filename).stem.casefold()
    return " " + re.sub(r"[_\-.]+", " ", stem) + " "


def tag_topics(filename: str) -> list[str]:
    normalized = normalize_for_tags(filename)
    tags: list[str] = []
    for topic, needles in TOPIC_KEYWORDS.items():
        if any(needle.casefold() in normalized for needle in needles):
            tags.append(topic)
    return tags


def command_path(name: str) -> str | None:
    return shutil.which(name)


def run_command(args: list[str], timeout_seconds: int) -> tuple[int | None, str, str]:
    try:
        completed = subprocess.run(
            args,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=timeout_seconds,
        )
        return completed.returncode, completed.stdout, completed.stderr
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout if isinstance(exc.stdout, str) else ""
        stderr = exc.stderr if isinstance(exc.stderr, str) else ""
        return None, stdout, f"timeout after {timeout_seconds}s\n{stderr}".strip()
    except OSError as exc:
        return None, "", str(exc)


def parse_pdfinfo(stdout: str) -> dict[str, Any]:
    fields: dict[str, Any] = {}
    for raw_line in stdout.splitlines():
        if ":" not in raw_line:
            continue
        key, value = raw_line.split(":", 1)
        normalized_key = key.strip().casefold().replace(" ", "_")
        fields[normalized_key] = value.strip()

    pages = fields.get("pages")
    if isinstance(pages, str) and pages.isdigit():
        fields["pages"] = int(pages)
    return fields


def compact_nonempty_lines(text: str, max_lines: int) -> list[str]:
    lines: list[str] = []
    for raw_line in text.splitlines():
        cleaned = re.sub(r"\s+", " ", raw_line).strip()
        if cleaned:
            lines.append(cleaned)
        if len(lines) >= max_lines:
            break
    return lines


def extract_pdf_text(path: Path, pdftotext_path: str | None, max_lines: int, timeout_seconds: int) -> dict[str, Any]:
    if pdftotext_path is None:
        return {
            "available": False,
            "status": "tool-unavailable",
            "first_nonempty_lines": [],
            "snippet": "",
            "stderr": "",
        }

    with tempfile.TemporaryDirectory(prefix="dashi_pdf_probe_") as tmpdir:
        out_path = Path(tmpdir) / "extracted.txt"
        returncode, _stdout, stderr = run_command(
            [pdftotext_path, "-layout", "-enc", "UTF-8", path.as_posix(), out_path.as_posix()],
            timeout_seconds,
        )
        if returncode != 0:
            return {
                "available": True,
                "status": "failed" if returncode is not None else "timeout-or-os-error",
                "returncode": returncode,
                "first_nonempty_lines": [],
                "snippet": "",
                "stderr": stderr.strip(),
            }
        try:
            text = out_path.read_text(encoding="utf-8", errors="replace")
        except OSError as exc:
            return {
                "available": True,
                "status": "readback-failed",
                "returncode": returncode,
                "first_nonempty_lines": [],
                "snippet": "",
                "stderr": str(exc),
            }
        lines = compact_nonempty_lines(text, max_lines)
        return {
            "available": True,
            "status": "ok",
            "returncode": returncode,
            "first_nonempty_lines": lines,
            "snippet": "\n".join(lines),
            "stderr": stderr.strip(),
        }


def extract_pdf_info(path: Path, pdfinfo_path: str | None, timeout_seconds: int) -> dict[str, Any]:
    if pdfinfo_path is None:
        return {
            "available": False,
            "status": "tool-unavailable",
            "metadata": {},
            "pages": None,
            "stderr": "",
        }
    returncode, stdout, stderr = run_command([pdfinfo_path, path.as_posix()], timeout_seconds)
    if returncode != 0:
        return {
            "available": True,
            "status": "failed" if returncode is not None else "timeout-or-os-error",
            "returncode": returncode,
            "metadata": {},
            "pages": None,
            "stderr": stderr.strip(),
        }
    metadata = parse_pdfinfo(stdout)
    return {
        "available": True,
        "status": "ok",
        "returncode": returncode,
        "metadata": metadata,
        "pages": metadata.get("pages"),
        "stderr": stderr.strip(),
    }


def probe_pdf(path: Path, tools: dict[str, str | None], max_lines: int, timeout_seconds: int) -> dict[str, Any]:
    stat = path.stat()
    info = extract_pdf_info(path, tools["pdfinfo"], timeout_seconds)
    text = extract_pdf_text(path, tools["pdftotext"], max_lines, timeout_seconds)
    return {
        "filename": path.name,
        "relative_path": path.as_posix(),
        "size_bytes": stat.st_size,
        "sha256": sha256_file(path),
        "topic_tags": tag_topics(path.name),
        "page_count": info["pages"],
        "pdfinfo": info,
        "pdftotext": text,
        "authority_claim": False,
        "theorem_claim": False,
        "promotion_claim": False,
    }


def count_rows(rows: list[dict[str, Any]]) -> dict[str, Any]:
    by_topic: dict[str, int] = {topic: 0 for topic in TOPIC_KEYWORDS}
    untagged = 0
    text_ok = 0
    info_ok = 0
    total_pages = 0
    page_count_known = 0
    for row in rows:
        if row["topic_tags"]:
            for topic in row["topic_tags"]:
                by_topic[topic] += 1
        else:
            untagged += 1
        if row["pdftotext"]["status"] == "ok":
            text_ok += 1
        if row["pdfinfo"]["status"] == "ok":
            info_ok += 1
        if isinstance(row["page_count"], int):
            page_count_known += 1
            total_pages += row["page_count"]
    return {
        "total_pdfs": len(rows),
        "pdfinfo_ok": info_ok,
        "pdftotext_ok": text_ok,
        "page_count_known": page_count_known,
        "total_known_pages": total_pages,
        "by_topic": dict(sorted(by_topic.items())),
        "untagged": untagged,
    }


def discover_pdfs(source_dir: Path) -> list[Path]:
    if not source_dir.exists():
        raise FileNotFoundError(f"source directory does not exist: {source_dir}")
    if not source_dir.is_dir():
        raise NotADirectoryError(f"source path is not a directory: {source_dir}")
    return sorted(source_dir.glob("*.pdf"), key=lambda path: path.name.casefold())


def build_payload(source_dir: Path, generated_at: str, max_lines: int, timeout_seconds: int) -> dict[str, Any]:
    tools = {
        "pdfinfo": command_path("pdfinfo"),
        "pdftotext": command_path("pdftotext"),
    }
    rows = [probe_pdf(path, tools, max_lines, timeout_seconds) for path in discover_pdfs(source_dir)]
    return {
        "schema": SCHEMA,
        "schema_version": SCHEMA_VERSION,
        "generated_at": generated_at,
        "source_dir": source_dir.as_posix(),
        "tool_status": tools,
        "extraction_policy": {
            "max_first_nonempty_lines": max_lines,
            "timeout_seconds_per_tool_call": timeout_seconds,
            "uses_external_pdf_tools_if_available": True,
            "fails_gracefully_when_tools_absent": True,
        },
        "counts": count_rows(rows),
        "claim_boundary": {
            "is_lightweight_context_probe": True,
            "contains_pdf_checksums": True,
            "contains_lightweight_snippets": True,
            "asserts_external_authority": False,
            "asserts_theorem_result": False,
            "asserts_promotion": False,
        },
        "promotion_flags": {
            "authority_source_promoted": False,
            "theorem_authority_promoted": False,
            "hodge_lane_promoted": False,
            "physics_lane_promoted": False,
            "ym_clay_promoted": False,
            "terminal_unification_promoted": False,
        },
        "rows": rows,
    }


def markdown_report(payload: dict[str, Any]) -> str:
    counts = payload["counts"]
    lines = [
        "# Downloaded PDF Context Probe",
        "",
        f"- Schema: `{payload['schema']}`",
        f"- Generated at: `{payload['generated_at']}`",
        f"- Source dir: `{payload['source_dir']}`",
        f"- PDFs: `{counts['total_pdfs']}`",
        f"- Known page total: `{counts['total_known_pages']}` across `{counts['page_count_known']}` PDFs",
        f"- `pdfinfo` ok: `{counts['pdfinfo_ok']}`",
        f"- `pdftotext` ok: `{counts['pdftotext_ok']}`",
        "- Authority claims: `false`",
        "- Theorem claims: `false`",
        "- Promotion claims: `false`",
        "",
        "## Tool Status",
        "",
        "| tool | path |",
        "|---|---|",
    ]
    for tool, path in sorted(payload["tool_status"].items()):
        lines.append(f"| `{tool}` | `{path or 'unavailable'}` |")

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
            "## PDF Rows",
            "",
            "| file | pages | bytes | sha256 | topics | text status |",
            "|---|---:|---:|---|---|---|",
        ]
    )
    for row in payload["rows"]:
        topics = ", ".join(f"`{topic}`" for topic in row["topic_tags"]) or "`none`"
        pages = row["page_count"] if row["page_count"] is not None else ""
        lines.append(
            "| "
            f"`{row['filename']}` | "
            f"{pages} | "
            f"{row['size_bytes']} | "
            f"`{row['sha256']}` | "
            f"{topics} | "
            f"`{row['pdftotext']['status']}` |"
        )

    lines.extend(["", "## Snippets", ""])
    for row in payload["rows"]:
        lines.append(f"### `{row['filename']}`")
        lines.append("")
        lines.append(f"- Pages: `{row['page_count'] if row['page_count'] is not None else 'unknown'}`")
        lines.append(f"- Tags: {', '.join(f'`{topic}`' for topic in row['topic_tags']) or '`none`'}")
        lines.append(f"- SHA-256: `{row['sha256']}`")
        lines.append("")
        snippet = row["pdftotext"]["snippet"]
        if snippet:
            lines.append("```text")
            lines.append(snippet)
            lines.append("```")
        else:
            lines.append(f"_No text snippet extracted; status `{row['pdftotext']['status']}`._")
        lines.append("")
    return "\n".join(lines)


def write_outputs(payload: dict[str, Any], output_dir: Path) -> tuple[Path, Path]:
    output_dir.mkdir(parents=True, exist_ok=True)
    json_path = output_dir / "downloaded_pdf_context_probe.json"
    markdown_path = output_dir / "downloaded_pdf_context_probe.md"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    markdown_path.write_text(markdown_report(payload), encoding="utf-8")
    return json_path, markdown_path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", type=Path, default=DEFAULT_SOURCE_DIR)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT_DIR)
    parser.add_argument("--generated-at", default=None)
    parser.add_argument("--max-lines", type=int, default=DEFAULT_MAX_LINES)
    parser.add_argument("--timeout-seconds", type=int, default=DEFAULT_TIMEOUT_SECONDS)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    generated_at = args.generated_at or utc_now_iso()
    payload = build_payload(args.source_dir, generated_at, args.max_lines, args.timeout_seconds)
    json_path, markdown_path = write_outputs(payload, args.output_dir)
    print(json.dumps({"json": json_path.as_posix(), "markdown": markdown_path.as_posix(), "counts": payload["counts"]}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

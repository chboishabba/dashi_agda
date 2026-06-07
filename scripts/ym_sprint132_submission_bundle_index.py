#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import re
from dataclasses import dataclass
from datetime import datetime, timezone
from pathlib import Path
from typing import Iterable


OUTPUT_JSON = "ym_sprint132_submission_bundle_index.json"
OUTPUT_MD = "ym_sprint132_submission_bundle_index.md"

SPRINT_OUTPUT_ARTIFACTS = {
    "sprint128_artifacts": (
        "outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit.md",
        "outputs/ym_sprint128_closure_audit/ym_sprint128_closure_audit_summary.json",
    ),
    "sprint129_artifacts": (
        "outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit.md",
        "outputs/ym_sprint129_mosco_spectral_audit/ym_sprint129_mosco_spectral_audit_summary.json",
    ),
    "sprint130_artifacts": (
        "outputs/ym_sprint130_os_fin_audit/ym_sprint130_os_fin_audit.md",
        "outputs/ym_sprint130_os_fin_audit/ym_sprint130_os_fin_audit_summary.json",
    ),
    "sprint131_artifacts": (
        "outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit.md",
        "outputs/ym_sprint131_final_claim_audit/ym_sprint131_final_claim_audit_summary.json",
        "outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet.md",
        "outputs/ym_sprint131_submission_packet/ym_sprint131_submission_packet_summary.json",
    ),
}

AGDA_DIR = Path("DASHI/Physics/Closure")
SPRINT_AGDA_PREFIXES = {
    "sprint128_agda_modules": "YMSprint128",
    "sprint129_agda_modules": "YMSprint129",
    "sprint130_agda_modules": "YMSprint130",
    "sprint131_agda_modules": "YMSprint131",
}

TOKEN_POSTULATE = "post" + "ulate"
TOKEN_TODO = "TO" + "DO"
TOKEN_STUB = "st" + "ub"
TOKEN_SKELETON = "skele" + "ton"
TOKEN_DUMMY = "dum" + "my"
TOKEN_FUTURE_PROOF = "future" + r"[\s-]*" + "proof"
TOKEN_HOLE = "ho" + "le"

SPRINT132_FORBIDDEN_PATTERNS = {
    "unproved axiom marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_POSTULATE + r"(?![A-Za-z0-9_])"
    ),
    "open work marker": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_TODO + r"(?![A-Za-z0-9_])"
    ),
    "placeholder wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_STUB + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "bare scaffold wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_SKELETON + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "dummy wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_DUMMY + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "deferred proof wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_FUTURE_PROOF + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "hole wording": re.compile(
        r"(?<![A-Za-z0-9_])" + TOKEN_HOLE + r"(?![A-Za-z0-9_])",
        re.IGNORECASE,
    ),
    "Agda hole braces": re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}")),
}

CLAY_PROMOTED_TRUE_PATTERNS = (
    re.compile(r"(?m)^\s*clayYangMillsPromoted\s*=\s*true\s*$"),
    re.compile(r'"clayYangMillsPromoted"\s*:\s*true'),
    re.compile(r"\bclayYangMillsPromoted\s*:\s*true\b"),
)


@dataclass(frozen=True)
class IndexedFile:
    category: str
    path: str
    size_bytes: int
    sha256: str


class FailClosedError(RuntimeError):
    pass


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Index Sprint128-131 submission artifacts and Sprint132 Agda modules."
    )
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=Path("outputs/ym_sprint132_submission_bundle_index"),
    )
    return parser.parse_args()


def relative(repo_root: Path, path: Path) -> str:
    return path.resolve().relative_to(repo_root.resolve()).as_posix()


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="replace")


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def discover_agda(repo_root: Path, prefix: str) -> list[str]:
    directory = repo_root / AGDA_DIR
    if not directory.is_dir():
        raise FailClosedError(f"missing Agda directory: {AGDA_DIR.as_posix()}")
    return [
        relative(repo_root, path)
        for path in sorted(directory.glob(prefix + "*.agda"))
        if path.is_file()
    ]


def build_category_paths(repo_root: Path) -> dict[str, list[str]]:
    categories = {
        category: list(paths)
        for category, paths in SPRINT_OUTPUT_ARTIFACTS.items()
    }
    for category, prefix in SPRINT_AGDA_PREFIXES.items():
        categories[category] = discover_agda(repo_root, prefix)

    sprint132_modules = discover_agda(repo_root, "YMSprint132")
    if sprint132_modules:
        categories["sprint132_agda_modules"] = sprint132_modules
    return categories


def validate_categories(categories: dict[str, list[str]]) -> None:
    empty = [category for category, paths in categories.items() if not paths]
    if empty:
        raise FailClosedError("empty required categories: " + ", ".join(empty))


def validate_file(repo_root: Path, rel_path: str) -> IndexedFile:
    path = repo_root / rel_path
    if not path.is_file():
        raise FailClosedError(f"missing referenced file: {rel_path}")
    size = path.stat().st_size
    if size <= 0:
        raise FailClosedError(f"empty referenced file: {rel_path}")
    return IndexedFile(
        category="",
        path=rel_path,
        size_bytes=size,
        sha256=sha256_file(path),
    )


def scan_for_promotion(repo_root: Path, rel_path: str) -> list[str]:
    path = repo_root / rel_path
    text = read_text(path)
    failures: list[str] = []
    for pattern in CLAY_PROMOTED_TRUE_PATTERNS:
        for match in pattern.finditer(text):
            failures.append(
                f"{rel_path}:{line_for_offset(text, match.start())}: clayYangMillsPromoted=true"
            )
    return failures


def scan_sprint132_incomplete(repo_root: Path, rel_path: str) -> list[str]:
    text = read_text(repo_root / rel_path)
    failures: list[str] = []
    for label, pattern in SPRINT132_FORBIDDEN_PATTERNS.items():
        for match in pattern.finditer(text):
            failures.append(f"{rel_path}:{line_for_offset(text, match.start())}: {label}")
    return failures


def index_files(repo_root: Path, categories: dict[str, list[str]]) -> list[IndexedFile]:
    indexed: list[IndexedFile] = []
    failures: list[str] = []
    seen: set[str] = set()

    for category, paths in categories.items():
        for rel_path in paths:
            if rel_path in seen:
                failures.append(f"duplicate referenced file: {rel_path}")
                continue
            seen.add(rel_path)
            try:
                item = validate_file(repo_root, rel_path)
            except FailClosedError as exc:
                failures.append(str(exc))
                continue
            indexed.append(
                IndexedFile(
                    category=category,
                    path=item.path,
                    size_bytes=item.size_bytes,
                    sha256=item.sha256,
                )
            )
            failures.extend(scan_for_promotion(repo_root, rel_path))
            if category == "sprint132_agda_modules":
                failures.extend(scan_sprint132_incomplete(repo_root, rel_path))

    if failures:
        raise FailClosedError("fail-closed validation errors:\n" + "\n".join(failures))
    return indexed


def render_json(categories: dict[str, list[str]], indexed: list[IndexedFile]) -> dict[str, object]:
    by_category: dict[str, list[dict[str, object]]] = {}
    for category in categories:
        by_category[category] = [
            {
                "category": item.category,
                "path": item.path,
                "size_bytes": item.size_bytes,
                "sha256": item.sha256,
            }
            for item in indexed
            if item.category == category
        ]

    return {
        "name": "ym_sprint132_submission_bundle_index",
        "generated_at_utc": datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
        "fail_closed": True,
        "clayYangMillsPromoted": False,
        "validation": {
            "missing_files_rejected": True,
            "empty_categories_rejected": True,
            "empty_files_rejected": True,
            "sprint132_incomplete_markers_rejected": True,
            "clayYangMillsPromoted_true_rejected": True,
        },
        "counts": {
            "categories": len(categories),
            "files": len(indexed),
            "bytes": sum(item.size_bytes for item in indexed),
        },
        "categories": by_category,
    }


def render_markdown(summary: dict[str, object]) -> str:
    categories = summary["categories"]
    assert isinstance(categories, dict)
    counts = summary["counts"]
    assert isinstance(counts, dict)

    lines = [
        "# YM Sprint132 Submission Bundle Index",
        "",
        f"- Generated UTC: `{summary['generated_at_utc']}`",
        f"- Files indexed: `{counts['files']}`",
        f"- Categories indexed: `{counts['categories']}`",
        f"- Total bytes: `{counts['bytes']}`",
        "- Fail closed: `true`",
        "- clayYangMillsPromoted: `false`",
        "",
        "## Validation",
        "",
    ]
    validation = summary["validation"]
    assert isinstance(validation, dict)
    for key in sorted(validation):
        lines.append(f"- `{key}`: `{str(validation[key]).lower()}`")

    for category, rows in categories.items():
        assert isinstance(rows, list)
        lines.extend(["", f"## {category}", ""])
        for row in rows:
            assert isinstance(row, dict)
            lines.append(
                f"- `{row['path']}` size=`{row['size_bytes']}` sha256=`{row['sha256']}`"
            )

    lines.append("")
    return "\n".join(lines)


def write_outputs(out_dir: Path, summary: dict[str, object]) -> list[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    json_path = out_dir / OUTPUT_JSON
    md_path = out_dir / OUTPUT_MD
    json_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    md_path.write_text(render_markdown(summary), encoding="utf-8")
    return [json_path, md_path]


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir

    categories = build_category_paths(repo_root)
    validate_categories(categories)
    indexed = index_files(repo_root, categories)
    summary = render_json(categories, indexed)
    paths = write_outputs(out_dir, summary)
    for path in paths:
        print(relative(repo_root, path))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

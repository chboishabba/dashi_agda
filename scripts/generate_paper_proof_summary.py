#!/usr/bin/env python3
"""Generate an ordered proof summary from a minimal Agda tree log."""

from __future__ import annotations

import argparse
import re
import sys
import textwrap
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
DOCSTRING_START = "{-!"
DOCSTRING_END = "-}"
FILE_PATTERN = re.compile(r"(?P<path>[^\s\t:]+?\.agda(?:\.log)?)")


@dataclass(frozen=True)
class FileSummary:
    path: Path
    rel_path: str
    docstring: str | None


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Read logs/minimal_tree_<paper>.txt, extract the first Agda docstring "
            "block from each listed file, and emit a drafting-oriented proof summary."
        )
    )
    parser.add_argument("paper", help="Paper identifier, e.g. Paper3_YangMills")
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=REPO_ROOT,
        help="Repository root. Defaults to the script's parent directory.",
    )
    return parser.parse_args(argv)


def fail(message: str) -> int:
    print(f"generate_paper_proof_summary: {message}", file=sys.stderr)
    return 1


def normalize_path(raw_path: str, repo_root: Path) -> Path:
    candidate = Path(raw_path)
    if candidate.is_absolute():
        return candidate
    return repo_root / candidate


def extract_listed_files(log_text: str, repo_root: Path) -> list[Path]:
    ordered: list[Path] = []
    seen: set[Path] = set()

    for line in log_text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue

        matches = [match.group("path").rstrip(".,;)]}") for match in FILE_PATTERN.finditer(stripped)]
        if not matches:
            continue

        chosen = next((raw for raw in matches if not raw.endswith(".agda.log")), matches[0])
        if chosen.endswith(".agda.log"):
            chosen = chosen[:-4]

        path = normalize_path(chosen, repo_root)
        if path in seen:
            continue
        seen.add(path)
        ordered.append(path)

    return ordered


def extract_first_docstring(text: str) -> str | None:
    start = text.find(DOCSTRING_START)
    if start < 0:
        return None

    cursor = start + len(DOCSTRING_START)
    depth = 1
    while cursor < len(text):
        next_start = text.find(DOCSTRING_START, cursor)
        next_end = text.find(DOCSTRING_END, cursor)

        if next_end < 0:
            return None
        if 0 <= next_start < next_end:
            depth += 1
            cursor = next_start + len(DOCSTRING_START)
            continue

        depth -= 1
        cursor = next_end + len(DOCSTRING_END)
        if depth == 0:
            raw = text[start + len(DOCSTRING_START) : next_end]
            return normalize_docstring(raw)

    return None


def normalize_docstring(block: str) -> str:
    lines = block.splitlines()
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()

    cleaned: list[str] = []
    for line in lines:
        stripped = line.rstrip()
        if stripped.startswith(" *"):
            stripped = stripped[2:]
            if stripped.startswith(" "):
                stripped = stripped[1:]
        cleaned.append(stripped.rstrip())

    normalized = textwrap.dedent("\n".join(cleaned)).strip()
    return normalized


def summarize_files(paths: list[Path], repo_root: Path) -> list[FileSummary]:
    summaries: list[FileSummary] = []
    for path in paths:
        rel_path = path.relative_to(repo_root).as_posix() if path.is_relative_to(repo_root) else str(path)
        if not path.exists():
            summaries.append(FileSummary(path=path, rel_path=rel_path, docstring=None))
            continue

        text = path.read_text(encoding="utf-8")
        summaries.append(
            FileSummary(
                path=path,
                rel_path=rel_path,
                docstring=extract_first_docstring(text),
            )
        )
    return summaries


def paragraph_lines(docstring: str) -> list[str]:
    paragraphs = [para.strip() for para in re.split(r"\n\s*\n", docstring) if para.strip()]
    lines: list[str] = []
    for index, paragraph in enumerate(paragraphs, start=1):
        wrapped = textwrap.wrap(
            paragraph,
            width=88,
            break_long_words=False,
            break_on_hyphens=False,
        )
        if not wrapped:
            continue
        if index > 1:
            lines.append("")
        lines.extend(wrapped)
    return lines


def render_summary(paper: str, log_path: Path, summaries: list[FileSummary]) -> str:
    lines: list[str] = [
        f"Paper: {paper}",
        f"Tree log: {log_path.relative_to(REPO_ROOT).as_posix() if log_path.is_relative_to(REPO_ROOT) else log_path}",
        f"Files: {len(summaries)}",
        "",
    ]

    for index, summary in enumerate(summaries, start=1):
        lines.append(f"{index}. {summary.rel_path}")
        if summary.docstring is None:
            if summary.path.exists():
                lines.append("   Docstring: [no `{-! ... -}` block found]")
            else:
                lines.append("   Docstring: [file missing]")
            lines.append("")
            continue

        lines.append("   Docstring:")
        for line in paragraph_lines(summary.docstring):
            if line:
                lines.append(f"   {line}")
            else:
                lines.append("   ")
        lines.append("")

    return "\n".join(lines).rstrip() + "\n"


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve()
    log_path = repo_root / "logs" / f"minimal_tree_{args.paper}.txt"

    if not log_path.exists():
        return fail(f"missing input log: {log_path}")

    try:
        log_text = log_path.read_text(encoding="utf-8")
    except OSError as exc:
        return fail(f"could not read {log_path}: {exc}")

    listed_files = extract_listed_files(log_text, repo_root)
    if not listed_files:
        return fail(f"no Agda files were found in {log_path}")

    summaries = summarize_files(listed_files, repo_root)
    sys.stdout.write(render_summary(args.paper, log_path, summaries))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

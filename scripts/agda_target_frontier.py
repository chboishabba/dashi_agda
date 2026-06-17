#!/usr/bin/env python3
"""Build deterministic Agda target batches for the parallel-check wrapper."""

from __future__ import annotations

import argparse
import json
import shlex
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Sequence


ROOT = Path(__file__).resolve().parents[1]
WRAPPER = "scripts/run_agda29_parallel_check.sh"


@dataclass(frozen=True)
class Batch:
    index: int
    group: str | None
    targets: tuple[str, ...]

    def command(self) -> list[str]:
        return [WRAPPER, *self.targets]


def _normalize_pathish(raw: str) -> str:
    text = raw.strip()
    if not text:
        return ""

    path = Path(text)
    if path.is_absolute():
        try:
            text = path.resolve().relative_to(ROOT).as_posix()
        except ValueError:
            text = path.as_posix()
    else:
        text = path.as_posix()
    return text


def _normalize_prefix(raw: str) -> str:
    text = raw.strip()
    if not text:
        return ""

    trailing_slash = text.endswith("/")
    path = Path(text)
    if path.is_absolute():
        try:
            text = path.resolve().relative_to(ROOT).as_posix()
        except ValueError:
            text = path.as_posix()
    else:
        text = path.as_posix()

    if trailing_slash and not text.endswith("/"):
        text += "/"
    return text


def _read_stdin_targets() -> list[str]:
    targets: list[str] = []
    for raw_line in sys.stdin:
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        for token in line.split():
            normalized = _normalize_pathish(token)
            if normalized:
                targets.append(normalized)
    return targets


def _dedupe_preserve_order(targets: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    result: list[str] = []
    for target in targets:
        if target in seen:
            continue
        seen.add(target)
        result.append(target)
    return result


def _top_level(target: str) -> str:
    return target.split("/", 1)[0]


def _prefix_match(target: str, prefixes: Sequence[str]) -> bool:
    return any(target.startswith(prefix) for prefix in prefixes)


def _chunk(items: Sequence[str], batch_size: int) -> list[tuple[str, ...]]:
    return [tuple(items[idx : idx + batch_size]) for idx in range(0, len(items), batch_size)]


def build_batches(
    targets: Sequence[str],
    batch_size: int,
    group_by_top_level: bool,
) -> list[Batch]:
    if batch_size <= 0:
        raise SystemExit("--batch-size must be a positive integer")

    normalized = sorted(_dedupe_preserve_order(targets))
    batches: list[Batch] = []

    if group_by_top_level:
        grouped: dict[str, list[str]] = {}
        for target in normalized:
            grouped.setdefault(_top_level(target), []).append(target)
        for group in sorted(grouped):
            for chunk in _chunk(grouped[group], batch_size):
                batches.append(Batch(index=len(batches) + 1, group=group, targets=chunk))
        return batches

    for chunk in _chunk(normalized, batch_size):
        batches.append(Batch(index=len(batches) + 1, group=None, targets=chunk))
    return batches


def _render_text(batches: Sequence[Batch]) -> str:
    lines: list[str] = []
    for batch in batches:
        prefix = f"[{batch.group}] " if batch.group else ""
        lines.append(f"{batch.index}. {prefix}{' '.join(shlex.quote(target) for target in batch.targets)}")
        lines.append("   " + " ".join(shlex.quote(part) for part in batch.command()))
    return "\n".join(lines)


def _render_json(
    raw_targets: Sequence[str],
    filtered_targets: Sequence[str],
    batches: Sequence[Batch],
    batch_size: int,
    group_by_top_level: bool,
    prefixes: Sequence[str],
) -> str:
    payload = {
        "root": str(ROOT),
        "wrapper": WRAPPER,
        "batch_size": batch_size,
        "group_by_top_level": group_by_top_level,
        "prefix_filters": list(prefixes),
        "input_count": len(raw_targets),
        "selected_count": len(filtered_targets),
        "batches": [
            {
                "index": batch.index,
                "group": batch.group,
                "targets": list(batch.targets),
                "command": batch.command(),
            }
            for batch in batches
        ],
    }
    return json.dumps(payload, indent=2, sort_keys=True)


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Read Agda target paths from CLI arguments or stdin and emit deterministic "
            "batches suitable for scripts/run_agda29_parallel_check.sh."
        )
    )
    parser.add_argument(
        "targets",
        nargs="*",
        help="Target paths to batch. Use '-' to read additional targets from stdin.",
    )
    parser.add_argument(
        "--batch-size",
        type=int,
        default=8,
        help="Maximum targets per batch. Default: 8.",
    )
    parser.add_argument(
        "--stdin",
        action="store_true",
        help="Read extra targets from stdin.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit JSON instead of shell-friendly text.",
    )
    parser.add_argument(
        "--prefix",
        action="append",
        default=[],
        metavar="PREFIX",
        help="Keep only targets that start with PREFIX. Repeatable.",
    )
    parser.add_argument(
        "--group-by-top-level",
        "--group-by-layer",
        dest="group_by_top_level",
        action="store_true",
        help="Keep batches within each top-level directory/layer.",
    )
    return parser.parse_args(argv)


def _collect_targets(args: argparse.Namespace) -> list[str]:
    targets: list[str] = []
    stdin_requested = args.stdin or not args.targets

    for raw in args.targets:
        if raw == "-":
            stdin_requested = True
            continue
        normalized = _normalize_pathish(raw)
        if normalized:
            targets.append(normalized)

    if stdin_requested:
        targets.extend(_read_stdin_targets())

    return targets


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    stdin_requested = args.stdin or "-" in args.targets or not args.targets
    if stdin_requested and sys.stdin.isatty():
        raise SystemExit("stdin was requested, but stdin is a tty; pipe a target list in or pass explicit targets")

    raw_targets = _collect_targets(args)
    prefixes = tuple(_normalize_prefix(prefix) for prefix in args.prefix if prefix.strip())
    selected = [
        target
        for target in raw_targets
        if not prefixes or _prefix_match(target, prefixes)
    ]
    selected = _dedupe_preserve_order(selected)
    batches = build_batches(selected, args.batch_size, args.group_by_top_level)

    if args.json:
        print(
            _render_json(
                raw_targets=raw_targets,
                filtered_targets=selected,
                batches=batches,
                batch_size=args.batch_size,
                group_by_top_level=args.group_by_top_level,
                prefixes=prefixes,
            )
        )
    else:
        print(_render_text(batches))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

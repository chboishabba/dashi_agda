from __future__ import annotations

import argparse
import json
import shlex
from pathlib import Path


def load_rows(path: Path) -> list[dict[str, object]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    if isinstance(data, list):
        rows = data
    elif isinstance(data, dict):
        rows = []
        for value in data.values():
            if isinstance(value, list):
                rows.extend(value)
    else:
        raise SystemExit(f"Unsupported batch payload type in {path}")
    filtered = [row for row in rows if isinstance(row, dict)]
    if not filtered:
        raise SystemExit(f"No queue rows found in {path}")
    return filtered


def extract_commands(rows: list[dict[str, object]]) -> list[str]:
    commands: list[str] = []
    for idx, row in enumerate(rows, start=1):
        command = row.get("command_template")
        if not isinstance(command, str) or not command.strip():
            raise SystemExit(
                f"Row {idx} is missing a usable command_template. "
                "Regenerate the batch JSON with --include-commands."
            )
        commands.append(command.strip())
    return commands


def dedupe_commands(commands: list[str]) -> list[str]:
    seen: set[str] = set()
    deduped: list[str] = []
    for command in commands:
        if command in seen:
            continue
        seen.add(command)
        deduped.append(command)
    return deduped


def build_shell_script(commands: list[str], source_path: Path) -> str:
    lines = [
        "#!/usr/bin/env bash",
        "set -euo pipefail",
        "",
        f"# Generated from {source_path}",
        "",
    ]
    for idx, command in enumerate(commands, start=1):
        lines.append(f'echo "[layer2 {idx}/{len(commands)}] {command}"')
        lines.append(command)
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def build_text(commands: list[str]) -> str:
    return "\n".join(commands) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Render executable command lines from a Layer 2 batch JSON artifact "
            "emitted by generate_layer2_long_compute_queue.py."
        )
    )
    parser.add_argument(
        "batch_json",
        type=Path,
        help="Path to a Layer 2 batch JSON file with command_template entries.",
    )
    parser.add_argument(
        "--format",
        choices=("text", "script"),
        default="text",
        help="Emit plain command lines or a runnable bash script.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        help="Optional output path. Defaults to stdout.",
    )
    parser.add_argument(
        "--dedupe",
        action="store_true",
        help="Collapse repeated identical command lines while preserving first-seen order.",
    )
    args = parser.parse_args()

    rows = load_rows(args.batch_json)
    commands = extract_commands(rows)
    if args.dedupe:
        commands = dedupe_commands(commands)

    if args.format == "script":
        payload = build_shell_script(commands, args.batch_json)
    else:
        payload = build_text(commands)

    if args.out:
        args.out.write_text(payload, encoding="utf-8")
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()

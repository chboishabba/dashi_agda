from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


ROOT = Path(__file__).resolve().parents[1]
SHELL_MODULE = "Ontology.Hecke.Layer2FiniteSearchShell"


@dataclass(frozen=True)
class StageTarget:
    stage: str
    target_name: str
    agda_module: str
    notes: str


@dataclass(frozen=True)
class PairPlan:
    pair_name: str
    left: str
    right: str
    preferred_sector_order: tuple[str, ...]
    stages: tuple[StageTarget, ...]


@dataclass(frozen=True)
class ShellCheck:
    check_name: str
    agda_module: str
    notes: str


PAIR_PLANS: tuple[PairPlan, ...] = (
    PairPlan(
        pair_name="first",
        left="balancedCycle",
        right="supportCascade",
        preferred_sector_order=("sector1", "sector0", "sector2"),
        stages=(
            StageTarget(
                stage="sector",
                target_name="FirstPairSectorSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Try sector-level separation first on the most asymmetric fixed-domain pair.",
            ),
            StageTarget(
                stage="package",
                target_name="FirstPairTriadPackageSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Only check whole-package triad equality if sector comparison does not separate.",
            ),
            StageTarget(
                stage="correlation",
                target_name="FirstPairCorrelationSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Correlation fallback if the triad histogram lane collapses on this pair.",
            ),
        ),
    ),
    PairPlan(
        pair_name="second",
        left="balancedComposed",
        right="supportCascade",
        preferred_sector_order=("sector1", "sector2", "sector0"),
        stages=(
            StageTarget(
                stage="sector",
                target_name="SecondPairSectorSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Second fixed-domain sector attempt.",
            ),
            StageTarget(
                stage="package",
                target_name="SecondPairTriadPackageSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Whole-package check only after sector collapse.",
            ),
            StageTarget(
                stage="correlation",
                target_name="SecondPairCorrelationSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Correlation fallback for the second pair.",
            ),
        ),
    ),
    PairPlan(
        pair_name="third",
        left="denseComposed",
        right="fullSupportCascade",
        preferred_sector_order=("sector0", "sector1", "sector2"),
        stages=(
            StageTarget(
                stage="sector",
                target_name="ThirdPairSectorSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Third fixed-domain sector attempt.",
            ),
            StageTarget(
                stage="package",
                target_name="ThirdPairTriadPackageSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Whole-package check only after sector collapse.",
            ),
            StageTarget(
                stage="correlation",
                target_name="ThirdPairCorrelationSeparates",
                agda_module="Ontology.Hecke.CurrentSaturatedPredictedPairComparisons",
                notes="Final fixed-domain correlation fallback.",
            ),
        ),
    ),
)


SHELL_CHECKS: tuple[ShellCheck, ...] = (
    ShellCheck(
        check_name="layer2-shell",
        agda_module=SHELL_MODULE,
        notes=(
            "Compile-thin shell only: validates the fixed Layer 2 pair/stage order "
            "without importing the heavy histogram lane."
        ),
    ),
)


def agda_command(module: str, jobs: int | None, include_parallel: bool) -> str:
    pieces = ["agda", "-i", "."]
    if include_parallel:
        pieces.extend(["--parallel"])
        if jobs is not None:
            pieces.extend(["-j", str(jobs)])
    pieces.append(module.replace("/", ".") if "/" in module else module)
    return " ".join(pieces)


def build_shell_batch(
    include_commands: bool,
    jobs: int | None,
    include_parallel: bool,
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for check in SHELL_CHECKS:
        row: dict[str, object] = {
            "batch": "shell",
            "check_name": check.check_name,
            "agda_module": check.agda_module,
            "notes": check.notes,
        }
        if include_commands:
            row["command_template"] = agda_command(
                check.agda_module,
                jobs=jobs,
                include_parallel=include_parallel,
            )
        rows.append(row)
    return rows


def build_offline_batch(
    include_commands: bool,
    jobs: int | None,
    include_parallel: bool,
) -> list[dict[str, object]]:
    rows: list[dict[str, object]] = []
    for pair in PAIR_PLANS:
        for stage in pair.stages:
            row: dict[str, object] = {
                "batch": "offline-heavy",
                "pair_name": pair.pair_name,
                "left": pair.left,
                "right": pair.right,
                "preferred_sector_order": list(pair.preferred_sector_order),
                "stage": stage.stage,
                "target_name": stage.target_name,
                "agda_module": stage.agda_module,
                "notes": stage.notes,
            }
            if include_commands:
                row["command_template"] = agda_command(
                    stage.agda_module,
                    jobs=jobs,
                    include_parallel=include_parallel,
                )
            rows.append(row)
    return rows


def render_shell_text(rows: Iterable[dict[str, object]]) -> list[str]:
    lines: list[str] = []
    for idx, row in enumerate(rows, start=1):
        lines.append(f"{idx}. shell check: {row['check_name']}")
        lines.append(f"   module: {row['agda_module']}")
        if "command_template" in row:
            lines.append(f"   command: {row['command_template']}")
        lines.append(f"   notes: {row['notes']}")
    return lines


def render_offline_text(rows: Iterable[dict[str, object]]) -> list[str]:
    lines: list[str] = []
    for idx, row in enumerate(rows, start=1):
        lines.append(
            f"{idx}. {row['pair_name']} pair: {row['left']} vs {row['right']} | "
            f"{row['stage']} -> {row['target_name']}"
        )
        lines.append(f"   sector order: {', '.join(row['preferred_sector_order'])}")
        lines.append(f"   module: {row['agda_module']}")
        if "command_template" in row:
            lines.append(f"   command: {row['command_template']}")
        lines.append(f"   notes: {row['notes']}")
    return lines


def render_text(shell_rows: Iterable[dict[str, object]], offline_rows: Iterable[dict[str, object]]) -> str:
    sections: list[str] = []
    shell_lines = render_shell_text(shell_rows)
    offline_lines = render_offline_text(offline_rows)
    if shell_lines:
        sections.append("Shell Batch")
        sections.extend(shell_lines)
    if offline_lines:
        if sections:
            sections.append("")
        sections.append("Offline Heavy Batch")
        sections.extend(offline_lines)
    return "\n".join(sections)


def render_batch_text(rows: Iterable[dict[str, object]], batch_name: str) -> str:
    if batch_name == "shell":
        return "\n".join(render_shell_text(rows))
    return "\n".join(render_offline_text(rows))


def group_offline_by_pair(rows: Iterable[dict[str, object]]) -> dict[str, list[dict[str, object]]]:
    grouped: dict[str, list[dict[str, object]]] = {}
    for row in rows:
        grouped.setdefault(str(row["pair_name"]), []).append(row)
    return grouped


def group_offline_by_stage(rows: Iterable[dict[str, object]]) -> dict[str, list[dict[str, object]]]:
    grouped: dict[str, list[dict[str, object]]] = {}
    for row in rows:
        grouped.setdefault(str(row["stage"]), []).append(row)
    return grouped


def write_payload(path: Path, payload: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(payload + ("" if payload.endswith("\n") else "\n"), encoding="utf-8")


def build_batch_index(
    out_dir: Path,
    shell_rows: list[dict[str, object]],
    offline_rows: list[dict[str, object]],
) -> dict[str, object]:
    by_pair = group_offline_by_pair(offline_rows)
    by_stage = group_offline_by_stage(offline_rows)
    return {
        "root": str(out_dir),
        "shell": {
            "row_count": len(shell_rows),
            "text": "shell.txt",
            "json": "shell.json",
            "checks": [str(row.get("check_name", "")) for row in shell_rows],
        },
        "offline-heavy": {
            "row_count": len(offline_rows),
            "text": "offline-heavy.txt",
            "json": "offline-heavy.json",
            "pairs": {
                pair_name: {
                    "row_count": len(rows),
                    "left": str(rows[0].get("left", "")) if rows else "",
                    "right": str(rows[0].get("right", "")) if rows else "",
                    "preferred_sector_order": list(rows[0].get("preferred_sector_order", [])) if rows else [],
                    "text": f"offline-heavy-by-pair/{pair_name}.txt",
                    "json": f"offline-heavy-by-pair/{pair_name}.json",
                }
                for pair_name, rows in by_pair.items()
            },
            "stages": {
                stage_name: {
                    "row_count": len(rows),
                    "text": f"offline-heavy-by-stage/{stage_name}.txt",
                    "json": f"offline-heavy-by-stage/{stage_name}.json",
                }
                for stage_name, rows in by_stage.items()
            },
        },
    }


def write_batch_files(
    out_dir: Path,
    shell_rows: list[dict[str, object]],
    offline_rows: list[dict[str, object]],
) -> None:
    write_payload(out_dir / "shell.txt", render_batch_text(shell_rows, "shell"))
    write_payload(out_dir / "shell.json", json.dumps(shell_rows, indent=2))

    write_payload(out_dir / "offline-heavy.txt", render_batch_text(offline_rows, "offline-heavy"))
    write_payload(out_dir / "offline-heavy.json", json.dumps(offline_rows, indent=2))

    by_pair_dir = out_dir / "offline-heavy-by-pair"
    for pair_name, rows in group_offline_by_pair(offline_rows).items():
        write_payload(by_pair_dir / f"{pair_name}.txt", render_batch_text(rows, "offline-heavy"))
        write_payload(by_pair_dir / f"{pair_name}.json", json.dumps(rows, indent=2))

    by_stage_dir = out_dir / "offline-heavy-by-stage"
    for stage_name, rows in group_offline_by_stage(offline_rows).items():
        write_payload(by_stage_dir / f"{stage_name}.txt", render_batch_text(rows, "offline-heavy"))
        write_payload(by_stage_dir / f"{stage_name}.json", json.dumps(rows, indent=2))

    index = build_batch_index(out_dir, shell_rows, offline_rows)
    write_payload(out_dir / "index.json", json.dumps(index, indent=2))
    lines = [
        "Layer 2 Batch Index",
        "",
        f"root: {index['root']}",
        "",
        "shell:",
        f"  rows: {index['shell']['row_count']}",
        f"  text: {index['shell']['text']}",
        f"  json: {index['shell']['json']}",
    ]
    shell_checks = index["shell"]["checks"]
    if shell_checks:
        lines.append(f"  checks: {', '.join(shell_checks)}")
    lines.extend(
        [
            "",
            "offline-heavy:",
            f"  rows: {index['offline-heavy']['row_count']}",
            f"  text: {index['offline-heavy']['text']}",
            f"  json: {index['offline-heavy']['json']}",
            "  pairs:",
        ]
    )
    for pair_name, info in index["offline-heavy"]["pairs"].items():
        lines.extend(
            [
                f"    - {pair_name}: {info['left']} vs {info['right']}",
                f"      rows: {info['row_count']}",
                f"      sector_order: {', '.join(info['preferred_sector_order'])}",
                f"      text: {info['text']}",
                f"      json: {info['json']}",
            ]
        )
    lines.append("  stages:")
    for stage_name, info in index["offline-heavy"]["stages"].items():
        lines.extend(
            [
                f"    - {stage_name}",
                f"      rows: {info['row_count']}",
                f"      text: {info['text']}",
                f"      json: {info['json']}",
            ]
        )
    write_payload(out_dir / "index.txt", "\n".join(lines))


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Emit the fixed Layer 2 queue as separate compile-thin shell checks and "
            "offline-heavy replay batches for the saturated-branch separator program."
        )
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
        help="Output format.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        help="Optional output path. Defaults to stdout.",
    )
    parser.add_argument(
        "--include-commands",
        action="store_true",
        help="Include Agda command templates for each queued step.",
    )
    parser.add_argument(
        "--parallel",
        action="store_true",
        help="Emit `agda --parallel` command templates.",
    )
    parser.add_argument(
        "-j",
        "--jobs",
        type=int,
        help="Optional job count for command templates. Only used with --parallel.",
    )
    parser.add_argument(
        "--batch",
        choices=("all", "shell", "offline-heavy"),
        default="all",
        help="Emit all batches, only the compile-thin shell batch, or only the offline-heavy batch.",
    )
    parser.add_argument(
        "--write-batch-files",
        type=Path,
        help=(
            "Optional output directory for materialized batch artifacts. "
            "Writes shell.{txt,json}, offline-heavy.{txt,json}, and grouped "
            "offline-heavy-by-pair / offline-heavy-by-stage files."
        ),
    )
    args = parser.parse_args()

    shell_rows = build_shell_batch(
        include_commands=args.include_commands,
        jobs=args.jobs,
        include_parallel=args.parallel,
    )
    offline_rows = build_offline_batch(
        include_commands=args.include_commands,
        jobs=args.jobs,
        include_parallel=args.parallel,
    )

    if args.batch == "shell":
        shell_rows_to_emit = shell_rows
        offline_rows_to_emit: list[dict[str, object]] = []
    elif args.batch == "offline-heavy":
        shell_rows_to_emit = []
        offline_rows_to_emit = offline_rows
    else:
        shell_rows_to_emit = shell_rows
        offline_rows_to_emit = offline_rows

    if args.format == "json":
        payload = json.dumps(
            {
                "shell": shell_rows_to_emit,
                "offline-heavy": offline_rows_to_emit,
            },
            indent=2,
        )
    else:
        payload = render_text(shell_rows_to_emit, offline_rows_to_emit)

    if args.write_batch_files:
        write_batch_files(args.write_batch_files, shell_rows_to_emit, offline_rows_to_emit)

    if args.out:
        args.out.write_text(payload + ("\n" if not payload.endswith("\n") else ""), encoding="utf-8")
    else:
        print(payload)


if __name__ == "__main__":
    main()

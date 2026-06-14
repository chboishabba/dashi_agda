#!/usr/bin/env python3
"""Audit stale-consumer flip candidates with exact-boundary and suffix reports."""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


FLIPPED_FACTS = [
    "enstrophyPassageClosed",
    "vorticityControlClosed",
    "lInfinityVorticityControlClosed",
    "globalRegularityClosed",
    "uniformBKMVorticityControlClosed",
    "globalSmoothRegularityProved",
    "localKPSumBelowOneProved",
    "strictAbsorptionControlPromoted",
    "uniformVolumeKPProved",
    "balabanRGTransferProved",
    "actualPolymerActivitySupplied",
    "balabanH3aContinuumIntakeClosed",
    "h3bVacuumProjectorContinuity",
    "noSpectralPollution",
    "osThermoLimit",
    "wightmanReconstruction",
    "operatorConvergenceRateExplicit",
    "uniformMassGapConstructed",
    "continuumYangMillsConstructed",
    "continuumUniquenessConstructed",
    "ymL3TightnessConstructed",
    "fullTightnessConstructed",
    "brstGaugeFixedOS3Closed",
    "ghostGradedSignClosed",
    "continuumGribovResolved",
    "gate3DensityOfCarrierCoreProved",
    "gate3MoscoRecoveryProved",
    "gate3NoSpectralPollutionProved",
    "gate3MassShellBridgeProved",
    "gate3UniformSeparationProved",
]

ID_CHARS = r"A-Za-z0-9_'"
BOUNDARY = rf"(?<![{ID_CHARS}]){{fact}}(?![{ID_CHARS}])"
ASSIGNMENT_CONTEXT = re.compile(r"(?:=|≡)\s*(true|false)\b")
HEAD_ASSIGNMENT = re.compile(r"^(\s*;?\s*)(?P<lhs>.+?)(\s*=\s*)$")
BARE_BOOL = re.compile(r"^(\s*)(true|false)(\s*(--.*)?)$")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Scan Agda sources for exact-boundary stale-consumer flip candidates "
            "and suspicious suffixed lookalikes."
        )
    )
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Repository root. Defaults to the script's parent directory.",
    )
    parser.add_argument(
        "--log-dir",
        type=Path,
        default=None,
        help="Directory that receives stale-consumer audit TSV files. Defaults to <repo>/logs.",
    )
    return parser.parse_args(argv)


def relpath(path: Path, repo_root: Path) -> str:
    return path.resolve().relative_to(repo_root).as_posix()


def build_patterns() -> tuple[dict[str, re.Pattern[str]], dict[str, re.Pattern[str]]]:
    exact = {
        fact: re.compile(rf"(?<![{ID_CHARS}]){re.escape(fact)}(?![{ID_CHARS}])")
        for fact in FLIPPED_FACTS
    }
    suffix = {
        fact: re.compile(rf"(?<![{ID_CHARS}]){re.escape(fact)}(?=[{ID_CHARS}])")
        for fact in FLIPPED_FACTS
    }
    return exact, suffix


def classify_context(line: str) -> str | None:
    match = ASSIGNMENT_CONTEXT.search(line)
    if match is None:
        return None
    return match.group(1)


def render_line(head: str, tail: str | None = None) -> str:
    head = head.replace("\t", " ")
    if tail is None:
        return head
    return f"{head} || {tail.replace('\t', ' ')}"


def scan_file(
    path: Path,
    repo_root: Path,
    exact_patterns: dict[str, re.Pattern[str]],
    suffix_patterns: dict[str, re.Pattern[str]],
) -> tuple[list[tuple[str, str, str, int, str]], list[tuple[str, str, str, int, str]]]:
    exact_rows: list[tuple[str, str, str, int, str]] = []
    suffix_rows: list[tuple[str, str, str, int, str]] = []

    text = path.read_text(encoding="utf-8", errors="ignore")
    lines = text.splitlines()
    index = 0

    while index < len(lines):
        raw_line = lines[index]
        line = raw_line.split("--", 1)[0]
        stripped = line.rstrip()

        exact_fact = next((fact for fact, pattern in exact_patterns.items() if pattern.search(line)), None)
        suffix_fact = next((fact for fact, pattern in suffix_patterns.items() if pattern.search(line)), None)
        context = classify_context(line)

        if exact_fact is not None and context is not None:
            exact_rows.append(
                ("exact", exact_fact, relpath(path, repo_root), index + 1, render_line(stripped))
            )

        if suffix_fact is not None and context is not None:
            suffix_rows.append(
                ("suspicious_suffix", suffix_fact, relpath(path, repo_root), index + 1, render_line(stripped))
            )

        head = HEAD_ASSIGNMENT.match(line)
        if head is None:
            index += 1
            continue

        if exact_fact is not None and index + 1 < len(lines):
            next_line = lines[index + 1].split("--", 1)[0]
            next_bool = BARE_BOOL.match(next_line.rstrip())
            if next_bool is not None:
                exact_rows.append(
                    (
                        "exact_split",
                        exact_fact,
                        relpath(path, repo_root),
                        index + 1,
                        render_line(head.group(0).rstrip(), next_line.rstrip()),
                    )
                )

        if suffix_fact is not None and index + 1 < len(lines):
            next_line = lines[index + 1].split("--", 1)[0]
            next_bool = BARE_BOOL.match(next_line.rstrip())
            if next_bool is not None:
                suffix_rows.append(
                    (
                        "suspicious_suffix_split",
                        suffix_fact,
                        relpath(path, repo_root),
                        index + 1,
                        render_line(head.group(0).rstrip(), next_line.rstrip()),
                    )
                )

        index += 1

    return exact_rows, suffix_rows


def write_tsv(path: Path, rows: list[tuple[str, str, str, int, str]]) -> None:
    header = "kind\tfact\tfile\tline\tmatched_text\n"
    with path.open("w", encoding="utf-8") as fh:
        fh.write(header)
        for kind, fact, file, line, matched_text in rows:
            fh.write(f"{kind}\t{fact}\t{file}\t{line}\t{matched_text}\n")


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve()
    log_dir = (args.log_dir or repo_root / "logs").resolve()
    log_dir.mkdir(parents=True, exist_ok=True)

    exact_out = log_dir / "stale_consumer_audit.tsv"
    suffix_out = log_dir / "stale_consumer_suffix_audit.tsv"

    exact_patterns, suffix_patterns = build_patterns()

    exact_rows: list[tuple[str, str, str, int, str]] = []
    suffix_rows: list[tuple[str, str, str, int, str]] = []

    agda_files = sorted((path for path in repo_root.rglob("*.agda") if path.is_file()), key=lambda p: relpath(p, repo_root))
    for path in agda_files:
        file_exact, file_suffix = scan_file(path, repo_root, exact_patterns, suffix_patterns)
        exact_rows.extend(file_exact)
        suffix_rows.extend(file_suffix)

    exact_rows.sort(key=lambda row: (row[1], row[2], row[3], row[4]))
    suffix_rows.sort(key=lambda row: (row[1], row[2], row[3], row[4]))

    write_tsv(exact_out, exact_rows)
    write_tsv(suffix_out, suffix_rows)

    print(f"repo_root: {repo_root}")
    print(f"scanned_agda_files: {len(agda_files)}")
    print(f"exact_boundary_hits: {len(exact_rows)}")
    print(f"exact_audit: {exact_out}")
    print(f"suspicious_suffix_hits: {len(suffix_rows)}")
    print(f"suffix_audit: {suffix_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

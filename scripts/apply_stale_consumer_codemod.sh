#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/apply_stale_consumer_codemod.sh [options]

Mechanically rewrites stale Agda consumer literals from `field = false` to
`field = true` for the fixed whitelist of 30 fields, while preserving the
protected governance tokens listed below. Use `--dry-run` to audit without
editing Agda sources.

Options:
  --repo-root PATH   Repository root to scan. Default: script parent.
  --log-dir PATH     Root directory for generated logs. Default: <repo>/logs
  --dry-run          Report would-change diffs and write logs, but do not edit.
  --help             Show this help.

Protected tokens never get rewritten if they appear on a line:
  clayNavierStokes
  clayYangMills
  terminal
  fullUnification
  gate3Promoted
EOF
}

repo_root=""
log_root=""
dry_run=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --repo-root)
      [[ $# -ge 2 ]] || { echo "error: --repo-root requires a value" >&2; exit 2; }
      repo_root="$2"
      shift 2
      ;;
    --log-dir)
      [[ $# -ge 2 ]] || { echo "error: --log-dir requires a value" >&2; exit 2; }
      log_root="$2"
      shift 2
      ;;
    --dry-run)
      dry_run=1
      shift
      ;;
    --help|-h)
      usage
      exit 0
      ;;
    *)
      echo "error: unknown argument: $1" >&2
      exit 2
      ;;
  esac
done

if [[ -z "$repo_root" ]]; then
  script_dir="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
  repo_root="$(CDPATH= cd -- "${script_dir}/.." && pwd)"
fi

if [[ -z "$log_root" ]]; then
  log_root="${repo_root}/logs"
fi

mkdir -p "$log_root"

python3 - "$repo_root" "$log_root" "$dry_run" <<'PY'
from __future__ import annotations

import difflib
import os
import re
import sys
from collections import Counter
from datetime import datetime
from pathlib import Path

REPO_ROOT = Path(sys.argv[1]).resolve()
LOG_ROOT = Path(sys.argv[2]).resolve()
DRY_RUN = sys.argv[3] == "1"

FIELDS = [
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

PROTECTED_TOKENS = [
    "clayNavierStokes",
    "clayYangMills",
    "terminal",
    "fullUnification",
    "gate3Promoted",
]

ID_CHARS = r"A-Za-z0-9_'"


def exact_fact_pattern(field: str) -> str:
    return rf"(?<![{ID_CHARS}]){re.escape(field)}(?![{ID_CHARS}])"


EXACT_FACT_PATTERNS = {
    field: re.compile(exact_fact_pattern(field))
    for field in FIELDS
}
ASSIGNMENT_LINE_PATTERNS = {
    field: re.compile(
        rf"^(\s*;?\s*)({exact_fact_pattern(field)})(\s*=\s*)false(\s*(--.*)?)$"
    )
    for field in FIELDS
}
ASSIGNMENT_HEAD_PATTERNS = {
    field: re.compile(rf"^(\s*;?\s*)({exact_fact_pattern(field)})(\s*=\s*)$")
    for field in FIELDS
}
EQUALITY_PATTERNS = {
    field: re.compile(
        rf"((?:[A-Za-z0-9_']+\.)*{exact_fact_pattern(field)}(?=[\s()])(?:[\s(][^≡]*)?≡\s*)false\b"
    )
    for field in FIELDS
}
SUSPICIOUS_SUFFIX_PATTERNS = {
    field: re.compile(rf"(?<![{ID_CHARS}]){re.escape(field)}(?=[{ID_CHARS}])")
    for field in FIELDS
}
SUSPICIOUS_SUFFIX_HEAD_PATTERNS = {
    field: re.compile(rf"^(\s*;?\s*)({re.escape(field)}[{ID_CHARS}]*)\s*=\s*$")
    for field in FIELDS
}
BOOL_CONTEXT_PATTERN = re.compile(r"(?:=|≡)\s*(true|false)\b")
BARE_BOOL_PATTERN = re.compile(r"^(\s*)(true|false)(\s*(--.*)?)$")


def rel(path: Path) -> str:
    return path.resolve().relative_to(REPO_ROOT).as_posix()


def rewrite_text(text: str) -> tuple[str, Counter[str], int]:
    counts: Counter[str] = Counter()
    protected_hits = 0
    lines = text.splitlines(keepends=True)
    new_lines: list[str] = []
    index = 0

    while index < len(lines):
        line = lines[index]
        stripped_newline = ""
        core = line
        if core.endswith("\r\n"):
            stripped_newline = "\r\n"
            core = core[:-2]
        elif core.endswith("\n"):
            stripped_newline = "\n"
            core = core[:-1]

        if any(token in core for token in PROTECTED_TOKENS):
            protected_hits += 1
            new_lines.append(line)
            index += 1
            continue

        rewritten = core
        flipped = False

        for field, pattern in ASSIGNMENT_LINE_PATTERNS.items():
            match = pattern.match(core)
            if match is None:
                continue
            rewritten = f"{match.group(1)}{match.group(2)}{match.group(3)}true{match.group(4)}"
            counts[field] += 1
            flipped = True
            break

        if not flipped:
            for field, pattern in EQUALITY_PATTERNS.items():
                if pattern.search(rewritten) is None:
                    continue
                rewritten = pattern.sub(r"\1true", rewritten)
                counts[field] += 1
                flipped = True
                break

        new_lines.append(rewritten + stripped_newline)

        if not flipped:
            for field, pattern in ASSIGNMENT_HEAD_PATTERNS.items():
                if pattern.match(core) is None or index + 1 >= len(lines):
                    continue
                next_line = lines[index + 1]
                next_newline = ""
                next_core = next_line
                if next_core.endswith("\r\n"):
                    next_newline = "\r\n"
                    next_core = next_core[:-2]
                elif next_core.endswith("\n"):
                    next_newline = "\n"
                    next_core = next_core[:-1]

                if any(token in next_core for token in PROTECTED_TOKENS):
                    protected_hits += 1
                    break

                next_match = BARE_BOOL_PATTERN.match(next_core)
                if next_match is None or next_match.group(2) != "false":
                    continue

                new_lines.append(f"{next_match.group(1)}true{next_match.group(3)}{next_newline}")
                counts[field] += 1
                index += 2
                flipped = True
                break

            if flipped:
                continue

        index += 1

    return "".join(new_lines), counts, protected_hits


def collect_audit_rows(text: str, relative_path: str) -> tuple[
    list[tuple[str, str, str, int, str]],
    list[tuple[str, str, str, int, str]],
]:
    exact_rows: list[tuple[str, str, str, int, str]] = []
    suffix_rows: list[tuple[str, str, str, int, str]] = []
    lines = text.splitlines()
    index = 0

    while index < len(lines):
        raw_line = lines[index]
        line = raw_line.split("--", 1)[0]
        stripped = line.rstrip()
        exact_fact = next((field for field, pattern in EXACT_FACT_PATTERNS.items() if pattern.search(line)), None)
        if exact_fact is None:
            exact_fact = next((field for field, pattern in EQUALITY_PATTERNS.items() if pattern.search(line)), None)
        suffix_fact = next(
            (field for field, pattern in SUSPICIOUS_SUFFIX_PATTERNS.items() if pattern.search(line)),
            None,
        )
        context = BOOL_CONTEXT_PATTERN.search(line)

        if exact_fact is not None and context is not None:
            exact_rows.append(("exact", exact_fact, relative_path, index + 1, stripped.replace("\t", " ")))

        if suffix_fact is not None and context is not None:
            suffix_rows.append(("suspicious_suffix", suffix_fact, relative_path, index + 1, stripped.replace("\t", " ")))

        if index + 1 >= len(lines):
            index += 1
            continue

        head_match = ASSIGNMENT_HEAD_PATTERNS[exact_fact].match(line) if exact_fact is not None else None
        suffix_head_match = (
            SUSPICIOUS_SUFFIX_HEAD_PATTERNS[suffix_fact].match(line) if suffix_fact is not None else None
        )
        if head_match is None and suffix_head_match is None:
            index += 1
            continue

        next_line = lines[index + 1].split("--", 1)[0]
        next_match = BARE_BOOL_PATTERN.match(next_line.rstrip())
        if next_match is None:
            index += 1
            continue

        if head_match is not None:
            exact_rows.append(
                (
                    "exact_split",
                    exact_fact,
                    relative_path,
                    index + 1,
                    f"{line.rstrip().replace('\t', ' ')} || {next_line.rstrip().replace('\t', ' ')}",
                )
            )

        if suffix_head_match is not None:
            suffix_rows.append(
                (
                    "suspicious_suffix_split",
                    suffix_fact,
                    relative_path,
                    index + 1,
                    f"{line.rstrip().replace('\t', ' ')} || {next_line.rstrip().replace('\t', ' ')}",
                )
            )

        index += 1

    return exact_rows, suffix_rows


run_stamp = f"{datetime.now().strftime('%Y%m%dT%H%M%S')}_{os.getpid()}"
run_dir = LOG_ROOT / "apply_stale_consumer_codemod" / run_stamp
run_dir.mkdir(parents=True, exist_ok=True)

patch_path = run_dir / "patch.diff"
audit_path = run_dir / "audit.log"
changed_manifest_path = run_dir / "changed_files.tsv"
exact_audit_path = run_dir / "exact_audit.tsv"
suffix_audit_path = run_dir / "suffix_audit.tsv"

agda_files = sorted(
    (path for path in REPO_ROOT.rglob("*.agda") if path.is_file()),
    key=lambda path: rel(path),
)
field_counts: Counter[str] = Counter({field: 0 for field in FIELDS})
changed_files: list[tuple[Path, int]] = []
patch_chunks: list[str] = []
protected_hits = 0
exact_rows: list[tuple[str, str, str, int, str]] = []
suffix_rows: list[tuple[str, str, str, int, str]] = []

for path in agda_files:
    original = path.read_text(encoding="utf-8")
    relative_path = rel(path)
    file_exact_rows, file_suffix_rows = collect_audit_rows(original, relative_path)
    exact_rows.extend(file_exact_rows)
    suffix_rows.extend(file_suffix_rows)
    rewritten, file_counts, file_protected_hits = rewrite_text(original)
    protected_hits += file_protected_hits
    if rewritten == original:
        continue

    file_flip_count = sum(file_counts.values())
    changed_files.append((path, file_flip_count))
    field_counts.update(file_counts)
    patch_chunks.extend(
        difflib.unified_diff(
            original.splitlines(),
            rewritten.splitlines(),
            fromfile=f"{relative_path} (before)",
            tofile=f"{relative_path} (after)",
            lineterm="",
        )
    )
    if not DRY_RUN:
        path.write_text(rewritten, encoding="utf-8")

patch_text = "\n".join(patch_chunks)
if patch_text:
    patch_text += "\n"
patch_path.write_text(patch_text, encoding="utf-8")

exact_audit_rows = [
    "kind\tfact\tfile\tline\tmatched_text\n",
]
exact_audit_rows.extend(f"{kind}\t{fact}\t{file}\t{line}\t{matched_text}\n" for kind, fact, file, line, matched_text in exact_rows)
exact_audit_path.write_text("".join(exact_audit_rows), encoding="utf-8")

suffix_audit_rows = [
    "kind\tfact\tfile\tline\tmatched_text\n",
]
suffix_audit_rows.extend(
    f"{kind}\t{fact}\t{file}\t{line}\t{matched_text}\n" for kind, fact, file, line, matched_text in suffix_rows
)
suffix_audit_path.write_text("".join(suffix_audit_rows), encoding="utf-8")

changed_manifest_lines = [f"{rel(path)}\t{count}" for path, count in changed_files]
changed_manifest_path.write_text(
    ("\n".join(changed_manifest_lines) + "\n") if changed_manifest_lines else "",
    encoding="utf-8",
)

total_flips = sum(field_counts.values())
nonzero_fields = [(field, field_counts[field]) for field in FIELDS if field_counts[field] > 0]
planned_files = len(changed_files)
written_files = 0 if DRY_RUN else planned_files

audit_lines = [
    "script: apply_stale_consumer_codemod",
    f"repo_root: {REPO_ROOT}",
    f"run_dir: {run_dir}",
    f"dry_run: {DRY_RUN}",
    f"scanned_agda_files: {len(agda_files)}",
    f"planned_files: {planned_files}",
    f"written_files: {written_files}",
    f"total_field_flips: {total_flips}",
    f"protected_line_hits: {protected_hits}",
    "",
    f"exact_audit: {exact_audit_path}",
    f"suffix_audit: {suffix_audit_path}",
    "",
    "field_counts:",
]
if nonzero_fields:
    audit_lines.extend(f"  {field}\t{count}" for field, count in nonzero_fields)
else:
    audit_lines.append("  (none)")
audit_lines.extend(["", "changed_files:"])
if changed_files:
    audit_lines.extend(f"  {rel(path)}\t{count}" for path, count in changed_files)
else:
    audit_lines.append("  (none)")
audit_lines.extend(
    [
        "",
        f"patch_log: {patch_path}",
        f"changed_files_manifest: {changed_manifest_path}",
    ]
)
audit_path.write_text("\n".join(audit_lines) + "\n", encoding="utf-8")

print("script: apply_stale_consumer_codemod")
print(f"repo_root: {REPO_ROOT}")
print(f"run_dir: {run_dir}")
print(f"dry_run: {DRY_RUN}")
print(f"scanned_agda_files: {len(agda_files)}")
print(f"planned_files: {planned_files}")
print(f"written_files: {written_files}")
print(f"total_field_flips: {total_flips}")
print(f"protected_line_hits: {protected_hits}")
print(f"patch_log: {patch_path}")
print(f"audit_log: {audit_path}")
print(f"exact_audit: {exact_audit_path}")
print(f"suffix_audit: {suffix_audit_path}")
print("field_counts:")
if nonzero_fields:
    for field, count in nonzero_fields:
        print(f"  {field}\t{count}")
else:
    print("  (none)")
print("changed_files:")
if changed_files:
    for path, count in changed_files:
        print(f"  {rel(path)}\t{count}")
else:
    print("  (none)")
PY

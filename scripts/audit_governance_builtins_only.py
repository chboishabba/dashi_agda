#!/usr/bin/env python3
"""Flag Agda modules that use governance vocabulary but import only built-ins.

This is a heuristic architecture audit, not a proof or CI typecheck. Intentional
leaf/domain carriers are recorded in scripts/governance_builtins_allowlist.txt.
CI can restrict failure to files changed from a base revision so legacy islands
remain visible without blocking unrelated work.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import subprocess
import sys

KEYWORDS = {
    "candidateOnly",
    "clinicalAuthority",
    "diagnosisAuthority",
    "treatmentAuthority",
    "legalAuthority",
    "culturalAuthority",
    "empiricalValidationAuthority",
    "mindReading",
    "forcedNormalization",
    "forcedNormalisation",
    "noExtraction",
    "noUniversalization",
    "noUniversalisation",
    "notProof",
    "guideOnly",
}

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)


def load_allowlist(root: Path, allowlist_path: Path) -> set[str]:
    path = allowlist_path if allowlist_path.is_absolute() else root / allowlist_path
    if not path.exists():
        return set()
    entries: set[str] = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            entries.add(line)
    return entries


def changed_agda_files(root: Path, base: str | None) -> set[str] | None:
    if base is None:
        return None
    try:
        result = subprocess.run(
            ["git", "diff", "--name-only", f"{base}...HEAD", "--", "*.agda"],
            cwd=root,
            check=True,
            capture_output=True,
            text=True,
        )
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f"unable to determine changed files from {base}: {exc}", file=sys.stderr)
        return set()
    return {line.strip() for line in result.stdout.splitlines() if line.strip()}


def audit(
    root: Path,
    allowlist: set[str],
    changed_only: set[str] | None,
) -> list[tuple[Path, list[str]]]:
    findings: list[tuple[Path, list[str]]] = []
    for path in sorted(root.rglob("*.agda")):
        rel = path.relative_to(root).as_posix()
        if rel in allowlist:
            continue
        if changed_only is not None and rel not in changed_only:
            continue
        text = path.read_text(encoding="utf-8")
        matched = sorted(keyword for keyword in KEYWORDS if keyword in text)
        if not matched:
            continue
        imports = IMPORT_RE.findall(text)
        non_builtin = [name for name in imports if not name.startswith("Agda.")]
        if not non_builtin:
            findings.append((path.relative_to(root), matched))
    return findings


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", nargs="?", default=".", type=Path)
    parser.add_argument(
        "--allowlist",
        default=Path("scripts/governance_builtins_allowlist.txt"),
        type=Path,
    )
    parser.add_argument(
        "--changed-from",
        help="restrict findings to Agda files changed from this git revision",
    )
    parser.add_argument("--fail", action="store_true", help="exit non-zero when findings exist")
    args = parser.parse_args()

    root = args.root.resolve()
    allowlist = load_allowlist(root, args.allowlist)
    changed_only = changed_agda_files(root, args.changed_from)
    findings = audit(root, allowlist, changed_only)

    for path, keywords in findings:
        print(f"{path}: builtins-only governance vocabulary: {', '.join(keywords)}")
    print(f"allowlisted={len(allowlist)} findings={len(findings)}")
    return 1 if args.fail and findings else 0


if __name__ == "__main__":
    sys.exit(main())

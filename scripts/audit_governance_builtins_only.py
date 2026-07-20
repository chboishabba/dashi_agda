#!/usr/bin/env python3
"""Flag Agda modules that use governance vocabulary but import only built-ins.

This is a heuristic architecture audit, not a proof or CI typecheck.  Neutral
leaf modules may be allow-listed when their self-contained status is deliberate.
"""

from __future__ import annotations

import argparse
from pathlib import Path
import re
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

ALLOWLIST = {
    "DASHI/Core/CandidateOnlyCore.agda",
    "DASHI/Core/AuthorityNonPromotionCore.agda",
    "DASHI/Promotion/AuthorityBoundaryCore.agda",
}

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)


def audit(root: Path) -> list[tuple[Path, list[str]]]:
    findings: list[tuple[Path, list[str]]] = []
    for path in sorted(root.rglob("*.agda")):
        rel = path.relative_to(root).as_posix()
        if rel in ALLOWLIST:
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
    parser.add_argument("--fail", action="store_true", help="exit non-zero when findings exist")
    args = parser.parse_args()

    findings = audit(args.root)
    for path, keywords in findings:
        print(f"{path}: builtins-only governance vocabulary: {', '.join(keywords)}")
    print(f"findings={len(findings)}")
    return 1 if args.fail and findings else 0


if __name__ == "__main__":
    sys.exit(main())

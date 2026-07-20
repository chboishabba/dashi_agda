#!/usr/bin/env python3
"""Audit governance-bearing Agda modules that import only built-ins.

This heuristic spans cultural, legal, biological/medical, physics, AI/latent,
trading, educational, and general promotion surfaces. Intentional leaves must be
explicitly allow-listed and should have a downstream integrated adapter.
"""
from __future__ import annotations
import argparse
from collections import Counter
from pathlib import Path
import re
import subprocess
import sys

KEYWORDS = {
    "candidateOnly", "promoted", "theoremAuthority", "truthAuthority",
    "supportAuthority", "admissibilityAuthority", "notProof", "guideOnly",
    "referenceOnly", "clinicalAuthority", "diagnosisAuthority",
    "diagnosticAuthority", "treatmentAuthority", "interventionAuthority",
    "pathologyPromotion", "cureFraming", "mindReading", "forcedNormalization",
    "forcedNormalisation", "culturalAuthority", "educationalAuthority",
    "noExtraction", "extractionBlocked", "noUniversalization",
    "noUniversalisation", "livingPractice", "provenanceRequired",
    "legalAuthority", "politicalAuthority", "tradingAuthority",
    "runtimeAuthority", "empiricalValidationAuthority", "empiricalAuthority",
    "scientificAuthority", "physicsAuthority", "causalAuthority",
    "causalInference", "reverseInference", "latentInference",
    "proxyIsNotCause", "measurementIsNotDiagnosis", "hiddenChart",
    "connectomeOverclaim", "boldOverclaim",
}

DOMAIN_PREFIXES = (
    ("DASHI/Culture/", "culture"), ("DASHI/Legal/", "legal"),
    ("DASHI/Biology/", "biology-medical"), ("DASHI/Physics/", "physics"),
    ("DASHI/AI/", "ai-latent"), ("DASHI/ML/", "ai-latent"),
    ("DASHI/Trading/", "trading"), ("DASHI/Education/", "education"),
    ("DASHI/Promotion/", "promotion-core"),
)
IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.]+)", re.MULTILINE)

def classify_domain(path: str) -> str:
    for prefix, domain in DOMAIN_PREFIXES:
        if path.startswith(prefix): return domain
    lowered = path.lower()
    if "legal" in lowered or "court" in lowered: return "legal"
    if "trading" in lowered or "market" in lowered: return "trading"
    if "education" in lowered or "pedagog" in lowered: return "education"
    if "latent" in lowered or "neural" in lowered or "/ai" in lowered: return "ai-latent"
    return "other"

def load_allowlist(root: Path, allowlist_path: Path) -> set[str]:
    path = allowlist_path if allowlist_path.is_absolute() else root / allowlist_path
    if not path.exists(): return set()
    return {line.strip() for line in path.read_text(encoding="utf-8").splitlines()
            if line.strip() and not line.strip().startswith("#")}

def changed_agda_files(root: Path, base: str | None) -> set[str] | None:
    if base is None: return None
    try:
        result = subprocess.run(["git", "diff", "--name-only", f"{base}...HEAD", "--", "*.agda"], cwd=root, check=True, capture_output=True, text=True)
    except (OSError, subprocess.CalledProcessError) as exc:
        print(f"unable to determine changed files from {base}: {exc}", file=sys.stderr)
        return set()
    return {line.strip() for line in result.stdout.splitlines() if line.strip()}

def audit(root: Path, allowlist: set[str], changed_only: set[str] | None) -> list[tuple[Path, str, list[str]]]:
    findings = []
    for path in sorted(root.rglob("*.agda")):
        rel = path.relative_to(root).as_posix()
        if rel in allowlist or (changed_only is not None and rel not in changed_only): continue
        text = path.read_text(encoding="utf-8")
        matched = sorted(keyword for keyword in KEYWORDS if keyword in text)
        if not matched: continue
        non_builtin = [name for name in IMPORT_RE.findall(text) if not name.startswith("Agda.")]
        if not non_builtin: findings.append((path.relative_to(root), classify_domain(rel), matched))
    return findings

def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", nargs="?", default=".", type=Path)
    parser.add_argument("--allowlist", default=Path("scripts/governance_builtins_allowlist.txt"), type=Path)
    parser.add_argument("--changed-from")
    parser.add_argument("--fail", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()
    allowlist = load_allowlist(root, args.allowlist)
    findings = audit(root, allowlist, changed_agda_files(root, args.changed_from))
    counts: Counter[str] = Counter()
    for path, domain, keywords in findings:
        counts[domain] += 1
        print(f"{path}: domain={domain} builtins-only governance vocabulary: {', '.join(keywords)}")
    summary = " ".join(f"{domain}={count}" for domain, count in sorted(counts.items()))
    print(f"allowlisted={len(allowlist)} findings={len(findings)} {summary}".rstrip())
    return 1 if args.fail and findings else 0

if __name__ == "__main__": sys.exit(main())

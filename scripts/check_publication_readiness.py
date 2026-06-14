#!/usr/bin/env python3
"""Validate the local publication-readiness support packet for Papers 1, 3, and 8."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_BASENAME = "core_papers_theorem_var_manifest"
MANIFEST_DIR = Path("Docs/papers/generated")
MANIFEST_PATHS = tuple(
    MANIFEST_DIR / f"{MANIFEST_BASENAME}.{suffix}" for suffix in ("json", "tsv", "md")
)

LIVE_PAPER_FILES = (
    Path("Docs/papers/live/Paper1NavierStokesClayDraft.md"),
    Path("Docs/papers/live/Paper3YangMillsClayDraft.md"),
    Path("Docs/papers/live/Paper8UnificationDraft.md"),
    Path("Docs/papers/PublicationRoadmap.md"),
)

THEOREM_INTERFACE_TARGETS = (
    Path("DASHI/Papers/NavierStokes/TheoremInterface.agda"),
    Path("DASHI/Papers/YangMills/TheoremInterface.agda"),
    Path("DASHI/Papers/Unification/TheoremInterface.agda"),
    Path("DASHI/Papers/CoreTheoremInterfaces.agda"),
    Path("DASHI/Papers/VirtualPaper1Root.agda"),
    Path("DASHI/Papers/VirtualPaper3Root.agda"),
    Path("DASHI/Papers/VirtualPaper8Root.agda"),
    Path("DASHI/DCHoTT/All.agda"),
    Path("DASHI/Cubical/UnificationCandidate.agda"),
)

REQUIRED_ANCHORS = {
    "Paper1 NS": (
        "canonicalNSPaperTheoremStatus",
        "a6TheoremProved",
        "a7ResidualDepletionProved",
        "a8FullLocalDefectMonotonicityProved",
        "a9CKNBKMClosureProved",
        "nsPaperInterfaceTerminalFalse",
    ),
    "Paper3 YM": (
        "canonicalYangMillsPaperTheoremInterface",
        "paperInterfaceLocalDominationTrue",
        "paperInterfacePAWOTGTransferTrue",
        "paperInterfaceClayTerminalFalse",
    ),
    "Paper8 Unification": (
        "canonicalUnificationPaperTheoremInterface",
        "unificationPaperInterfaceTerminalFalse",
        "unificationPaperInterfaceUCT4StillOpen",
    ),
}

FORBIDDEN_CLAIM_PHRASES = (
    "clay-approved",
    "clay approved",
    "clay-accepted",
    "clay accepted",
)


@dataclass(frozen=True)
class CheckResult:
    name: str
    ok: bool
    detail: str


def rel(path: Path, repo_root: Path) -> str:
    try:
        return path.relative_to(repo_root).as_posix()
    except ValueError:
        return path.as_posix()


def load_manifest(repo_root: Path) -> tuple[dict[str, object] | None, list[CheckResult]]:
    path = repo_root / MANIFEST_DIR / f"{MANIFEST_BASENAME}.json"
    results: list[CheckResult] = []
    if not path.exists():
        return None, [CheckResult("manifest-json-exists", False, rel(path, repo_root))]
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        return None, [CheckResult("manifest-json-parseable", False, f"{rel(path, repo_root)}: {exc}")]
    results.append(CheckResult("manifest-json-parseable", True, rel(path, repo_root)))
    return payload, results


def check_live_files(repo_root: Path) -> list[CheckResult]:
    results = []
    for path in LIVE_PAPER_FILES:
        full = repo_root / path
        results.append(
            CheckResult(
                f"live-file:{path.as_posix()}",
                full.exists() and full.is_file(),
                path.as_posix(),
            )
        )
    return results


def check_manifest_files(repo_root: Path) -> list[CheckResult]:
    generator = repo_root / "scripts/generate_paper_proof_manifest.py"
    results = []
    newest_source_mtime = generator.stat().st_mtime if generator.exists() else 0.0

    for path in MANIFEST_PATHS:
        full = repo_root / path
        exists = full.exists() and full.is_file()
        fresh = exists and full.stat().st_mtime >= newest_source_mtime
        results.append(CheckResult(f"manifest-file:{path.as_posix()}", exists and fresh, path.as_posix()))
    return results


def check_manifest_payload(payload: dict[str, object] | None, repo_root: Path) -> list[CheckResult]:
    if payload is None:
        return []
    rows = payload.get("rows")
    results: list[CheckResult] = []
    if not isinstance(rows, list):
        return [CheckResult("manifest-rows-list", False, "rows must be a list")]

    papers = {row.get("paper") for row in rows if isinstance(row, dict)}
    results.append(
        CheckResult(
            "manifest-core-papers-present",
            {"Paper1 NS", "Paper3 YM", "Paper8 Unification"} <= papers,
            ", ".join(sorted(str(paper) for paper in papers)),
        )
    )
    results.append(CheckResult("manifest-row-count", payload.get("row_count") == len(rows), str(len(rows))))

    bad_false_rows = []
    missing_files = []
    missing_vars = []
    text_cache: dict[Path, str] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        agda_file = row.get("agda_file")
        exact_var = row.get("exact_var")
        expected_status = row.get("expected_status")
        note = f"{row.get('lemma', '')} {row.get('governance_note', '')}".lower()
        if ("clay" in note or "terminal" in note or "promotion" in note) and "false" in note:
            if expected_status != "false" and "guard" in note:
                bad_false_rows.append(str(row.get("lemma", "<unknown>")))
        if not isinstance(agda_file, str) or not isinstance(exact_var, str):
            continue
        full = repo_root / agda_file
        if not full.exists():
            missing_files.append(agda_file)
            continue
        if full not in text_cache:
            text_cache[full] = full.read_text(encoding="utf-8")
        if exact_var not in text_cache[full]:
            missing_vars.append(f"{exact_var} in {agda_file}")

    results.append(CheckResult("manifest-terminal-guards-false", not bad_false_rows, "; ".join(bad_false_rows)))
    results.append(CheckResult("manifest-agda-files-exist", not missing_files, "; ".join(missing_files)))
    results.append(CheckResult("manifest-exact-vars-present", not missing_vars, "; ".join(missing_vars[:10])))
    return results


def check_theorem_interfaces(repo_root: Path) -> list[CheckResult]:
    results: list[CheckResult] = []
    for path in THEOREM_INTERFACE_TARGETS:
        full = repo_root / path
        results.append(CheckResult(f"agda-target-listed:{path.as_posix()}", full.exists(), path.as_posix()))

    for paper, anchors in REQUIRED_ANCHORS.items():
        if paper == "Paper1 NS":
            path = repo_root / "DASHI/Papers/NavierStokes/TheoremInterface.agda"
        elif paper == "Paper3 YM":
            path = repo_root / "DASHI/Papers/YangMills/TheoremInterface.agda"
        else:
            path = repo_root / "DASHI/Papers/Unification/TheoremInterface.agda"
        text = path.read_text(encoding="utf-8") if path.exists() else ""
        missing = [anchor for anchor in anchors if anchor not in text]
        results.append(CheckResult(f"anchors:{paper}", not missing, "; ".join(missing)))
    return results


def check_claim_boundaries(repo_root: Path) -> list[CheckResult]:
    paths = [*LIVE_PAPER_FILES, Path("Docs/support/live/SupportCompendium.md")]
    hits = []
    for path in paths:
        full = repo_root / path
        if not full.exists():
            continue
        text = full.read_text(encoding="utf-8").lower()
        for phrase in FORBIDDEN_CLAIM_PHRASES:
            if phrase in text:
                hits.append(f"{path.as_posix()}:{phrase}")
    return [CheckResult("claim-boundary-forbidden-phrases", not hits, "; ".join(hits))]


def agda_command(target: Path) -> list[str]:
    stdlib_path = Path("/tmp/dashi-agda-stdlib")
    if not stdlib_path.exists():
        stdlib_path = Path("/usr/share/agda/lib/stdlib")
    return [
        "agda",
        "--no-libraries",
        "-i",
        ".",
        "-i",
        "DCHoTT-Agda",
        "-i",
        "cubical",
        "-i",
        stdlib_path.as_posix(),
        target.as_posix(),
    ]


def run_agda_targets(repo_root: Path, targets: tuple[Path, ...]) -> list[CheckResult]:
    results: list[CheckResult] = []
    for target in targets:
        proc = subprocess.run(
            agda_command(target),
            cwd=repo_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        results.append(
            CheckResult(
                f"agda-typecheck:{target.as_posix()}",
                proc.returncode == 0,
                proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else "ok",
            )
        )
    return results


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=REPO_ROOT)
    parser.add_argument("--run-agda", action="store_true", help="typecheck the declared Agda support targets")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve()

    payload, manifest_load_results = load_manifest(repo_root)
    results = [
        *check_live_files(repo_root),
        *check_manifest_files(repo_root),
        *manifest_load_results,
        *check_manifest_payload(payload, repo_root),
        *check_theorem_interfaces(repo_root),
        *check_claim_boundaries(repo_root),
    ]
    if args.run_agda:
        results.extend(run_agda_targets(repo_root, THEOREM_INTERFACE_TARGETS))

    width = max(len(result.name) for result in results)
    for result in results:
        status = "PASS" if result.ok else "FAIL"
        print(f"{status} {result.name.ljust(width)} {result.detail}")

    failures = [result for result in results if not result.ok]
    if failures:
        print(f"publication readiness: {len(failures)} failing checks", file=sys.stderr)
        return 1
    print("publication readiness: core support packet checks passed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

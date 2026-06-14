#!/usr/bin/env python3
"""Validate the local publication-readiness support packet for Papers 1, 3, and 8."""

from __future__ import annotations

import argparse
import json
import re
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

PAPER_UPGRADE_OBLIGATION_SOURCES = {
    "paper1-ns-upgrade-obligations": (
        Path("Docs/papers/live/Paper1NavierStokesClayDraft.md"),
    ),
    "paper3-ym-upgrade-obligations": (
        Path("Docs/papers/live/Paper3YangMillsClayDraft.md"),
        Path("Docs/support/live/PaperCommonCitationLedger.md"),
        Path("scripts/render_core_paper_pdfs.py"),
    ),
}

PAPER_UPGRADE_OBLIGATION_GROUPS = {
    "paper1-ns-upgrade-obligations": (
        ("seregin/ess-intake", ("seregin/ess", "ess/seregin", "seregin-rate")),
        (
            "ess-intake",
            ("seregin/ess intake", "ess/seregin intake", "quantitative seregin/ess rate intake"),
        ),
        ("target-not-derived-r-1-12", ("r^(1/12)", "target", "not promoted")),
        ("route-compatibility", ("route", "compatible")),
    ),
    "paper3-ym-upgrade-obligations": (
        ("balaban-1988-lemma-3", ("balaban 1988 lemma 3",)),
        ("activity-bound", ("activity bound",)),
        ("polymer-summability", ("polymer summability",)),
        ("trace-norm", ("trace norm", "trace-norm")),
        ("option-b-deferred", ("option b deferred",)),
        ("seiler-compatibility", ("seiler compatibility", "seiler-compatibility")),
    ),
}

CLAY_PUBLICATION_GOVERNANCE_ROWS = (
    {
        "gate_id": "ARXIV_JOURNAL_READINESS_NOT_CLAY_PRIZE_SUBMISSION",
        "boundary": "arXiv/journal submission readiness is not Clay prize submission",
        "governance_owner": "external",
        "internal_readiness_promotes_clay": False,
        "clay_prize_submission_claim": False,
        "fail_closed": True,
    },
    {
        "gate_id": "TWO_YEAR_COMMUNITY_ACCEPTANCE_EXTERNAL",
        "boundary": "two-year post-publication/community acceptance remains external governance",
        "governance_owner": "external",
        "internal_readiness_promotes_clay": False,
        "clay_prize_submission_claim": False,
        "fail_closed": True,
    },
    {
        "gate_id": "NO_DIRECT_CMI_MANUSCRIPT_SUBMISSION_CLAIM",
        "boundary": "no direct CMI manuscript submission claim is promoted",
        "governance_owner": "external",
        "internal_readiness_promotes_clay": False,
        "clay_prize_submission_claim": False,
        "fail_closed": True,
    },
)

FORBIDDEN_CLAY_PUBLICATION_PATTERNS = (
    (
        "arxiv-or-journal-as-clay-prize-submission",
        re.compile(
            r"\b(?:arxiv|journal|referee|publication)[^\n.]{0,100}"
            r"\b(?:is|as|equals|constitutes|counts\s+as)[^\n.]{0,40}"
            r"\b(?:clay|cmi)[^\n.]{0,80}\b(?:prize\s+)?submission\b",
            re.IGNORECASE,
        ),
    ),
    (
        "direct-cmi-manuscript-submission",
        re.compile(
            r"\bsubmit(?:ted|s|ting)?[^\n.]{0,80}\b(?:manuscript|paper|draft)[^\n.]{0,80}"
            r"\b(?:directly\s+)?(?:to|with)\s+(?:cmi|clay\s+mathematics\s+institute)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "cmi-acceptance-or-approval-claim",
        re.compile(
            r"\b(?:cmi|clay\s+mathematics\s+institute)[^\n.]{0,100}"
            r"\b(?:accepted|approved|validated|certified|received)[^\n.]{0,80}"
            r"\b(?:manuscript|paper|draft|submission|claim)\b",
            re.IGNORECASE,
        ),
    ),
    (
        "internal-community-acceptance-claim",
        re.compile(
            r"\b(?:two[- ]year|2[- ]year|community\s+acceptance)[^\n.]{0,100}"
            r"\b(?:satisfied|discharged|completed|proved|internal|repository-local)\b",
            re.IGNORECASE,
        ),
    ),
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


def forbidden_clay_publication_hits(repo_root: Path, paths: list[Path]) -> list[str]:
    hits: list[str] = []
    for path in paths:
        full = repo_root / path
        if not full.exists():
            continue
        text = full.read_text(encoding="utf-8", errors="replace")
        for name, pattern in FORBIDDEN_CLAY_PUBLICATION_PATTERNS:
            for match in pattern.finditer(text):
                line = text.count("\n", 0, match.start()) + 1
                hits.append(f"{path.as_posix()}:{line}:{name}")
    return hits


def check_clay_publication_governance(repo_root: Path) -> list[CheckResult]:
    rows = list(CLAY_PUBLICATION_GOVERNANCE_ROWS)
    gate_ids = {str(row.get("gate_id", "")) for row in rows}
    required_gate_ids = {
        "ARXIV_JOURNAL_READINESS_NOT_CLAY_PRIZE_SUBMISSION",
        "TWO_YEAR_COMMUNITY_ACCEPTANCE_EXTERNAL",
        "NO_DIRECT_CMI_MANUSCRIPT_SUBMISSION_CLAIM",
    }
    bad_rows = [
        str(row.get("gate_id", "<unknown>"))
        for row in rows
        if (
            row.get("governance_owner") != "external"
            or row.get("internal_readiness_promotes_clay") is not False
            or row.get("clay_prize_submission_claim") is not False
            or row.get("fail_closed") is not True
        )
    ]
    scan_paths = [
        *LIVE_PAPER_FILES,
        Path("Docs/papers/PublicationRoadmap.md"),
        Path("Docs/support/live/SupportCompendium.md"),
    ]
    forbidden_hits = forbidden_clay_publication_hits(repo_root, scan_paths)
    return [
        CheckResult(
            "clay-publication-governance-rows-present",
            required_gate_ids <= gate_ids,
            ", ".join(sorted(gate_ids)),
        ),
        CheckResult("clay-publication-governance-fail-closed", not bad_rows, "; ".join(bad_rows)),
        CheckResult(
            "clay-publication-forbidden-promotion-claims",
            not forbidden_hits,
            "; ".join(forbidden_hits),
        ),
    ]


def normalize_obligation_text(text: str) -> str:
    return " ".join(text.lower().replace("`", "").replace("_", " ").split())


def check_paper_upgrade_obligations(repo_root: Path) -> list[CheckResult]:
    results: list[CheckResult] = []
    for name, sources in PAPER_UPGRADE_OBLIGATION_SOURCES.items():
        texts = []
        missing_sources = []
        for source in sources:
            full = repo_root / source
            if not full.exists():
                missing_sources.append(source.as_posix())
                continue
            texts.append(full.read_text(encoding="utf-8"))
        corpus = normalize_obligation_text("\n".join(texts))
        missing_groups = []
        for group_name, phrases in PAPER_UPGRADE_OBLIGATION_GROUPS[name]:
            if not any(phrase in corpus for phrase in phrases):
                missing_groups.append(group_name)
        detail_parts = [*missing_sources, *missing_groups]
        results.append(CheckResult(name, not detail_parts, "; ".join(detail_parts)))
    return results


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
        *check_clay_publication_governance(repo_root),
        *check_paper_upgrade_obligations(repo_root),
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

#!/usr/bin/env python3
"""Validate the local publication-readiness support packet for Papers 1, 3, and 8."""

from __future__ import annotations

import argparse
import ast
import os
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

CORE_MANUSCRIPT_FILES = (
    Path("Docs/papers/live/Paper1NavierStokesClayDraft.md"),
    Path("Docs/papers/live/Paper3YangMillsClayDraft.md"),
    Path("Docs/papers/live/Paper8UnificationDraft.md"),
)

CITATION_LEDGER = Path("Docs/support/live/PaperCommonCitationLedger.md")
RENDERER_SCRIPT = Path("scripts/render_core_paper_pdfs.py")
AGDA_BIN = os.environ.get("AGDA_BIN")


def _resolve_agda_bin() -> str:
    if AGDA_BIN:
        return AGDA_BIN
    try:
        completed = subprocess.run(
            ["nix", "build", "--no-link", "--print-out-paths", "/home/c/Documents/code/agda#debug.bin"],
            capture_output=True,
            text=True,
            check=False,
        )
        if completed.returncode == 0:
            candidate = Path((completed.stdout or "").strip()) / "bin" / "agda"
            if candidate.is_file():
                return str(candidate)
    except FileNotFoundError:
        pass
    return "agda"


AGDA_BIN = _resolve_agda_bin()

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
    "clay-certified",
    "clay certified",
    "cmi-approved",
    "cmi approved",
    "cmi-certified",
    "cmi certified",
    "millennium prize solved",
    "officially solved",
    "we have solved",
    "this solves navier-stokes",
    "this solves yang-mills",
    "solution of the navier-stokes millennium problem",
    "solution of the yang-mills millennium problem",
)

AUTHOR_PLACEHOLDER_PATTERNS = (
    re.compile(r"pending\s+final\s+public\s+author\s+list", re.IGNORECASE),
    re.compile(r"\b(?:tbd|todo)\b.{0,30}\bauthor", re.IGNORECASE),
    re.compile(r"\bauthor\b.{0,30}\b(?:tbd|todo)\b", re.IGNORECASE),
    re.compile(r"author\s*:\s*(?:pending|tbd|todo|dashi\s+project)\s*$", re.IGNORECASE | re.MULTILINE),
)

PUBLIC_CITATION_PLACEHOLDERS = (
    "see common citation ledger",
    "common citation ledger",
    "citation ledger placeholder",
    "internal citation ledger",
    "ledger entry pending",
    "formatted reference pending",
)

LIVE_CITATION_KEY_RE = re.compile(r"`([A-Za-z][A-Za-z0-9]+(?:[A-Za-z0-9-]*[A-Za-z0-9])?)`")

BALABAN_OPTION_B_GATE_MARKERS = ("B1", "B2", "B3", "B4", "B5")
BALABAN_OPTION_B_GATE_ALIASES = {
    "B1": ("casimir suppression",),
    "B2": ("polymer localization",),
    "B3": ("kotecky preiss activity bound", "kotecky preiss", "kp activity bound"),
    "B4": ("trace norm consequence", "trace norm transfer"),
    "B5": ("intermediate beta rg induction", "intermediate beta", "rg induction"),
}
BALABAN_OPTION_B_ALLOWED_STATUS_TOKENS = (
    "false",
    "open",
    "deferred",
    "non promoting",
    "non promotion",
    "boundary",
    "diagnostic",
    "not promoted",
)
BALABAN_OPTION_B_FORBIDDEN_STATUS_TOKENS = (
    "true",
    "proved",
    "closed",
    "promoted",
    "promotion allowed",
    "clay promoted",
    "mass gap promoted",
)
BALABAN_OPTION_B_OPTIONAL_SCRIPTS = (
    Path("scripts/ym_option_b_gap_audit.py"),
    Path("scripts/ym_balaban_constant_diagnostic.py"),
)

MISSING_MATH_MASTER_FRONTIER_ROWS = (
    {
        "name": "ns-a1-a3-abel-stationarity-frontier",
        "paper": "Paper1 NS",
        "terms": (
            ("publishableclaimtext", "seregin ess", "a3", "unpromoted"),
            ("thetaless thanoneanalyticestimateprovedhere", "analytic theta 1 estimate", "not proved"),
        ),
    },
    {
        "name": "ns-a4-defect-wall-frontier",
        "paper": "Paper1 NS",
        "terms": (
            ("hminushalfnonlineardefectboundwithoutcircularity", "open"),
            ("dangershellmaximumprincipleopen", "open"),
        ),
    },
    {
        "name": "ym-h3a-balaban-frontier",
        "paper": "Paper3 YM",
        "terms": (
            ("balaban rg h3a frontier", "open frontier"),
            ("option b b3 kotecky preiss activity bound", "false"),
        ),
    },
    {
        "name": "uct-cross-term-nullity-frontier",
        "paper": "Paper8 Unification",
        "terms": (
            ("u 1a h decomposition blocker", "false"),
            ("cross term nullity discriminant proof guard", "false"),
        ),
    },
)

MISSING_MATH_MASTER_FRONTIER_ALLOWED_STATUSES = {
    "authority-intake-boundary",
    "conditional",
    "diagnostic",
    "false",
    "open",
    "open-frontier",
    "target-only",
}

MISSING_MATH_MASTER_FRONTIER_OPTIONAL_SCRIPTS = (
    Path("scripts/missing_math_master_agenda.py"),
    Path("scripts/ns_abel_defect_measure_agenda.py"),
)

MISSING_MATH_MASTER_FRONTIER_LIVE_WALLS = (
    {
        "name": "paper1-live-wall",
        "path": Path("Docs/papers/live/Paper1NavierStokesClayDraft.md"),
        "groups": (
            ("a1-a3-frontier", ("a1 a3", "live mathematical wall")),
            ("abel-stationarity", ("abel weighted triadic", "stationarity")),
            ("a4-frontier", ("a4", "actual theorem walls")),
            ("ckn-bkm-boundary", ("ckn bkm", "global regularity")),
        ),
    },
    {
        "name": "paper3-live-wall",
        "path": Path("Docs/papers/live/Paper3YangMillsClayDraft.md"),
        "groups": (
            ("h3a-frontier", ("h3a", "frontier")),
            ("balaban-frontier", ("balaban centered", "load bearing frontier")),
            ("os-wightman-wall", ("os wightman", "reconstruction")),
            ("mass-gap-boundary", ("continuum mass gap", "clay")),
        ),
    },
    {
        "name": "paper8-live-wall",
        "path": Path("Docs/papers/live/Paper8UnificationDraft.md"),
        "groups": (
            ("uct-1-4-frontier", ("uct 1 uct 4", "live mathematical wall")),
            ("cross-term-nullity", ("cross term nullity", "unique continuation")),
            ("downstream-locked", ("uct 5 uct 8", "locked")),
            ("terminal-boundary", ("terminal unification guard remains false",)),
        ),
    },
)

THEOREM_AGENDA_SCRIPTS = (
    {
        "name": "missing-math-master-agenda",
        "path": Path("scripts/missing_math_master_agenda.py"),
        "command": ("--format", "json"),
        "id_key": "task_id",
        "required_ids": tuple(
            [f"NS-{index}" for index in range(1, 11)]
            + [f"YM-{index}" for index in range(1, 11)]
            + [f"UCT-{index}" for index in range(1, 11)]
        ),
        "source_markers": (
            "promotion_allowed",
            "clay_promotion",
            "terminal_promotion",
            "fail-closed",
        ),
    },
    {
        "name": "ns-abel-defect-measure-agenda",
        "path": Path("scripts/ns_abel_defect_measure_agenda.py"),
        "command": ("--format", "json", "--max-evidence-files", "2"),
        "id_key": "marker",
        "required_ids": ("A1.1", "A1.2", "A1.3", "A3.1", "A3.2", "A3.3", "A3.4"),
        "source_markers": (
            "boundary_or_agenda_only_not_proved",
            "pde_measure_constructed",
            "stationarity_proved",
            "clay_promotion",
        ),
    },
    {
        "name": "ym-option-b-gap-audit",
        "path": Path("scripts/ym_option_b_gap_audit.py"),
        "command": ("--format", "json"),
        "id_key": "gate_id",
        "required_ids": ("B1", "B2", "B3", "B4", "B5"),
        "source_markers": (
            "promotion_allowed",
            "clay_promotion",
            "recorded_boundary_blocked",
            "missing_gate_id_fail_closed",
        ),
    },
    {
        "name": "ns-missing-math-theorem-agenda",
        "path": Path("scripts/ns_missing_math_theorem_agenda.py"),
        "command": ("--format", "json"),
        "id_key": "theorem_id",
        "required_ids": ("NS-A", "NS-B", "NS-C", "NS-D", "NS-E"),
        "source_markers": (
            "AbelTriadicDefectMeasureConstruction",
            "NSTypeIBlowupKappaBiasBound",
            "PointwiseToAbelStretchingTransfer",
            "promotion_allowed",
            "clay_promotion",
            "fail_closed",
        ),
    },
    {
        "name": "ym-missing-math-theorem-agenda",
        "path": Path("scripts/ym_missing_math_theorem_agenda.py"),
        "command": ("--format", "json"),
        "id_key": "theorem_id",
        "required_ids": ("YM-A", "YM-B", "YM-C", "YM-D", "YM-E"),
        "source_markers": (
            "HamiltonianDominatesDefectPlusHolonomy",
            "H3aTraceNormTransfer",
            "NoSpectralPollutionBelowFiniteMargin",
            "promotion_allowed",
            "clay_promotion",
            "fail_closed",
        ),
    },
    {
        "name": "uct-missing-math-theorem-agenda",
        "path": Path("scripts/uct_missing_math_theorem_agenda.py"),
        "command": ("--format", "json"),
        "id_key": "id",
        "required_ids": ("UCT-A", "UCT-B", "UCT-C", "UCT-D", "UCT-E", "UCT-F", "UCT-G", "UCT-H"),
        "source_markers": (
            "OverlapResidualPDE",
            "CrossTermNullity",
            "JordanVonNeumannRecovery",
            "promotion_allowed",
            "terminal_promotion",
            "fail_closed",
        ),
    },
    {
        "name": "full-missing-math-theorem-agenda",
        "path": Path("scripts/full_missing_math_theorem_agenda.py"),
        "command": ("--format", "json"),
        "id_key": "theorem_id",
        "required_ids": (
            "NS-A",
            "NS-B",
            "NS-C",
            "NS-D",
            "NS-E",
            "YM-A",
            "YM-B",
            "YM-C",
            "YM-D",
            "YM-E",
            "UCT-A",
            "UCT-B",
            "UCT-C",
            "UCT-D",
            "UCT-E",
            "UCT-F",
            "UCT-G",
            "UCT-H",
        ),
        "source_markers": (
            "EXPECTED_COUNTS",
            "NS",
            "YM",
            "UCT",
            "promotion_allowed",
            "clay_promotion",
            "terminal_promotion",
        ),
    },
)

THEOREM_AGENDA_RECEIPTS = (
{
    "name": "missing-math-master-frontier-receipt",
    "path": Path("DASHI/Physics/Closure/MissingMathMasterFrontierReceipt.agda"),
    "required_anchors": (
        "canonicalMissingMathMasterFrontierReceipt",
        "canonicalNSGateCodes",
        "canonicalYMGateCodes",
        "canonicalUCTGateCodes",
        "nsPromotionFlag",
        "ymPromotionFlag",
        "unificationPromotionFlag",
        "promotionFlagIsFalse",
        "failClosedIsTrue",
        "missingMathMasterFrontierSummary",
    ),
    "required_false_fields": (
        "promotionFlag",
        "nsPromotionFlag",
        "ymPromotionFlag",
        "unificationPromotionFlag",
    ),
    "required_true_fields": ("failClosed",),
    "required_gate_tokens": (
        "AbelTriadicDefectMeasureConstruction",
        "ApproximateTransferOperatorStationarity",
        "H3aTraceNormTransfer",
        "NoSpectralPollutionBelowFiniteMargin",
        "UCT1",
        "UCT4",
        "UCT8",
    ),
},
{
    "name": "full-missing-math-theorem-agenda-receipt",
    "path": Path("DASHI/Physics/Closure/FullMissingMathTheoremAgendaBoundary.agda"),
    "required_anchors": (
        "canonicalFullMissingMathTheoremAgendaBoundary",
        "fullAgendaFailClosedIsTrue",
        "allPromotionFlagsFalse",
        "nsCDependsOnNSA",
        "nsEDependsOnNSAToNSD",
        "ymCDependsOnYMB",
        "ymDDependsOnYMB",
        "uctHDependsOnUCTDChain",
    ),
    "required_false_fields": (
        "promotionAllowed",
        "clayPromotion",
        "terminalPromotion",
    ),
    "required_true_fields": ("failClosed",),
    "required_gate_tokens": (
        "AbelTriadicDefectMeasureConstruction",
        "HamiltonianDominatesDefectPlusHolonomy",
        "H3aTraceNormTransfer",
        "OverlapResidualPDE",
        "CrossTermNullity",
        "JordanVonNeumannRecovery",
    ),
},
)

THEOREM_PACKET_MANIFEST_EXPECTATIONS = (
    ("Paper1 NS", "Missing-math master: NS A1/A3 Abel stationarity", "candidateAbelRateNotDerived", "open"),
    ("Paper1 NS", "Missing-math master: NS A4 support transfer", "A4LeiRenTianFourierOutputCouplingProved", "false"),
    ("Paper1 NS", "Missing-math master: NS A5 kappa-bias", "a5BiasVanishingTheoremProved", "false"),
    ("Paper1 NS", "Missing-math master: NS A6 pointwise-to-Abel", "compositeA6BoundaryDoesNotProveNSClay", "downstream-locked"),
    ("Paper3 YM", "Missing-math master: YM finite domination", "noClayPromotionFromYMBochnerWeitzenbockBoundary", "downstream-locked"),
    ("Paper3 YM", "Missing-math master: YM H3a", "ymH3aContinuumIntakeKeepsClayFalse", "authority-intake"),
    ("Paper3 YM", "Missing-math master: YM H3b", "ymH3bBoundaryPromotionImpossibleHere", "open"),
    ("Paper3 YM", "Missing-math master: YM no spectral pollution", "YMNoSpectralPollutionToOSWightmanSocketCompositeProved", "false"),
    ("Paper3 YM", "Missing-math master: YM RP/OS/Wightman", "YMThermodynamicOSWightmanOperatorBoundaryClosesNothing", "downstream-locked"),
    ("Paper8 Unification", "Missing-math master: UCT.1 residual PDE", "uct1ResidualPDESpecificationRecorded", "open"),
    ("Paper8 Unification", "Missing-math master: UCT.2 operator class", "uct2EllipticityOrParabolicityClassRecorded", "open"),
    ("Paper8 Unification", "Missing-math master: UCT.3 Carleman intake", "uct3CarlemanUniqueContinuationRecorded", "authority-intake"),
    ("Paper8 Unification", "Missing-math master: UCT.4 cross-term nullity", "uct4ActualTheoremTargetRecorded", "open"),
    ("Paper8 Unification", "Missing-math master: UCT.5 modulo-null linearity", "moduloNullLinearityConsumer", "downstream-locked"),
    ("Paper8 Unification", "Missing-math master: UCT.6 four-point cancellation", "fourPointConsumer", "downstream-locked"),
    ("Paper8 Unification", "Missing-math master: UCT.7 parallelogram", "parallelogramConsumer", "downstream-locked"),
    ("Paper8 Unification", "Missing-math master: UCT.8 Jordan-von Neumann", "jordanVonNeumannAdapterConsumer", "downstream-locked"),
)

EXPECTED_INTAKE_TEXT = (
    {
        "name": "paper1-seregin-ess-authority-intake",
        "path": Path("Docs/papers/live/Paper1NavierStokesClayDraft.md"),
        "required": (
            "Seregin2012",
            "ESS2003",
            "Type-I",
            "ancient",
            "L^{3,\\infty}",
            "A3.2",
            "A3.3",
            "r^(1/12)",
            "not derived",
        ),
    },
    {
        "name": "paper1-route-compatibility-intake",
        "path": Path("Docs/papers/live/Paper1NavierStokesClayDraft.md"),
        "required": (
            "Route compatibility",
            "Sprint164",
            "tail-flux",
            "Abel",
            "separate",
        ),
    },
    {
        "name": "paper3-balaban-option-a-intake",
        "path": Path("Docs/papers/live/Paper3YangMillsClayDraft.md"),
        "required": (
            "Balaban1988",
            "Lemma 3",
            "activity bound",
            "polymer",
            "summability",
            "trace-norm",
            "H3a",
        ),
    },
    {
        "name": "paper3-option-b-deferred-intake",
        "path": Path("Docs/papers/live/Paper3YangMillsClayDraft.md"),
        "required": (
            "Option-B",
            "deferred",
            "companion Option-B paper",
            "repo-native",
            "polymer",
        ),
    },
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
        ("balaban-1988-lemma-3", ("balaban1988 lemma 3", "balaban 1988 lemma 3")),
        ("activity-bound", ("activity bound",)),
        ("polymer-summability", ("polymer summability",)),
        ("trace-norm", ("trace norm", "trace-norm")),
        (
            "option-b-deferred",
            ("option b deferred", "repo native alternative is explicitly deferred", "companion option b paper"),
        ),
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


def check_public_manuscript_author_lines(repo_root: Path) -> list[CheckResult]:
    missing = []
    placeholders = []
    for path in CORE_MANUSCRIPT_FILES:
        full = repo_root / path
        if not full.exists():
            missing.append(path.as_posix())
            continue
        text = full.read_text(encoding="utf-8", errors="replace")
        author_match = re.search(r"^Author:\s*(.+?)\s*$", text, re.MULTILINE)
        if not author_match:
            missing.append(path.as_posix())
            continue
        author = author_match.group(1).strip().strip("`")
        if not author or any(pattern.search(f"Author: {author}") for pattern in AUTHOR_PLACEHOLDER_PATTERNS):
            placeholders.append(f"{path.as_posix()}:Author:{author or '<empty>'}")
        for pattern in AUTHOR_PLACEHOLDER_PATTERNS:
            for hit in pattern.finditer(text):
                line = text.count("\n", 0, hit.start()) + 1
                location = f"{path.as_posix()}:{line}:{hit.group(0).strip()}"
                if location not in placeholders:
                    placeholders.append(location)
    return [
        CheckResult("public-manuscript-author-lines-present", not missing, "; ".join(missing)),
        CheckResult("public-manuscript-author-placeholders-absent", not placeholders, "; ".join(placeholders)),
    ]


def check_public_citation_placeholders(repo_root: Path) -> list[CheckResult]:
    hits = []
    for path in CORE_MANUSCRIPT_FILES:
        full = repo_root / path
        if not full.exists():
            continue
        text = full.read_text(encoding="utf-8", errors="replace")
        lowered = text.lower()
        for phrase in PUBLIC_CITATION_PLACEHOLDERS:
            start = 0
            while True:
                index = lowered.find(phrase, start)
                if index == -1:
                    break
                line = text.count("\n", 0, index) + 1
                hits.append(f"{path.as_posix()}:{line}:{phrase}")
                start = index + len(phrase)
    return [CheckResult("public-citation-ledger-placeholders-absent", not hits, "; ".join(hits))]


def ledger_keys(repo_root: Path) -> set[str]:
    path = repo_root / CITATION_LEDGER
    if not path.exists():
        return set()
    keys = set()
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if not line.startswith("| `"):
            continue
        cells = [cell.strip() for cell in line.strip().strip("|").split("|")]
        if cells:
            keys.add(cells[0].strip("`"))
    return keys


def renderer_bib_keys(repo_root: Path) -> tuple[set[str], str | None]:
    path = repo_root / RENDERER_SCRIPT
    if not path.exists():
        return set(), f"{RENDERER_SCRIPT.as_posix()} missing"
    try:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=path.as_posix())
    except SyntaxError as exc:
        return set(), f"{RENDERER_SCRIPT.as_posix()}: {exc}"
    for node in tree.body:
        if not isinstance(node, ast.Assign):
            continue
        if not any(isinstance(target, ast.Name) and target.id == "BIB_ENTRIES" for target in node.targets):
            continue
        try:
            value = ast.literal_eval(node.value)
        except (ValueError, SyntaxError) as exc:
            return set(), f"{RENDERER_SCRIPT.as_posix()}: BIB_ENTRIES not literal: {exc}"
        if not isinstance(value, dict):
            return set(), f"{RENDERER_SCRIPT.as_posix()}: BIB_ENTRIES must be a dict"
        return {str(key) for key in value.keys()}, None
    return set(), f"{RENDERER_SCRIPT.as_posix()}: BIB_ENTRIES not found"


def check_renderer_bibliography_entries(repo_root: Path) -> list[CheckResult]:
    known_ledger_keys = ledger_keys(repo_root)
    renderer_keys, renderer_error = renderer_bib_keys(repo_root)
    live_keys: set[str] = set()
    for path in CORE_MANUSCRIPT_FILES:
        full = repo_root / path
        if not full.exists():
            continue
        text = full.read_text(encoding="utf-8", errors="replace")
        live_keys.update(key for key in LIVE_CITATION_KEY_RE.findall(text) if key in known_ledger_keys)
    missing_ledger = sorted(key for key in live_keys if key not in known_ledger_keys)
    missing_renderer = sorted(key for key in live_keys if key not in renderer_keys)
    return [
        CheckResult("live-citation-keys-have-ledger-rows", not missing_ledger, "; ".join(missing_ledger)),
        CheckResult(
            "live-citation-keys-have-renderer-bib-entries",
            renderer_error is None and not missing_renderer,
            renderer_error or "; ".join(missing_renderer),
        ),
    ]


def check_expected_intake_text(repo_root: Path) -> list[CheckResult]:
    results = []
    for obligation in EXPECTED_INTAKE_TEXT:
        path = obligation["path"]
        full = repo_root / path
        if not full.exists():
            results.append(CheckResult(str(obligation["name"]), False, f"{path.as_posix()} missing"))
            continue
        text = normalize_obligation_text(full.read_text(encoding="utf-8", errors="replace"))
        missing = [
            phrase
            for phrase in obligation["required"]
            if normalize_obligation_text(str(phrase)) not in text
        ]
        results.append(CheckResult(str(obligation["name"]), not missing, "; ".join(str(item) for item in missing)))
    return results


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
    return " ".join(re.sub(r"[^a-z0-9]+", " ", text.lower()).split())


def row_text(row: dict[str, object]) -> str:
    return " ".join(str(value) for value in row.values())


def row_matches_terms(row: dict[str, object], terms: tuple[str, ...]) -> bool:
    normalized = normalize_obligation_text(row_text(row))
    return all(normalize_obligation_text(term) in normalized for term in terms)


def json_walk(value: object) -> list[object]:
    values = [value]
    if isinstance(value, dict):
        for item in value.values():
            values.extend(json_walk(item))
    elif isinstance(value, list):
        for item in value:
            values.extend(json_walk(item))
    return values


def first_json_value(text: str) -> object:
    decoder = json.JSONDecoder()
    for index, char in enumerate(text):
        if char not in "[{":
            continue
        try:
            value, _ = decoder.raw_decode(text[index:])
        except json.JSONDecodeError:
            continue
        return value
    raise ValueError("no JSON object or array found")


def values_for_key(payload: object, key_name: str) -> set[str]:
    values = set()
    for item in json_walk(payload):
        if isinstance(item, dict) and key_name in item:
            values.add(str(item[key_name]))
    return values


def promoting_json_fields(payload: object) -> list[str]:
    bad: list[str] = []
    for item in json_walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            key_lower = str(key).lower()
            if isinstance(value, bool) and value is True:
                if (
                    ("promotion" in key_lower or "promoted" in key_lower)
                    and not any(
                        safe in key_lower
                        for safe in ("no_", "non_", "block", "forbidden", "false", "fail_closed")
                    )
                ):
                    bad.append(f"{key}=true")
            if isinstance(value, str):
                value_lower = value.lower()
                if key_lower.endswith("status") or "proof_status" in key_lower:
                    if value_lower in {"true", "proved", "promoted", "promotion_allowed"}:
                        bad.append(f"{key}={value}")
                    if any(token in value_lower for token in ("proved", "promoted")) and not any(
                        safe in value_lower
                        for safe in (
                            "not",
                            "no",
                            "non",
                            "false",
                            "blocked",
                            "boundary",
                            "fail",
                            "diagnostic",
                        )
                    ):
                        bad.append(f"{key}={value}")
    return bad


def run_theorem_agenda_script(
    repo_root: Path,
    path: Path,
    command_args: tuple[str, ...],
) -> tuple[object | None, str | None]:
    proc = subprocess.run(
        [sys.executable, str(repo_root / path), *command_args],
        cwd=repo_root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if proc.returncode != 0:
        detail = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else "nonzero exit"
        return None, detail
    try:
        return first_json_value(proc.stdout), None
    except ValueError as exc:
        return None, str(exc)


def agda_field_assignment(text: str, field_name: str, value: str) -> bool:
    lines = text.splitlines()
    field_pattern = re.compile(rf"^\s*;?\s*{re.escape(field_name)}\s*=\s*(?P<rest>\S*)\s*$")
    for index, line in enumerate(lines):
        match = field_pattern.match(line)
        if match is None:
            continue
        rest = match.group("rest")
        if rest == value:
            return True
        for next_line in lines[index + 1 :]:
            stripped = next_line.strip()
            if not stripped:
                continue
            return stripped == value
    return False


def check_theorem_agenda_surfaces(repo_root: Path) -> list[CheckResult]:
    results: list[CheckResult] = []
    for script in THEOREM_AGENDA_SCRIPTS:
        name = str(script["name"])
        path = script["path"]
        assert isinstance(path, Path)
        full = repo_root / path
        if not full.exists():
            results.append(CheckResult(f"theorem-agenda-script-exists:{name}", False, path.as_posix()))
            results.append(CheckResult(f"theorem-agenda-source-contract:{name}", False, "missing script"))
            results.append(CheckResult(f"theorem-agenda-output-contract:{name}", False, "missing script"))
            continue

        source_text = full.read_text(encoding="utf-8", errors="replace")
        required_ids = tuple(str(item) for item in script["required_ids"])
        source_missing = [
            item for item in (*required_ids, *tuple(str(marker) for marker in script["source_markers"]))
            if item not in source_text
        ]
        results.append(CheckResult(f"theorem-agenda-script-exists:{name}", True, path.as_posix()))
        results.append(
            CheckResult(
                f"theorem-agenda-source-contract:{name}",
                not source_missing,
                "; ".join(source_missing),
            )
        )

        payload, error = run_theorem_agenda_script(
            repo_root,
            path,
            tuple(str(item) for item in script["command"]),
        )
        if error is not None:
            results.append(CheckResult(f"theorem-agenda-output-contract:{name}", False, error))
            continue
        observed_ids = values_for_key(payload, str(script["id_key"]))
        output_missing = [item for item in required_ids if item not in observed_ids]
        promoting_fields = promoting_json_fields(payload)
        results.append(
            CheckResult(
                f"theorem-agenda-output-contract:{name}",
                not output_missing and not promoting_fields,
                "; ".join([*output_missing, *promoting_fields[:10]]),
            )
        )

    for receipt in THEOREM_AGENDA_RECEIPTS:
        receipt_path = receipt["path"]
        assert isinstance(receipt_path, Path)
        receipt_full = repo_root / receipt_path
        receipt_name = str(receipt["name"])
        if not receipt_full.exists():
            results.append(CheckResult(f"theorem-agenda-receipt-exists:{receipt_name}", False, receipt_path.as_posix()))
            results.append(CheckResult(f"theorem-agenda-receipt-contract:{receipt_name}", False, "missing receipt"))
            continue

        receipt_text = receipt_full.read_text(encoding="utf-8", errors="replace")
        missing_anchors = [
            str(anchor)
            for anchor in (
                *receipt["required_anchors"],
                *receipt["required_gate_tokens"],
            )
            if str(anchor) not in receipt_text
        ]
        wrong_false = [
            str(field)
            for field in receipt["required_false_fields"]
            if not agda_field_assignment(receipt_text, str(field), "false")
        ]
        wrong_true = [
            str(field)
            for field in receipt["required_true_fields"]
            if not agda_field_assignment(receipt_text, str(field), "true")
        ]
        results.append(CheckResult(f"theorem-agenda-receipt-exists:{receipt_name}", True, receipt_path.as_posix()))
        results.append(
            CheckResult(
                f"theorem-agenda-receipt-contract:{receipt_name}",
                not missing_anchors and not wrong_false and not wrong_true,
                "; ".join([*missing_anchors, *[f"{field}=false" for field in wrong_false], *[f"{field}=true" for field in wrong_true]]),
            )
        )
    return results


def check_theorem_packet_manifest_rows(payload: dict[str, object] | None) -> list[CheckResult]:
    rows = payload.get("rows") if payload is not None else None
    if not isinstance(rows, list):
        return [CheckResult("theorem-packet-manifest-exact-rows", False, "rows must be a list")]

    rows_by_key: dict[tuple[str, str, str], dict[str, object]] = {}
    for row in rows:
        if not isinstance(row, dict):
            continue
        key = (str(row.get("paper", "")), str(row.get("lemma", "")), str(row.get("exact_var", "")))
        rows_by_key[key] = row

    missing = []
    promoted = []
    for paper, lemma, exact_var, expected_status in THEOREM_PACKET_MANIFEST_EXPECTATIONS:
        row = rows_by_key.get((paper, lemma, exact_var))
        if row is None:
            missing.append(f"{paper}:{lemma}:{exact_var}")
            continue
        actual_status = str(row.get("expected_status", ""))
        note = str(row.get("governance_note", "")).lower()
        if actual_status != expected_status:
            promoted.append(f"{lemma}:{actual_status}")
            continue
        status_lower = actual_status.lower()
        if status_lower in {"true", "proved", "promoted"}:
            promoted.append(f"{lemma}:{actual_status}")
        if not any(token in note for token in ("block", "false", "cannot", "non-promot", "unpromot", "locked", "open")):
            promoted.append(f"{lemma}:missing-governance-guard")

    return [
        CheckResult(
            "theorem-packet-manifest-exact-rows",
            not missing,
            "; ".join(missing),
        ),
        CheckResult(
            "theorem-packet-manifest-nonpromoting-statuses",
            not promoted,
            "; ".join(promoted),
        ),
    ]


def missing_math_master_frontier_rows(rows: list[object]) -> dict[str, list[dict[str, object]]]:
    selected: dict[str, list[dict[str, object]]] = {}
    for requirement in MISSING_MATH_MASTER_FRONTIER_ROWS:
        paper = requirement["paper"]
        name = str(requirement["name"])
        term_groups = requirement["terms"]
        matches = []
        for row in rows:
            if not isinstance(row, dict) or row.get("paper") != paper:
                continue
            if any(row_matches_terms(row, tuple(group)) for group in term_groups):
                matches.append(row)
        selected[name] = matches
    return selected


def check_missing_math_master_frontier(
    payload: dict[str, object] | None,
    repo_root: Path,
) -> list[CheckResult]:
    rows = payload.get("rows") if payload is not None else None
    if not isinstance(rows, list):
        return [CheckResult("missing-math-master-frontier-manifest-rows-present", False, "rows must be a list")]

    selected = missing_math_master_frontier_rows(rows)
    missing_row_groups = [name for name, matches in selected.items() if not matches]
    results = [
        CheckResult(
            "missing-math-master-frontier-manifest-rows-present",
            not missing_row_groups,
            "; ".join(missing_row_groups),
        )
    ]

    unsafe_statuses = []
    for name, matches in selected.items():
        for row in matches:
            status = str(row.get("expected_status", ""))
            if status not in MISSING_MATH_MASTER_FRONTIER_ALLOWED_STATUSES:
                unsafe_statuses.append(f"{name}:{row.get('lemma', '<unknown>')}:{status}")
    results.append(
        CheckResult(
            "missing-math-master-frontier-statuses-nonpromoting",
            not unsafe_statuses,
            "; ".join(unsafe_statuses),
        )
    )

    script_failures = []
    present_scripts = []
    for path in MISSING_MATH_MASTER_FRONTIER_OPTIONAL_SCRIPTS:
        full = repo_root / path
        if not full.exists():
            continue
        present_scripts.append(path.as_posix())
        text = normalize_obligation_text(full.read_text(encoding="utf-8", errors="replace"))
        has_diagnostic = any(
            phrase in text
            for phrase in (
                "diagnostic",
                "audit",
                "agenda",
                "fail closed",
                "frontier",
                "missing theorem",
            )
        )
        has_non_promotion = any(
            phrase in text
            for phrase in (
                "non promoting",
                "non promotion",
                "no promotion",
                "not promote",
                "does not promote",
                "cannot promote",
                "promotion false",
                "promotion remains false",
            )
        )
        if not has_diagnostic or not has_non_promotion:
            missing = []
            if not has_diagnostic:
                missing.append("diagnostic")
            if not has_non_promotion:
                missing.append("non-promotion")
            script_failures.append(f"{path.as_posix()}:{','.join(missing)}")
    results.append(
        CheckResult(
            "missing-math-master-frontier-optional-scripts-diagnostic-nonpromotion",
            not script_failures,
            "; ".join(script_failures) if script_failures else ", ".join(present_scripts) or "optional scripts absent",
        )
    )

    live_wall_failures = []
    for paper in MISSING_MATH_MASTER_FRONTIER_LIVE_WALLS:
        path = paper["path"]
        full = repo_root / path
        if not full.exists():
            live_wall_failures.append(f"{path.as_posix()}:missing")
            continue
        corpus = normalize_obligation_text(full.read_text(encoding="utf-8", errors="replace"))
        for group_name, phrases in paper["groups"]:
            if not all(normalize_obligation_text(phrase) in corpus for phrase in phrases):
                live_wall_failures.append(f"{paper['name']}:{group_name}")
    results.append(
        CheckResult(
            "missing-math-master-frontier-live-walls-in-papers",
            not live_wall_failures,
            "; ".join(live_wall_failures),
        )
    )
    return results


def option_b_manifest_rows(rows: list[object]) -> list[dict[str, object]]:
    selected = []
    gate_markers = {marker.lower() for marker in BALABAN_OPTION_B_GATE_MARKERS}
    for row in rows:
        if not isinstance(row, dict):
            continue
        if row.get("paper") != "Paper3 YM":
            continue
        normalized = normalize_obligation_text(row_text(row))
        words = set(normalized.split())
        if "option b" in normalized or gate_markers & words:
            selected.append(row)
    return selected


def has_option_b_gate(text: str, marker: str) -> bool:
    normalized = normalize_obligation_text(text)
    words = set(normalized.split())
    return marker.lower() in words or any(
        normalize_obligation_text(alias) in normalized
        for alias in BALABAN_OPTION_B_GATE_ALIASES[marker]
    )


def check_balaban_option_b_readiness(payload: dict[str, object] | None, repo_root: Path) -> list[CheckResult]:
    results: list[CheckResult] = []
    rows = payload.get("rows") if payload is not None else None
    option_b_rows = option_b_manifest_rows(rows) if isinstance(rows, list) else []
    manifest_text = "\n".join(row_text(row) for row in option_b_rows)
    missing_manifest_gates = [
        marker for marker in BALABAN_OPTION_B_GATE_MARKERS if marker.lower() not in set(normalize_obligation_text(manifest_text).split())
    ]
    results.append(
        CheckResult(
            "balaban-option-b-manifest-b1-b5-gates-present",
            not missing_manifest_gates,
            "; ".join(missing_manifest_gates),
        )
    )

    unsafe_rows = []
    for row in option_b_rows:
        row_normalized = normalize_obligation_text(row_text(row))
        expected_status = normalize_obligation_text(str(row.get("expected_status", "")))
        status_is_safe = any(token in row_normalized for token in BALABAN_OPTION_B_ALLOWED_STATUS_TOKENS)
        status_is_promoting = any(token in expected_status for token in BALABAN_OPTION_B_FORBIDDEN_STATUS_TOKENS)
        if not status_is_safe or status_is_promoting:
            unsafe_rows.append(str(row.get("lemma", "<unknown>")))
    option_b_corpus = normalize_obligation_text(manifest_text)
    option_b_boundary_markers = {
        "non-promoting": any(
            marker in option_b_corpus
            for marker in (
                "non promoting",
                "non promotion",
                "not promoted",
                "no promotion",
                "cannot promote",
                "does not convert",
                "unpromoted",
                "promotion remain blocked",
                "promotion remains blocked",
                "not a clay authority",
            )
        ),
        "false": "false" in set(option_b_corpus.split()),
        "open-or-deferred": "open" in set(option_b_corpus.split()) or "deferred" in set(option_b_corpus.split()),
    }
    missing_boundary_markers = [
        name for name, present in option_b_boundary_markers.items() if not present
    ]
    results.append(
        CheckResult(
            "balaban-option-b-manifest-nonpromoting-false-open",
            bool(option_b_rows) and not unsafe_rows and not missing_boundary_markers,
            "; ".join([*unsafe_rows, *missing_boundary_markers]),
        )
    )

    paper3_path = Path("Docs/papers/live/Paper3YangMillsClayDraft.md")
    paper3_full = repo_root / paper3_path
    if not paper3_full.exists():
        results.append(CheckResult("balaban-option-b-paper3-deferral-and-five-gates", False, f"{paper3_path.as_posix()} missing"))
    else:
        paper3_text = paper3_full.read_text(encoding="utf-8", errors="replace")
        normalized_paper3 = normalize_obligation_text(paper3_text)
        deferral_present = (
            "option b" in normalized_paper3
            and any(token in normalized_paper3 for token in ("deferred", "deferral", "companion option b paper"))
        )
        missing_paper3_gates = [
            marker for marker in BALABAN_OPTION_B_GATE_MARKERS if not has_option_b_gate(paper3_text, marker)
        ]
        details = []
        if not deferral_present:
            details.append("Option-B deferral")
        details.extend(missing_paper3_gates)
        results.append(
            CheckResult(
                "balaban-option-b-paper3-deferral-and-five-gates",
                deferral_present and not missing_paper3_gates,
                "; ".join(details),
            )
        )

    script_failures = []
    for path in BALABAN_OPTION_B_OPTIONAL_SCRIPTS:
        full = repo_root / path
        if not full.exists():
            continue
        text = normalize_obligation_text(full.read_text(encoding="utf-8", errors="replace"))
        has_diagnostic = "diagnostic" in text
        has_non_promotion = any(
            phrase in text
            for phrase in (
                "non promoting",
                "non promotion",
                "not promote",
                "no promotion",
                "promotion false",
                "theorem promotion claim",
                "does not promote",
            )
        )
        if not has_diagnostic or not has_non_promotion:
            missing = []
            if not has_diagnostic:
                missing.append("diagnostic")
            if not has_non_promotion:
                missing.append("non-promotion")
            script_failures.append(f"{path.as_posix()}:{','.join(missing)}")
    present_scripts = [
        path.as_posix() for path in BALABAN_OPTION_B_OPTIONAL_SCRIPTS if (repo_root / path).exists()
    ]
    results.append(
        CheckResult(
            "balaban-option-b-optional-scripts-diagnostic-nonpromotion",
            not script_failures,
            "; ".join(script_failures) if script_failures else ", ".join(present_scripts) or "optional scripts absent",
        )
    )
    return results


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
            if not any(normalize_obligation_text(phrase) in corpus for phrase in phrases):
                missing_groups.append(group_name)
        detail_parts = [*missing_sources, *missing_groups]
        results.append(CheckResult(name, not detail_parts, "; ".join(detail_parts)))
    return results


def agda_command(target: Path) -> list[str]:
    stdlib_path = Path("/tmp/dashi-agda-stdlib")
    if not stdlib_path.exists():
        stdlib_path = Path("/usr/share/agda/lib/stdlib")
    return [
        AGDA_BIN,
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
    parser.add_argument(
        "--agda-bin",
        default=AGDA_BIN,
        help="Agda binary to use (defaults to $AGDA_BIN or local agda build)",
    )
    parser.add_argument("--run-agda", action="store_true", help="typecheck the declared Agda support targets")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve()
    global AGDA_BIN
    AGDA_BIN = args.agda_bin

    payload, manifest_load_results = load_manifest(repo_root)
    results = [
        *check_live_files(repo_root),
        *check_manifest_files(repo_root),
        *manifest_load_results,
        *check_manifest_payload(payload, repo_root),
        *check_theorem_interfaces(repo_root),
        *check_public_manuscript_author_lines(repo_root),
        *check_public_citation_placeholders(repo_root),
        *check_renderer_bibliography_entries(repo_root),
        *check_claim_boundaries(repo_root),
        *check_clay_publication_governance(repo_root),
        *check_expected_intake_text(repo_root),
        *check_balaban_option_b_readiness(payload, repo_root),
        *check_missing_math_master_frontier(payload, repo_root),
        *check_theorem_packet_manifest_rows(payload),
        *check_theorem_agenda_surfaces(repo_root),
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

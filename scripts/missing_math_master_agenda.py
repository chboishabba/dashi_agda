#!/usr/bin/env python3
"""Emit the master fail-closed missing-math agenda for NS/YM/Unification.

The agenda is intentionally static and repo-local: it encodes the current
missing theorem/authority walls from the live reference documents and validates
that every cited support surface exists before printing output.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


REQUIRED_SOURCE_DOCS = (
    "Docs/support/reference/NSAnalyticState.md",
    "Docs/support/reference/YMAnalyticState.md",
    "Docs/support/reference/AgdaValidationTargets.md",
    "Docs/papers/live/Paper1NavierStokesClayDraft.md",
    "Docs/papers/live/Paper3YangMillsClayDraft.md",
    "Docs/papers/live/Paper8UnificationDraft.md",
)

ALLOWED_STATUSES = {
    "open",
    "blocked",
    "downstream",
    "authority-intake",
}

LANE_DOCS = {
    "NS": (
        "Docs/support/reference/NSAnalyticState.md",
        "Docs/support/reference/AgdaValidationTargets.md",
        "Docs/papers/live/Paper1NavierStokesClayDraft.md",
    ),
    "YM": (
        "Docs/support/reference/YMAnalyticState.md",
        "Docs/support/reference/AgdaValidationTargets.md",
        "Docs/papers/live/Paper3YangMillsClayDraft.md",
    ),
    "Unification": (
        "Docs/support/reference/AgdaValidationTargets.md",
        "Docs/papers/live/Paper8UnificationDraft.md",
    ),
}


def row(
    lane: str,
    task_id: str,
    title: str,
    status: str,
    support: list[str],
    missing_content: str,
    depends_on: list[str],
    next_artifact: str,
) -> dict[str, Any]:
    if status not in ALLOWED_STATUSES:
        raise ValueError(f"{task_id}: invalid status {status!r}")
    return {
        "lane": lane,
        "task_id": task_id,
        "title": title,
        "status": status,
        "primary_support_files": [*LANE_DOCS[lane], *support],
        "missing_content": missing_content,
        "depends_on": depends_on,
        "promotion_allowed": False,
        "clay_promotion": False,
        "terminal_promotion": False,
        "next_artifact": next_artifact,
    }


def build_agenda() -> dict[str, Any]:
    ns_rows = [
        row(
            "NS",
            "NS-1",
            "A1.1 bounded Abel-weighted defect mass",
            "open",
            ["DASHI/Physics/Closure/NSBoundedAbelMassEstimateBoundary.agda"],
            "Accept or reject the explicit Abel-weighted defect-mass bound in the exact norm consumed by the downstream Abel/leakage route.",
            [],
            "reviewer-readable A1.1 constant and norm certificate",
        ),
        row(
            "NS",
            "NS-2",
            "A1.2 weak-* tightness / precompactness",
            "open",
            ["DASHI/Physics/Closure/NSAbelTriadicDefectMeasureConstructionBoundary.agda"],
            "Prove tightness and compactness for the Abel defect-measure family with the stated tail radius and no hidden compactness loss.",
            ["NS-1"],
            "A1.2 tightness lemma packet",
        ),
        row(
            "NS",
            "NS-3",
            "A1.3 quantitative shell-tail control",
            "open",
            ["DASHI/Physics/Closure/NSAbelTriadicDefectMeasureConstructionBoundary.agda"],
            "Close the quantitative shell-tail estimate for the selected ESS/Type-I danger shell in the exact Abel-weighted topology.",
            ["NS-1", "NS-2"],
            "A1.3 shell-tail estimate with constants",
        ),
        row(
            "NS",
            "NS-4",
            "A3.1 localized energy ODE for W_r",
            "open",
            ["DASHI/Physics/Closure/NSAbelTriadicStationarityConstructionBoundary.agda"],
            "Derive the localized ODE for W_r = U_r - U_infinity with the transport, pressure, and cutoff errors budgeted in the downstream norm.",
            ["NS-1", "NS-2", "NS-3"],
            "A3.1 localized energy ODE proof artifact",
        ),
        row(
            "NS",
            "NS-5",
            "A3.2 Seregin/ESS epsilon-rate intake",
            "authority-intake",
            ["DASHI/Physics/Closure/NSQuantitativeStationarityRateBoundary.agda"],
            "Import or prove the Seregin/ESS quantitative rate, including the candidate epsilon = 1/6, in the exact form used by A3.3/A3.4.",
            ["NS-4"],
            "A3.2 ESS/Seregin authority-intake receipt",
        ),
        row(
            "NS",
            "NS-6",
            "A3.3 quantitative stationarity rate",
            "open",
            ["DASHI/Physics/Closure/NSQuantitativeStationarityRateBoundary.agda"],
            "Prove delta_r -> 0, with the candidate O(r^(1/12)) rate or a replacement rate strong enough for Abel summation.",
            ["NS-4", "NS-5"],
            "A3.3 stationarity-rate theorem packet",
        ),
        row(
            "NS",
            "NS-7",
            "A3.4 multiscale Abel-summation closure",
            "open",
            ["DASHI/Physics/Closure/NSAbelTriadicStationarityConstructionBoundary.agda"],
            "Show the multiscale Abel summation closes without hidden exponent loss or unbudgeted shell leakage.",
            ["NS-1", "NS-2", "NS-3", "NS-4", "NS-5", "NS-6"],
            "A3.4 Abel-summation closure ledger",
        ),
        row(
            "NS",
            "NS-8",
            "A4.1-A4.5 uniform output-support transfer",
            "open",
            [
                "DASHI/Physics/Closure/NSLeiRenTianOutputSupportTransferBoundary.agda",
                "DASHI/Physics/Closure/NSLeiRenTianFourierOutputCouplingBoundary.agda",
            ],
            "Accept the direction-map regularity, Jacobian lower bound, coarea propagation, strip-hitting richness, and Type-I-uniform lower bound as a usable support-richness theorem.",
            [],
            "A4 support-richness theorem packet",
        ),
        row(
            "NS",
            "NS-9",
            "A5-A6 kappa-bias and pointwise-to-Abel coercivity",
            "downstream",
            [
                "DASHI/Physics/Closure/NSA5KappaBiasVanishingFromA4StationarityBoundary.agda",
                "DASHI/Physics/Closure/NSPointwiseToAbelCompositeA6Boundary.agda",
            ],
            "Discharge the kappa-bias vanishing and leakage/coercivity budgets only after A1/A3 stationarity and A4 support richness are accepted.",
            ["NS-1", "NS-2", "NS-3", "NS-4", "NS-5", "NS-6", "NS-7", "NS-8"],
            "A5-A6 downstream consumer proof packet",
        ),
        row(
            "NS",
            "NS-10",
            "A7-A9 depletion, scale monotonicity, and CKN/BKM contradiction",
            "downstream",
            [
                "DASHI/Physics/Closure/NSA7ResidualDepletionGronwallBoundary.agda",
                "DASHI/Physics/Closure/NSA8A9MonotonicityClosureTheoremLadderBoundary.agda",
            ],
            "Run the Gronwall depletion threshold, scale-monotonicity recursion, and final CKN/BKM contradiction after the upstream reserve-producing inputs are accepted.",
            ["NS-9"],
            "A7-A9 closure ladder acceptance artifact",
        ),
    ]

    ym_rows = [
        row(
            "YM",
            "YM-1",
            "Finite carrier self-adjointness and fixed-lattice gap",
            "downstream",
            ["DASHI/Physics/Closure/YMSpectralMarginToContinuumTransferCompositeLightweightBoundary.agda"],
            "Keep the finite operator/gap evidence scoped as finite-carrier input rather than a continuum mass-gap theorem.",
            [],
            "finite-carrier operator/gap scope receipt",
        ),
        row(
            "YM",
            "YM-2",
            "Uniform finite vacuum-orthogonal spectral margin",
            "open",
            ["DASHI/Physics/Closure/YMSpectralMarginToContinuumTransferCompositeLightweightBoundary.agda"],
            "Maintain the gamma_d >= m_* margin with constants compatible with the continuum-transfer interface.",
            ["YM-1"],
            "uniform finite-margin certificate",
        ),
        row(
            "YM",
            "YM-3",
            "Mosco/liminf compactness support",
            "downstream",
            [
                "DASHI/Physics/Closure/YMSprint109NoBottomSpectrumPollutionCompactness.agda",
                "DASHI/Physics/Closure/YMSprint109MoscoSpectralLiminfAssembly.agda",
                "DASHI/Physics/Closure/YMSprint119MoscoAllObligationsReducer.agda",
            ],
            "Keep Mosco/liminf compactness as necessary support, not as a substitute for H3a trace-norm transfer.",
            ["YM-1", "YM-2"],
            "Mosco support boundary audit",
        ),
        row(
            "YM",
            "YM-4",
            "H3a trace-norm transfer on Omega^perp",
            "authority-intake",
            [
                "DASHI/Physics/Closure/YMSprint119TransferCalculusAllObligationsReducer.agda",
                "DASHI/Physics/Closure/YMBruhatTitsToOSLatticeTransferBoundary.agda",
            ],
            "Cite or internally rederive the Balaban-centered transfer theorem in the exact trace-norm and vacuum-orthogonal sector required by Paper 3.",
            ["YM-2", "YM-3"],
            "H3a Balaban transfer theorem intake",
        ),
        row(
            "YM",
            "YM-5",
            "Balaban block-spin effective-action input",
            "authority-intake",
            ["DASHI/Physics/Closure/YMOnlyRemainingAuthorityBlockersBoundary.agda"],
            "Audit the block-spin/effective-action theorem input that H3a consumes; repo-local finite evidence does not replace this authority.",
            ["YM-4"],
            "block-spin effective-action authority docket",
        ),
        row(
            "YM",
            "YM-6",
            "Infinite-volume survival of finite margin",
            "authority-intake",
            ["DASHI/Physics/Closure/YMOnlyRemainingAuthorityBlockersBoundary.agda"],
            "Justify that the finite margin survives the scaling/infinite-volume limit in the cited constructive-QFT framework.",
            ["YM-4", "YM-5"],
            "infinite-volume margin-survival receipt",
        ),
        row(
            "YM",
            "YM-7",
            "RG-compatible reflection positivity",
            "authority-intake",
            ["DASHI/Physics/Closure/YMReflectionPositivityFullTheoremAssemblyBoundary.agda"],
            "Preserve reflection positivity through the RG/continuum intake strongly enough for the OS/Wightman bridge.",
            ["YM-4", "YM-5", "YM-6"],
            "RG reflection-positivity authority receipt",
        ),
        row(
            "YM",
            "YM-8",
            "H3b vacuum-projector continuity",
            "downstream",
            ["DASHI/Physics/Closure/YMContinuumTransferToNoSpectralPollutionSocketCompositeLightweightBoundary.agda"],
            "Transport finite vacuum projectors to the RP.4 limiting vacuum after H3a and reflection positivity are accepted.",
            ["YM-4", "YM-7"],
            "H3b vacuum-compatibility lemma packet",
        ),
        row(
            "YM",
            "YM-9",
            "No spectral pollution below the finite margin",
            "downstream",
            ["DASHI/Physics/Closure/YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary.agda"],
            "Close spectral-pollution exclusion from H3a + H3b with the required norm-resolvent or equivalent strength.",
            ["YM-4", "YM-8"],
            "no-spectral-pollution theorem packet",
        ),
        row(
            "YM",
            "YM-10",
            "RP/OS/Wightman and final authority packaging",
            "authority-intake",
            [
                "DASHI/Physics/Closure/YMContinuumMassGapFinalAssemblyBoundary.agda",
                "DASHI/Physics/Closure/YMStandardLanguageWriteupReadinessBoundary.agda",
                "DASHI/Physics/Closure/YMPaperSubmissionPacketBoundary.agda",
                "DASHI/Physics/Closure/YMExternalAcceptanceBoundary.agda",
                "DASHI/Physics/Closure/YMFinalAuthorityPackagingCompositeLightweightBoundary.agda",
            ],
            "Keep OS reconstruction, Wightman reconstruction, Seiler compatibility, external acceptance, and final mass-gap packaging explicit and non-promoting.",
            ["YM-7", "YM-8", "YM-9"],
            "YM reviewer authority packet with promotion guards false",
        ),
    ]

    unification_rows = [
        row(
            "Unification",
            "UCT-1",
            "Specify the overlap residual PDE",
            "open",
            ["DASHI/Physics/Closure/UnificationScaleInvariantCrossTermHypothesisBoundary.agda"],
            "State the lane-appropriate residual PDE whose vanishing would force the overlap cross term to be null.",
            [],
            "UCT.1 residual PDE statement",
        ),
        row(
            "Unification",
            "UCT-2",
            "Verify ellipticity or parabolicity class",
            "open",
            [
                "DASHI/Physics/Closure/UnificationU1aHJustificationNSLaneBoundary.agda",
                "DASHI/Physics/Closure/UnificationU1aHJustificationYMLaneBoundary.agda",
                "DASHI/Physics/Closure/UnificationU1aHJustificationGlobalBoundary.agda",
            ],
            "Prove the residual PDE has the exact elliptic or parabolic structure required by the intended unique-continuation theorem.",
            ["UCT-1"],
            "UCT.2 operator-class witness",
        ),
        row(
            "Unification",
            "UCT-3",
            "Import matched Carleman/unique-continuation theorem",
            "authority-intake",
            ["DASHI/Physics/Closure/UnificationU1aHPerLaneCompositeBoundary.agda"],
            "Import or prove the Carleman/unique-continuation input matched to the residual PDE class and lane boundary conditions.",
            ["UCT-1", "UCT-2"],
            "UCT.3 Carleman authority packet",
        ),
        row(
            "Unification",
            "UCT-4",
            "Derive cross-term nullity",
            "open",
            ["DASHI/Physics/Closure/UnificationCrossTermNullityDiscriminantBoundary.agda"],
            "Derive cross-term nullity from the residual PDE plus matched unique-continuation theorem; two-homogeneity alone is insufficient.",
            ["UCT-1", "UCT-2", "UCT-3"],
            "UCT.4 cross-term nullity theorem",
        ),
        row(
            "Unification",
            "UCT-5",
            "Modulo-null linearity",
            "downstream",
            ["DASHI/Physics/Closure/UnificationNullClassSubspaceCompleteBoundary.agda"],
            "Show the null class is a complete linear subspace and that the quotient operations are well-defined after cross-term nullity.",
            ["UCT-4"],
            "UCT.5 modulo-null linearity proof",
        ),
        row(
            "Unification",
            "UCT-6",
            "Four-point cancellation",
            "downstream",
            ["DASHI/Physics/Closure/UnificationParallelogramFromBilinearBoundary.agda"],
            "Convert cross-term nullity into the four-point cancellation identity needed by the closure grammar.",
            ["UCT-4", "UCT-5"],
            "UCT.6 four-point cancellation lemma",
        ),
        row(
            "Unification",
            "UCT-7",
            "Parallelogram law on V/null",
            "downstream",
            ["DASHI/Physics/Closure/UnificationParallelogramFromBilinearBoundary.agda"],
            "Derive the parallelogram law on the quotient norm from the null-subspace and four-point cancellation results.",
            ["UCT-5", "UCT-6"],
            "UCT.7 quotient parallelogram theorem",
        ),
        row(
            "Unification",
            "UCT-8",
            "Jordan-von Neumann recovery",
            "downstream",
            ["DASHI/Physics/Closure/UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary.agda"],
            "Recover the quotient Hilbert inner product from the parallelogram law using the JvN polarization route.",
            ["UCT-7"],
            "UCT.8 Jordan-von Neumann recovery socket",
        ),
        row(
            "Unification",
            "UCT-9",
            "Signature/Clifford consumer socket",
            "downstream",
            ["DASHI/Physics/Closure/UnificationSignatureCliffordConsumerSocketBoundary.agda"],
            "Attach signature and Clifford consumers only after the quotient Hilbert structure exists; do not promote these consumers into the missing theorem wall.",
            ["UCT-8"],
            "UCT.9 signature/Clifford consumer boundary",
        ),
        row(
            "Unification",
            "UCT-10",
            "Lane authority and review packet",
            "authority-intake",
            [
                "DASHI/Physics/Closure/UnificationLaneJustificationAuthorityBoundary.agda",
                "DASHI/Physics/Closure/UnificationConsumerAuthorityAssemblyBoundary.agda",
                "DASHI/Physics/Closure/UnificationAuthorityReviewPacketBoundary.agda",
            ],
            "Package lane justifications and consumer authorities with terminal unification and Clay-style promotion guards held false.",
            ["UCT-1", "UCT-2", "UCT-3", "UCT-4", "UCT-5", "UCT-6", "UCT-7", "UCT-8", "UCT-9"],
            "UCT.10 authority review packet with terminal guard false",
        ),
    ]

    return {
        "schema": "dashi.missing_math_master_agenda.v1",
        "promotion_policy": {
            "fail_closed": True,
            "promotion_allowed": False,
            "clay_promotion": False,
            "terminal_promotion": False,
        },
        "source_documents": list(REQUIRED_SOURCE_DOCS),
        "walls": {
            "NS": ns_rows,
            "YM": ym_rows,
            "Unification": unification_rows,
        },
    }


def iter_rows(agenda: dict[str, Any]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for lane in ("NS", "YM", "Unification"):
        rows.extend(agenda["walls"][lane])
    return rows


def validate_agenda(repo_root: Path, agenda: dict[str, Any]) -> None:
    required_paths = set(REQUIRED_SOURCE_DOCS)
    task_ids = {entry["task_id"] for entry in iter_rows(agenda)}
    missing_dependencies: list[str] = []

    expected_counts = {"NS": 10, "YM": 10, "Unification": 10}
    for lane, expected in expected_counts.items():
        actual = len(agenda["walls"].get(lane, []))
        if actual != expected:
            missing_dependencies.append(f"{lane}: expected {expected} rows, got {actual}")

    for entry in iter_rows(agenda):
        required_paths.update(entry["primary_support_files"])
        if entry["status"] not in ALLOWED_STATUSES:
            missing_dependencies.append(f"{entry['task_id']}: invalid status {entry['status']}")
        for dep in entry["depends_on"]:
            if dep not in task_ids:
                missing_dependencies.append(f"{entry['task_id']}: unknown dependency {dep}")
        for flag in ("promotion_allowed", "clay_promotion", "terminal_promotion"):
            if entry.get(flag) is not False:
                missing_dependencies.append(f"{entry['task_id']}: {flag} must be false")

    missing_files = sorted(path for path in required_paths if not (repo_root / path).is_file())
    if missing_files or missing_dependencies:
        problems = []
        if missing_files:
            problems.append("missing required files:\n" + "\n".join(f"  - {path}" for path in missing_files))
        if missing_dependencies:
            problems.append("invalid agenda rows:\n" + "\n".join(f"  - {item}" for item in missing_dependencies))
        raise SystemExit("fail-closed agenda validation failed:\n" + "\n".join(problems))


def escape_cell(value: Any) -> str:
    if isinstance(value, list):
        text = ", ".join(str(item) for item in value) if value else "-"
    elif isinstance(value, bool):
        text = "false" if value is False else "true"
    else:
        text = str(value)
    return text.replace("|", "\\|").replace("\n", " ")


def render_markdown(agenda: dict[str, Any]) -> str:
    columns = (
        "lane",
        "task_id",
        "title",
        "status",
        "primary_support_files",
        "missing_content",
        "depends_on",
        "promotion_allowed",
        "clay_promotion",
        "terminal_promotion",
        "next_artifact",
    )
    lines = [
        "# Missing Math Master Agenda",
        "",
        "Promotion policy: fail-closed; promotion_allowed=false; clay_promotion=false; terminal_promotion=false.",
        "",
        "| " + " | ".join(columns) + " |",
        "| " + " | ".join("---" for _ in columns) + " |",
    ]
    for entry in iter_rows(agenda):
        lines.append("| " + " | ".join(escape_cell(entry[column]) for column in columns) + " |")
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--format", choices=("json", "md"), default="json")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    agenda = build_agenda()
    validate_agenda(repo_root, agenda)
    if args.format == "md":
        sys.stdout.write(render_markdown(agenda))
    else:
        sys.stdout.write(json.dumps(agenda, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

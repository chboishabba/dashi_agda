#!/usr/bin/env python3
"""Fail-closed NS missing-math theorem agenda checker.

The checker encodes the exact NS-A through NS-E theorem packet requested by
the current proof agenda.  It validates that repo marker surfaces exist, but
it never upgrades marker presence into a proof or Clay promotion.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Sequence


THEOREM_IDS = ("NS-A", "NS-B", "NS-C", "NS-D", "NS-E")


@dataclass(frozen=True)
class EvidenceRequirement:
    path: str
    markers: tuple[str, ...]
    role: str


@dataclass(frozen=True)
class EvidenceResult:
    path: str
    role: str
    present: bool
    markers: list[str]
    missing_markers: list[str]
    marker_count: int
    status: str


@dataclass(frozen=True)
class TheoremTarget:
    theorem_id: str
    theorem_name: str
    theorem_statement: str
    symbolic_conclusion: str
    required_inputs: list[str]
    missing_estimates: list[str]
    downstream_unlocks: list[str]
    status: str
    promotion_allowed: bool
    clay_promotion: bool
    evidence: list[EvidenceResult]
    evidence_ok: bool


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Repository root to inspect.",
    )
    parser.add_argument(
        "--format",
        choices=("json", "md"),
        default="json",
        help="Output format. JSON is the default.",
    )
    return parser.parse_args(argv)


def theorem_specs() -> list[dict[str, object]]:
    return [
        {
            "theorem_id": "NS-A",
            "theorem_name": "AbelTriadicDefectMeasureConstruction",
            "theorem_statement": (
                "Construct CKN-scale Abel triadic defect measures for Type-I or ancient NS blowup "
                "rescalings with finite Abel mass and approximate T_NS stationarity."
            ),
            "symbolic_conclusion": (
                "mu_r^Abel -> mu, mu finite; delta_r(T_NS,mu_r) -> 0; "
                "AbelTriadicDefectMeasureConstructed"
            ),
            "required_inputs": [
                "CKN-scale blowup rescaling",
                "bounded Abel triadic mass",
                "LP shell mass/tail control",
                "Seregin/ESS compactness intake",
                "quantitative stationarity rate",
                "true Leray triadic observable",
            ],
            "missing_estimates": [
                "uniform Abel finite-variation bound at CKN scales",
                "weak-* tightness/precompactness of Abel windows",
                "quantitative shell-tail control",
                "delta_r -> 0 stationarity rate for the actual PDE rescaling",
                "Abel summation closure without hidden exponent loss",
            ],
            "downstream_unlocks": [
                "NS-C NSTypeIBlowupKappaBiasBound",
                "A5 stationary kappa-bias vanishing",
                "A6 pointwise-to-Abel consumer inputs",
            ],
            "evidence_requirements": [
                EvidenceRequirement(
                    "README.md",
                    (
                        "AbelTriadicDefectMeasureConstruction",
                        "approximate `T_NS`-stationarity",
                        "prove the kappa-bias bound for actual Type-I/ancient rescalings",
                    ),
                    "README live-frontier marker",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSAbelTriadicDefectMeasureConstructionBoundary.agda",
                    (
                        "NSAbelTriadicDefectMeasureConstructionBoundaryRecorded",
                        "LPAbelTriadicMeasureObligationTyped",
                        "RelationToLeiRenTianTyped",
                        "AbelTriadicDefectMeasureConstructed",
                        "AbelTriadicDefectMeasureConstructed ≡ false",
                        "clayNavierStokesPromoted ≡ false",
                    ),
                    "Agda fail-closed boundary",
                ),
            ],
        },
        {
            "theorem_id": "NS-B",
            "theorem_name": "LeiRenTianOutputSupportTransferToAbelMeasure",
            "theorem_statement": (
                "Transfer Lei-Ren-Tian physical output support through the Fourier/Whitney "
                "coupling into the Abel triadic defect-measure support needed by NS-A/NS-C."
            ),
            "symbolic_conclusion": (
                "LRT_support(physical) => supp_out(mu_r^Abel) avoids collapse; "
                "pdeAbelMeasureSupportTheoremProved"
            ),
            "required_inputs": [
                "Lei-Ren-Tian great-circle/output-support criterion",
                "physical angular measure",
                "localized Whitney frame packets",
                "Fourier output pushforward",
                "Whitney/coarea/Sard-Fubini disintegration",
                "uniform Type-I constants across rescaling windows",
            ],
            "missing_estimates": [
                "PDE Abel-measure support theorem",
                "A4.2-A4.5 quantitative Jacobian/coarea/strip-hitting estimates",
                "uniform non-angular-collapse constants for Type-I windows",
                "exceptional-mass routing through Abel measures",
            ],
            "downstream_unlocks": [
                "NS-A support-rich Abel measures",
                "NS-C kappa-bias obstruction",
                "A5 transfer-neutrality fixed-point step",
            ],
            "evidence_requirements": [
                EvidenceRequirement(
                    "README.md",
                    (
                        "NSLeiRenTianOutputSupportTransferBoundary",
                        "physical-to-Fourier output-support coupling",
                        "does not prove A4 or Clay NS",
                    ),
                    "README A4/LRT marker",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSLeiRenTianOutputSupportTransferBoundary.agda",
                    (
                        "NSLeiRenTianOutputSupportTransferBoundaryRecorded",
                        "pdeAbelMeasureSupportTheoremProved",
                        "pdeAbelMeasureSupportTheoremProved ≡ false",
                        "leiRenTianOutputSupportTransferProved",
                        "clayNavierStokesPromoted ≡ false",
                    ),
                    "Agda LRT output-support boundary",
                ),
            ],
        },
        {
            "theorem_id": "NS-C",
            "theorem_name": "NSTypeIBlowupKappaBiasBound",
            "theorem_statement": (
                "For any Type-I or ancient NS blowup rescaling producing the NS-A/NS-B package, "
                "bound the persistent positive kappa-bias in its Abel triadic defect measure."
            ),
            "symbolic_conclusion": (
                "limsup_{r->0} int lambda(c)(kappa^2-1/2) dmu_r^Abel <= 0; "
                "|Bias(mu_r)| -> 0 or nonpositive"
            ),
            "required_inputs": [
                "NS-A Abel triadic defect measure construction",
                "NS-B output-support richness for Abel measures",
                "exact finite kappa formula omega.S omega = lambda(c)(2 kappa^2 - 1)",
                "arcsine kappa baseline E[kappa^2]=1/2",
                "approximate T_NS stationarity",
                "A5 transfer-neutrality route",
            ],
            "missing_estimates": [
                "bias-to-stretching rewrite for actual PDE Abel measures",
                "one-step Koopman/transfer neutrality with stationarity error",
                "spectral-gap correction estimate in the Abel support class",
                "log-rate vanishing |Bias(mu_r)| = O(|log r|^-1/2)",
                "exclusion of persistent positive Type-I kappa-bias",
            ],
            "downstream_unlocks": [
                "A5 kappa-bias vanishing",
                "A6 bias absorption into dissipation",
                "A7 residual depletion route",
            ],
            "evidence_requirements": [
                EvidenceRequirement(
                    "README.md",
                    (
                        "NSTypeIBlowupKappaBiasBound",
                        "lambda(c)(kappa^2 - 1/2)",
                        "prove the Type-I bias bound",
                    ),
                    "README kappa-bias frontier",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSA5KappaBiasVanishingFromA4StationarityBoundary.agda",
                    (
                        "NSA5KappaBiasVanishingFromA4StationarityBoundary",
                        "a5CandidateTheoremStatementText",
                        "|Bias(mu_r)| = O(|log r|^-1/2)",
                        "clayNavierStokesPromotedHere ≡ false",
                    ),
                    "Agda A5 theorem-target grammar",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSA6A4BiasToLeakageClosureCompositeBoundary.agda",
                    (
                        "a5BiasVanishingTheoremProved",
                        "a5BiasVanishingTheoremProved ≡ false",
                        "a6PointwiseToAbelTheoremProved",
                        "nsClayPromotedHere ≡ false",
                    ),
                    "Agda A4/A5/A6 fail-closed composite",
                ),
            ],
        },
        {
            "theorem_id": "NS-D",
            "theorem_name": "PointwiseToAbelStretchingTransfer",
            "theorem_statement": (
                "Replace localized pointwise vortex stretching by the Abel/shell mean in the "
                "enstrophy defect identity with diagonal, off-diagonal, localization, pressure, "
                "and mixing errors controlled in the exact A6 budget."
            ),
            "symbolic_conclusion": (
                "omega.S omega pointwise -> <omega.S omega>_Abel + Err; "
                "Err <= epsilon*D + lower-order"
            ),
            "required_inputs": [
                "A5 bias vanishing or nonpositive bias control",
                "diagonal stretching-to-Abel mean theorem",
                "off-diagonal shell absorption",
                "Abel shell mixing LLN",
                "localized cutoff and pressure commutator estimates",
                "Bony/paraproduct repair for A6.2",
            ],
            "missing_estimates": [
                "full pressure/localization theorem in the exact PDE norm",
                "uniform Abel recentering/tail estimate",
                "global residual monotonicity after A6",
                "A7 depletion consumer",
            ],
            "downstream_unlocks": [
                "A6 leakage reduction",
                "A7 residual depletion Gronwall",
                "A8 scale monotonicity recursion",
            ],
            "evidence_requirements": [
                EvidenceRequirement(
                    "README.md",
                    (
                        "NSPointwiseToAbelCompositeA6Boundary",
                        "pointwise `omega . S omega`",
                        "residual depletion, and NS Clay remain unproved",
                    ),
                    "README A6 pointwise-to-Abel marker",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSPointwiseToAbelCompositeA6Boundary.agda",
                    (
                        "NSPointwiseToAbelCompositeA6Boundary",
                        "Exact A6 inequality shape",
                        "residualMonotonicityProved ≡ false",
                        "residualDepletionProved ≡ false",
                        "nsClayPromoted ≡ false",
                    ),
                    "Agda A6 composite boundary",
                ),
            ],
        },
        {
            "theorem_id": "NS-E",
            "theorem_name": "ClosureChainA5A9",
            "theorem_statement": (
                "Close the downstream A5-A9 chain: A5 kappa-bias vanishing, A6 leakage "
                "reduction, A7 Gronwall depletion, A8 scale monotonicity recursion, and "
                "A9 CKN/BKM contradiction."
            ),
            "symbolic_conclusion": (
                "A5 & A6 & A7 & A8 => A9; A9 => no Type-I singular CKN/BKM blowup route; "
                "Clay promotion still requires separate authority"
            ),
            "required_inputs": [
                "NS-C kappa-bias bound",
                "NS-D pointwise-to-Abel stretching transfer",
                "A7 residual depletion differential inequality",
                "A8 full local defect monotonicity/annular decay",
                "A9 CKN epsilon regularity and BKM continuation interface",
                "paper-facing terminal guard",
            ],
            "missing_estimates": [
                "A7 critical residual depletion theorem",
                "A8 scale-recursion contraction in the exact local defect norm",
                "A9 singularity contradiction with accepted CKN/BKM hypotheses",
                "global Clay Navier-Stokes authority packet",
            ],
            "downstream_unlocks": [
                "paper-facing NS closure appendix can cite a complete fail-closed chain",
                "conditional CKN/BKM contradiction route",
                "candidate Clay packet review, still non-promoting",
            ],
            "evidence_requirements": [
                EvidenceRequirement(
                    "Docs/roadmaps/ClayNSProofRoadmap.md",
                    (
                        "`A5` kappa-bias vanishing",
                        "`A6` leakage reduction and pointwise-to-Abel transfer",
                        "`A7` Gronwall depletion",
                        "`A8` scale-monotonicity recursion",
                        "`A9` CKN/BKM contradiction",
                        "unpromoted",
                    ),
                    "roadmap A5-A9 grammar marker",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSA6A4BiasToLeakageClosureCompositeBoundary.agda",
                    (
                        "a7CriticalResidualDepletionTheoremProved ≡ false",
                        "a8LocalDefectMonotonicityTheoremProved ≡ false",
                        "a9CKNBKMClosureTheoremProved ≡ false",
                        "nsClayPromotedHere ≡ false",
                    ),
                    "Agda A5-A9 fail-closed flags",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSA7ResidualDepletionGronwallBoundary.agda",
                    (
                        "NSA7ResidualDepletionGronwallBoundary",
                        "A7 residual depletion",
                        "NSClayPromotedFromA7 ≡ false",
                    ),
                    "Agda A7 boundary",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSA8A9MonotonicityClosureTheoremLadderBoundary.agda",
                    (
                        "NSA8A9MonotonicityClosureTheoremLadderBoundary",
                        "A8",
                        "A9",
                        "NSClayPromotedFromA8A9 ≡ false",
                    ),
                    "Agda A8/A9 ladder boundary",
                ),
                EvidenceRequirement(
                    "DASHI/Physics/Closure/NSA9CKNBKMClosureBoundary.agda",
                    (
                        "NSA9CKNBKMClosureBoundary",
                        "CKN",
                        "BKM",
                        "NSClayPromotedFromA9 ≡ false",
                    ),
                    "Agda A9 CKN/BKM boundary",
                ),
            ],
        },
    ]


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return path.read_text(encoding="utf-8", errors="replace")


def validate_requirement(repo_root: Path, req: EvidenceRequirement) -> EvidenceResult:
    path = repo_root / req.path
    if not path.is_file():
        return EvidenceResult(
            path=req.path,
            role=req.role,
            present=False,
            markers=list(req.markers),
            missing_markers=list(req.markers),
            marker_count=0,
            status="missing_file",
        )
    text = read_text(path)
    missing = [marker for marker in req.markers if marker not in text]
    return EvidenceResult(
        path=req.path,
        role=req.role,
        present=not missing,
        markers=list(req.markers),
        missing_markers=missing,
        marker_count=len(req.markers) - len(missing),
        status="markers_present" if not missing else "missing_markers",
    )


def build_agenda(repo_root: Path) -> dict[str, object]:
    targets: list[TheoremTarget] = []
    for spec in theorem_specs():
        evidence = [
            validate_requirement(repo_root, req)
            for req in spec["evidence_requirements"]  # type: ignore[index]
        ]
        evidence_ok = all(item.present for item in evidence)
        targets.append(
            TheoremTarget(
                theorem_id=str(spec["theorem_id"]),
                theorem_name=str(spec["theorem_name"]),
                theorem_statement=str(spec["theorem_statement"]),
                symbolic_conclusion=str(spec["symbolic_conclusion"]),
                required_inputs=list(spec["required_inputs"]),  # type: ignore[arg-type]
                missing_estimates=list(spec["missing_estimates"]),  # type: ignore[arg-type]
                downstream_unlocks=list(spec["downstream_unlocks"]),  # type: ignore[arg-type]
                status=(
                    "fail_closed_marker_validated_not_proved"
                    if evidence_ok
                    else "fail_closed_missing_required_evidence_marker"
                ),
                promotion_allowed=False,
                clay_promotion=False,
                evidence=evidence,
                evidence_ok=evidence_ok,
            )
        )

    ok = tuple(target.theorem_id for target in targets) == THEOREM_IDS and all(
        target.evidence_ok and not target.promotion_allowed and not target.clay_promotion
        for target in targets
    )
    payload = {
        "ok": ok,
        "fail_closed": True,
        "agenda": "NS missing-math theorem packet",
        "theorem_ids": list(THEOREM_IDS),
        "promotion_allowed": False,
        "clay_promotion": False,
        "claim_policy": "Evidence markers validate agenda surfaces only; no proof or Clay promotion is claimed.",
        "targets": [asdict(target) for target in targets],
        "summary": {
            "target_count": len(targets),
            "evidence_requirement_count": sum(len(target.evidence) for target in targets),
            "evidence_requirements_ok": sum(
                1 for target in targets for evidence in target.evidence if evidence.present
            ),
            "proof_claimed": False,
            "clay_promotion": False,
        },
    }
    return payload


def render_md(payload: dict[str, object]) -> str:
    lines = [
        "# NS Missing-Math Theorem Agenda",
        "",
        f"- ok: `{str(payload['ok']).lower()}`",
        f"- fail_closed: `{str(payload['fail_closed']).lower()}`",
        "- proof_claimed: `false`",
        "- clay_promotion: `false`",
        "",
    ]
    for target in payload["targets"]:  # type: ignore[index]
        item = target  # type: ignore[assignment]
        lines.extend(
            [
                f"## {item['theorem_id']} {item['theorem_name']}",
                "",
                f"- status: `{item['status']}`",
                "- promotion_allowed: `false`",
                "- clay_promotion: `false`",
                f"- theorem_statement: {item['theorem_statement']}",
                f"- symbolic_conclusion: `{item['symbolic_conclusion']}`",
                "- required_inputs: " + "; ".join(item["required_inputs"]),
                "- missing_estimates: " + "; ".join(item["missing_estimates"]),
                "- downstream_unlocks: " + "; ".join(item["downstream_unlocks"]),
                "- evidence:",
            ]
        )
        for evidence in item["evidence"]:
            lines.append(
                f"  - `{evidence['path']}`: `{evidence['status']}` "
                f"({evidence['marker_count']}/{len(evidence['markers'])} markers)"
            )
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = build_agenda(args.repo_root.resolve())
    if args.format == "md":
        print(render_md(payload), end="")
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

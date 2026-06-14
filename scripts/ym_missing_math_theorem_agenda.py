#!/usr/bin/env python3
"""Emit the fail-closed YM missing-math theorem agenda.

This checker is intentionally repo-local.  It encodes the five theorem targets
from the current Paper 3/YM packet, then validates that the supporting Paper 3,
YM documentation, and Agda receipt markers still exist before emitting JSON or
Markdown.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


THEOREM_IDS = ("YM-A", "YM-B", "YM-C", "YM-D", "YM-E")


@dataclass(frozen=True)
class EvidenceMarker:
    path: str
    markers: tuple[str, ...]
    role: str


@dataclass(frozen=True)
class TheoremTarget:
    theorem_id: str
    name: str
    statement: str
    symbolic_conclusion: str
    required_inputs: tuple[str, ...]
    missing_estimates: tuple[str, ...]
    authority_inputs: tuple[str, ...]
    downstream_unlocks: tuple[str, ...]
    status: str
    evidence_markers: tuple[EvidenceMarker, ...]
    option_paths: tuple[dict[str, str], ...] = ()


COMMON_DOC_MARKERS = (
    EvidenceMarker(
        "Docs/papers/live/Paper3YangMillsClayDraft.md",
        ("Paper 3", "Yang-Mills", "promotion"),
        "live Paper 3 draft names the non-promoting YM lane",
    ),
    EvidenceMarker(
        "Docs/support/reference/YMAnalyticState.md",
        ("Yang-Mills", "Forbidden claim", "Clay promotion"),
        "YM analytic state records the fail-closed forbidden claim",
    ),
)


THEOREMS: tuple[TheoremTarget, ...] = (
    TheoremTarget(
        theorem_id="YM-A",
        name="HamiltonianDominatesDefectPlusHolonomy",
        statement=(
            "Finite gauge Hamiltonian domination controls defect energy plus "
            "non-flat holonomy with constants that survive only as a local input."
        ),
        symbolic_conclusion="H_fin >= c_def Defect + c_hol Hol_nonflat on carrier sector",
        required_inputs=(
            "self-adjoint finite gauge quotient Hamiltonian",
            "Bochner-Weitzenbock finite domination receipt",
            "positive defect and holonomy weights",
        ),
        missing_estimates=(
            "continuum transfer of finite domination",
            "OS/RP-compatible lower-bound transport",
        ),
        authority_inputs=(),
        downstream_unlocks=("YM-B", "YM-D"),
        status="downstream-locked",
        evidence_markers=(
            *COMMON_DOC_MARKERS,
            EvidenceMarker(
                "DASHI/Physics/Closure/YMBochnerWeitzenbockHamiltonianDominationBoundary.agda",
                ("noClayPromotionFromYMBochnerWeitzenbockBoundary", "terminal promotion stay false"),
                "Agda finite-domination boundary keeps promotion closed",
            ),
            EvidenceMarker(
                "Docs/papers/generated/core_papers_theorem_var_manifest.md",
                ("Missing-math master: YM finite domination", "downstream-locked"),
                "generated theorem manifest records YM-A frontier status",
            ),
        ),
    ),
    TheoremTarget(
        theorem_id="YM-B",
        name="H3aTraceNormTransfer",
        statement=(
            "H3a transfers cutoff/RG data to the continuum vacuum-orthogonal "
            "sector in the trace norm needed by the no-pollution chain."
        ),
        symbolic_conclusion="||P_perp(T_a - T_inf)P_perp||_1 -> 0",
        required_inputs=(
            "strict p=7 KP absorption",
            "Balaban RG/block-spin transfer package",
            "vacuum-orthogonal trace-class topology",
        ),
        missing_estimates=(
            "repo-native operator-limit construction from Option B diagnostics",
            "uniform trace-norm summability strong enough for H3a",
        ),
        authority_inputs=(
            "Option A: external Balaban RG/polymer theorem intake",
            "Option B: repo-native five-lemma route remains open past B4 diagnostics",
        ),
        downstream_unlocks=("YM-C", "YM-D", "YM-E"),
        status="authority-intake-with-repo-native-open-option",
        option_paths=(
            {
                "option": "A",
                "kind": "authority-backed",
                "status": "authority-intake",
                "description": "External Balaban RG/polymer theorem intake for H3a.",
            },
            {
                "option": "B",
                "kind": "repo-native-open",
                "status": "diagnostic-not-theorem",
                "description": "B4 trace-norm consequence is recorded, but the operator limit is not constructed.",
            },
        ),
        evidence_markers=(
            *COMMON_DOC_MARKERS,
            EvidenceMarker(
                "DASHI/Physics/Closure/YMH3aContinuumIntakeReceipt.agda",
                ("ymH3aContinuumIntakeKeepsClayFalse", "H3a continuum intake"),
                "Agda H3a intake boundary keeps Clay false",
            ),
            EvidenceMarker(
                "DASHI/Physics/Closure/OptionBNativePolymerFiveLemmaBoundaryReceipt.agda",
                ("B4TraceNormConvergenceFromSummability", "operator-limit non-promotion boundary"),
                "Agda Option B B4 diagnostic is distinct from an H3a theorem",
            ),
            EvidenceMarker(
                "Docs/papers/generated/core_papers_theorem_var_manifest.md",
                (
                    "Balaban Option A theorem-intake boundary",
                    "Option B B4 trace-norm consequence boundary",
                ),
                "generated theorem manifest preserves Option A/B distinction",
            ),
        ),
    ),
    TheoremTarget(
        theorem_id="YM-C",
        name="H3bVacuumProjectionContinuity",
        statement=(
            "H3b identifies finite vacuum projectors with the limiting RP.4 "
            "vacuum projection strongly enough for the spectral chain."
        ),
        symbolic_conclusion="P_vac,a -> P_vac,inf and P_perp,a -> P_perp,inf compatibly",
        required_inputs=(
            "H3a trace-norm transfer",
            "positive limiting mass parameter m_infty",
            "RP.4 limiting vacuum identity",
        ),
        missing_estimates=(
            "vacuum-projector continuity in the exact topology consumed by YM-D",
            "strong/norm-resolvent compatibility tied to the limiting vacuum",
        ),
        authority_inputs=(),
        downstream_unlocks=("YM-D", "YM-E"),
        status="open",
        evidence_markers=(
            *COMMON_DOC_MARKERS,
            EvidenceMarker(
                "DASHI/Physics/Closure/YMH3bVacuumProjectorNoSpectralPollutionBoundaryReceipt.agda",
                ("ymH3bBoundaryPromotionImpossibleHere", "H3b", "promotion remains closed"),
                "Agda H3b boundary names the vacuum-projector theorem wire",
            ),
            EvidenceMarker(
                "DASHI/Physics/Closure/YMSprint109NoBottomSpectrumPollutionCompactness.agda",
                ("h3bVacuumProjectionContinuityProvedHere", "false"),
                "Sprint 109 Agda surface keeps H3b continuity unproved here",
            ),
            EvidenceMarker(
                "Docs/papers/generated/core_papers_theorem_var_manifest.md",
                ("Missing-math master: YM H3b", "open"),
                "generated theorem manifest records YM-C as open",
            ),
        ),
    ),
    TheoremTarget(
        theorem_id="YM-D",
        name="NoSpectralPollutionBelowFiniteMargin",
        statement=(
            "The continuum Hamiltonian gains no spectrum below the transported "
            "finite vacuum-orthogonal margin."
        ),
        symbolic_conclusion="spec(H_inf|Omega_perp) cap (0,m_*) = empty",
        required_inputs=(
            "YM-A finite domination/margin input",
            "YM-B H3a trace-norm transfer",
            "YM-C H3b vacuum projection continuity",
            "Mosco or norm-resolvent strength sufficient for spectral exclusion",
        ),
        missing_estimates=(
            "below-margin no-pollution exclusion",
            "finite-to-continuum lower-margin survival",
        ),
        authority_inputs=(),
        downstream_unlocks=("YM-E", "continuum mass-gap packaging"),
        status="false-as-promoted-theorem",
        evidence_markers=(
            *COMMON_DOC_MARKERS,
            EvidenceMarker(
                "DASHI/Physics/Closure/YMNoSpectralPollutionToOSWightmanSocketCompositeLightweightBoundary.agda",
                ("YMNoSpectralPollutionToOSWightmanSocketCompositeProved", "false"),
                "Agda no-spectral-pollution socket remains false",
            ),
            EvidenceMarker(
                "Docs/papers/generated/core_papers_theorem_var_manifest.md",
                ("Missing-math master: YM no spectral pollution", "false"),
                "generated theorem manifest records YM-D as false",
            ),
        ),
    ),
    TheoremTarget(
        theorem_id="YM-E",
        name="RP/OS/Wightman reconstruction compatibility",
        statement=(
            "Reflection positivity, OS axioms, thermodynamic limit, Wightman "
            "reconstruction, and operator convergence are mutually compatible "
            "with the YM-D spectral conclusion."
        ),
        symbolic_conclusion="RP + OS + Wightman + operator convergence => physical YM Hilbert package",
        required_inputs=(
            "YM-D no spectral pollution below finite margin",
            "continuum reflection positivity",
            "OS axioms for the gauge-invariant physical sector",
            "Wightman reconstruction authority hypotheses",
        ),
        missing_estimates=(
            "gauge-sector continuum OS positivity",
            "thermodynamic-to-Wightman operator compatibility",
            "external acceptance of reconstruction hypotheses",
        ),
        authority_inputs=(
            "Osterwalder-Schrader reconstruction theorem",
            "Wightman reconstruction compatibility authority",
            "constructive-QFT thermodynamic limit authority",
        ),
        downstream_unlocks=("continuum mass gap candidate packet", "Clay review packet only after external acceptance"),
        status="downstream-locked",
        evidence_markers=(
            *COMMON_DOC_MARKERS,
            EvidenceMarker(
                "DASHI/Physics/Closure/YMThermodynamicOSWightmanOperatorBoundaryReceipt.agda",
                ("YMThermodynamicOSWightmanOperatorBoundaryClosesNothing", "Clay promotion is explicitly forbidden here"),
                "Agda thermodynamic OS/Wightman boundary closes no Clay theorem",
            ),
            EvidenceMarker(
                "DASHI/Physics/Closure/YMOSWightmanReconstructionAuthority.agda",
                ("OSWightmanReconstruction", "Authority"),
                "Agda OS/Wightman reconstruction authority surface exists",
            ),
            EvidenceMarker(
                "Docs/papers/generated/core_papers_theorem_var_manifest.md",
                ("Missing-math master: YM RP/OS/Wightman", "downstream-locked"),
                "generated theorem manifest records YM-E as downstream locked",
            ),
        ),
    ),
)


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--format", choices=("json", "md"), default="json")
    return parser.parse_args(argv)


def read_text(repo_root: Path, rel_path: str) -> str | None:
    path = repo_root / rel_path
    if not path.is_file():
        return None
    return path.read_text(encoding="utf-8")


def validate_marker(repo_root: Path, marker: EvidenceMarker) -> dict[str, Any]:
    text = read_text(repo_root, marker.path)
    if text is None:
        return {
            "path": marker.path,
            "role": marker.role,
            "present": False,
            "markers": list(marker.markers),
            "matched_markers": [],
            "ok": False,
        }
    matched = [needle for needle in marker.markers if needle in text]
    return {
        "path": marker.path,
        "role": marker.role,
        "present": True,
        "markers": list(marker.markers),
        "matched_markers": matched,
        "ok": len(matched) == len(marker.markers),
    }


def theorem_to_row(repo_root: Path, theorem: TheoremTarget) -> dict[str, Any]:
    evidence = [validate_marker(repo_root, marker) for marker in theorem.evidence_markers]
    return {
        "theorem_id": theorem.theorem_id,
        "name": theorem.name,
        "statement": theorem.statement,
        "symbolic_conclusion": theorem.symbolic_conclusion,
        "required_inputs": list(theorem.required_inputs),
        "missing_estimates": list(theorem.missing_estimates),
        "authority_inputs": list(theorem.authority_inputs),
        "downstream_unlocks": list(theorem.downstream_unlocks),
        "status": theorem.status,
        "promotion_allowed": False,
        "clay_promotion": False,
        "evidence": evidence,
        "evidence_ok": all(item["ok"] for item in evidence),
        **({"option_paths": list(theorem.option_paths)} if theorem.option_paths else {}),
    }


def build_payload(repo_root: Path) -> dict[str, Any]:
    rows = [theorem_to_row(repo_root, theorem) for theorem in THEOREMS]
    ids = [row["theorem_id"] for row in rows]
    flags_false = all(
        row["promotion_allowed"] is False and row["clay_promotion"] is False
        for row in rows
    )
    return {
        "agenda": "ym_missing_math_theorem_agenda",
        "packet": "latest Paper3/YM theorem packet",
        "ok": ids == list(THEOREM_IDS) and flags_false and all(row["evidence_ok"] for row in rows),
        "fail_closed": True,
        "promotion_allowed": False,
        "clay_promotion": False,
        "theorem_ids": ids,
        "theorems": rows,
    }


def render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# YM Missing-Math Theorem Agenda",
        "",
        f"- ok: `{str(payload['ok']).lower()}`",
        f"- fail_closed: `{str(payload['fail_closed']).lower()}`",
        f"- promotion_allowed: `{str(payload['promotion_allowed']).lower()}`",
        f"- clay_promotion: `{str(payload['clay_promotion']).lower()}`",
        "",
    ]
    for row in payload["theorems"]:
        lines.extend(
            [
                f"## {row['theorem_id']} {row['name']}",
                "",
                f"- status: `{row['status']}`",
                f"- conclusion: `{row['symbolic_conclusion']}`",
                f"- promotion_allowed: `{str(row['promotion_allowed']).lower()}`",
                f"- clay_promotion: `{str(row['clay_promotion']).lower()}`",
                f"- evidence_ok: `{str(row['evidence_ok']).lower()}`",
                f"- statement: {row['statement']}",
                f"- required_inputs: {', '.join(row['required_inputs'])}",
                f"- missing_estimates: {', '.join(row['missing_estimates']) or 'none'}",
                f"- authority_inputs: {', '.join(row['authority_inputs']) or 'none'}",
                f"- downstream_unlocks: {', '.join(row['downstream_unlocks'])}",
            ]
        )
        if "option_paths" in row:
            for option in row["option_paths"]:
                lines.append(
                    f"- option {option['option']}: `{option['kind']}` / `{option['status']}` - {option['description']}"
                )
        for evidence in row["evidence"]:
            marker_state = "ok" if evidence["ok"] else "missing"
            lines.append(f"- evidence {marker_state}: `{evidence['path']}` ({evidence['role']})")
        lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo_root = args.repo_root.resolve()
    payload = build_payload(repo_root)
    if args.format == "md":
        print(render_markdown(payload))
    else:
        print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if payload["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

#!/usr/bin/env python3
"""Fail-closed audit for the current NS-C kappa-bias route candidate.

This script records the latest Gaussian self-similar bookkeeping for the
Navier-Stokes kappa-bias route.  It is intentionally diagnostic: it checks that
the formal route data is internally coherent, names the exact analytic blockers,
and keeps every proof/promotion flag false.

Default output is JSON.  With ``--out-dir`` the JSON receipt is also written to
disk; ``--markdown`` adds a short Markdown report.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Sequence


CONTRACT = "ns_kappa_bias_candidate_audit"
ARTIFACT_SCHEMA = "dashi.ns_kappa_bias_candidate_audit.v1"
SUMMARY_NAME = "ns_kappa_bias_candidate_audit_summary.json"
REPORT_NAME = "ns_kappa_bias_candidate_audit.md"
ROUTE_DECISION = "NS_C_KAPPA_BIAS_ROUTE_CANDIDATE_OPEN_NON_PROMOTING"


@dataclass(frozen=True)
class IdentityTerm:
    term_id: str
    expression: str
    role: str
    status: str
    promotion_ready: bool = False


@dataclass(frozen=True)
class Blocker:
    blocker_id: str
    missing_witness: str
    why_it_blocks: str
    status: str = "OPEN_BLOCKER"
    proved: bool = False


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Repository root used only for receipt metadata.",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="Optional directory for JSON and Markdown artifacts.",
    )
    parser.add_argument(
        "--markdown",
        action="store_true",
        help="Also emit a Markdown report.  Requires --out-dir for file output.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        default=True,
        help="Emit JSON to stdout.  This is the default.",
    )
    return parser.parse_args(argv)


def gaussian_balance_terms() -> list[IdentityTerm]:
    return [
        IdentityTerm(
            term_id="gaussian_weight",
            expression="G(y)=exp(-|y|^2/4)",
            role="self-similar Gaussian weight for the Leray variable y",
            status="RECORDED",
        ),
        IdentityTerm(
            term_id="omega_energy",
            expression="Omega_G=int |omega|^2 G dy",
            role="nonzero weighted vorticity mass used to normalize Bias_G and Drift_G",
            status="RECORDED_REQUIRES_NONTRIVIAL_PROFILE",
        ),
        IdentityTerm(
            term_id="diffusion_side",
            expression="2 int |grad omega|^2 G dy - 1/2 int |omega|^2 G dy",
            role="left side after multiplying the self-similar vorticity equation by omega G and integrating",
            status="FORMAL_IDENTITY_RECORDED",
        ),
        IdentityTerm(
            term_id="bias_side",
            expression="4 Bias_G Omega_G",
            role="Gaussian weighted kappa-bias contribution",
            status="FORMAL_IDENTITY_RECORDED",
        ),
        IdentityTerm(
            term_id="drift_ibp_side",
            expression="Drift_G Omega_G",
            role="residual drift/integration-by-parts contribution not controlled by the kappa-bias proxy alone",
            status="OPEN_CONTROL_TERM",
        ),
        IdentityTerm(
            term_id="full_balance",
            expression=(
                "2 int |grad omega|^2 G dy - 1/2 int |omega|^2 G dy "
                "= 4 Bias_G Omega_G + Drift_G Omega_G"
            ),
            role="Gaussian self-similar balance identity under sufficient smoothness/decay",
            status="CANDIDATE_IDENTITY_NOT_PROOF",
        ),
        IdentityTerm(
            term_id="ou_poincare_control",
            expression="int |grad omega|^2 G dy >= 1/2 int |omega|^2 G dy",
            role="OU/Poincare lower bound for nontrivial admissible weighted profiles",
            status="CONTROL_RECORDED_NOT_CLOSING_ROUTE",
        ),
        IdentityTerm(
            term_id="normalized_inequality",
            expression="1 <= 4 Bias_G + Drift_G",
            role="necessary normalized constraint when Omega_G > 0",
            status="NECESSARY_CONDITION_ONLY",
        ),
        IdentityTerm(
            term_id="bias_mapping",
            expression="Bias_G maps to int lambda(c)(kappa^2-1/2) dmu",
            role="candidate bridge from Gaussian self-similar bookkeeping to Abel triadic defect measure bias",
            status="MAPPING_TARGET_OPEN",
        ),
    ]


def blockers() -> list[Blocker]:
    return [
        Blocker(
            blocker_id="abel_triadic_defect_measure_construction",
            missing_witness=(
                "construct a CKN-scale Abel triadic defect measure mu from actual Type-I or ancient blowup "
                "rescalings"
            ),
            why_it_blocks="without mu, the integral lambda(c)(kappa^2-1/2) dmu is only a target expression",
        ),
        Blocker(
            blocker_id="bias_g_to_abel_integral_identification",
            missing_witness="prove Bias_G equals or is controlled by the Abel triadic kappa-bias integral",
            why_it_blocks="the finite angular formula does not identify the Gaussian PDE term with the defect measure",
        ),
        Blocker(
            blocker_id="drift_integration_by_parts_control",
            missing_witness="bound or sign-control Drift_G for the self-similar/ancient profile class",
            why_it_blocks="OU/Poincare gives only 1 <= 4 Bias_G + Drift_G, not a kappa-bias bound by itself",
        ),
        Blocker(
            blocker_id="approximate_stationarity_under_t_ns",
            missing_witness="prove approximate T_NS stationarity for blowup-generated Abel measures",
            why_it_blocks="the variational proxy says stationarity is the decisive constraint on persistent bias",
        ),
        Blocker(
            blocker_id="compensated_leakage_identity",
            missing_witness="prove the compensated leakage identity needed to pass from finite diagnostics to PDE scales",
            why_it_blocks="leakage can invalidate a local bias balance even when finite angular samples look favorable",
        ),
        Blocker(
            blocker_id="local_defect_monotonicity_and_ckn_bkm_closure",
            missing_witness="connect the bias obstruction to local defect monotonicity, CKN regularity, and BKM closure",
            why_it_blocks="even a kappa-bias estimate would still need the continuation/regularity closure chain",
        ),
    ]


def build_audit(repo_root: Path) -> dict[str, Any]:
    identity_terms = gaussian_balance_terms()
    blocker_rows = blockers()
    blocker_ids = [row.blocker_id for row in blocker_rows]
    core_identity = next(row for row in identity_terms if row.term_id == "full_balance")
    normalized = next(row for row in identity_terms if row.term_id == "normalized_inequality")
    mapping = next(row for row in identity_terms if row.term_id == "bias_mapping")

    proof_flags = {
        "route_candidate": True,
        "route_open": True,
        "route_non_promoting": True,
        "candidate_proved": False,
        "identity_proved_for_ns_profiles": False,
        "ou_poincare_closes_route": False,
        "drift_term_controlled": False,
        "bias_g_mapping_proved": False,
        "abel_triadic_defect_measure_constructed": False,
        "type_i_kappa_bias_bound_proved": False,
        "local_defect_monotonicity_proved": False,
        "ckn_bkm_closure_proved": False,
        "clay_navier_stokes_promoted": False,
        "promotion_allowed": False,
        "claim_proved": False,
        "claim_closed": False,
    }

    structural_checks = {
        "has_gaussian_balance_identity": core_identity.expression
        == "2 int |grad omega|^2 G dy - 1/2 int |omega|^2 G dy = 4 Bias_G Omega_G + Drift_G Omega_G",
        "has_ou_poincare_control": normalized.expression == "1 <= 4 Bias_G + Drift_G",
        "has_drift_ibp_term": any(row.term_id == "drift_ibp_side" for row in identity_terms),
        "has_bias_g_mapping": mapping.expression == "Bias_G maps to int lambda(c)(kappa^2-1/2) dmu",
        "has_explicit_blockers": len(blocker_rows) >= 5 and all(not row.proved for row in blocker_rows),
        "promotion_flags_false": all(value is False for key, value in proof_flags.items() if key not in {"route_candidate", "route_open", "route_non_promoting"}),
    }
    audit_passed = all(structural_checks.values())

    return {
        "artifact_schema": ARTIFACT_SCHEMA,
        "contract": CONTRACT,
        "repo_root": str(repo_root),
        "route": "NS-C kappa-bias candidate",
        "route_decision": ROUTE_DECISION,
        "decision": ROUTE_DECISION,
        "status": "candidate_open_non_promoting_not_proved",
        "audit_passed": audit_passed,
        "core_identity_fields": {
            "gaussian_weight": "G(y)=exp(-|y|^2/4)",
            "omega_energy": "Omega_G=int |omega|^2 G dy",
            "gaussian_self_similar_balance_identity": core_identity.expression,
            "ou_poincare_lower_bound": "int |grad omega|^2 G dy >= 1/2 int |omega|^2 G dy",
            "necessary_normalized_constraint": normalized.expression,
            "drift_integration_by_parts_term": "Drift_G Omega_G",
            "bias_g_to_abel_integral_mapping": mapping.expression,
            "abel_integrand": "lambda(c)(kappa^2-1/2)",
        },
        "identity_terms": [asdict(row) for row in identity_terms],
        "blockers": [asdict(row) for row in blocker_rows],
        "blocker_ids": blocker_ids,
        "structural_checks": structural_checks,
        "promotion_flags": proof_flags,
        "promotion": {
            "promotes_ns_clay": False,
            "promotes_type_i_kappa_bias_bound": False,
            "promotes_abel_measure_construction": False,
            "reason": "diagnostic identity ledger only; all analytic blockers remain open",
        },
        "interpretation": (
            "The Gaussian identity records a necessary balance for a nontrivial self-similar profile. "
            "OU/Poincare forces 1 <= 4 Bias_G + Drift_G, so kappa-bias cannot promote without "
            "controlling the drift integration-by-parts term and constructing the Abel defect measure."
        ),
        "control_card": {
            "O": "Worker 2 owns scripts/ns_kappa_bias_candidate_audit.py and tests/test_ns_kappa_bias_candidate_audit.py",
            "R": "record the latest NS-C kappa-bias candidate as open, non-promoting, and not proved",
            "C": "pure-stdlib deterministic JSON audit with optional Markdown",
            "S": "Gaussian self-similar balance, OU/Poincare control, drift IBP term, Bias_G-to-Abel mapping, explicit blockers",
            "L": "route status is candidate/open/non-promoting; all proof and Clay promotion flags remain false",
            "P": ROUTE_DECISION,
            "G": "fail closed unless identity fields, blockers, and false promotion flags are present",
            "F": "missing Abel measure construction, Bias_G mapping proof, drift control, stationarity, leakage, and CKN/BKM closure",
        },
    }


def render_markdown(payload: dict[str, Any]) -> str:
    lines = [
        "# NS-C Kappa-Bias Candidate Audit",
        "",
        f"- Decision: `{payload['route_decision']}`",
        f"- Status: `{payload['status']}`",
        f"- Audit passed: `{payload['audit_passed']}`",
        f"- Clay promoted: `{payload['promotion_flags']['clay_navier_stokes_promoted']}`",
        "",
        "## Core Identity",
    ]
    fields = payload["core_identity_fields"]
    for key in [
        "gaussian_weight",
        "omega_energy",
        "gaussian_self_similar_balance_identity",
        "ou_poincare_lower_bound",
        "necessary_normalized_constraint",
        "bias_g_to_abel_integral_mapping",
    ]:
        lines.append(f"- `{key}`: `{fields[key]}`")
    lines.extend(["", "## Blockers"])
    for row in payload["blockers"]:
        lines.append(f"- `{row['blocker_id']}`: {row['missing_witness']}")
    lines.extend(["", "## Control Card"])
    for key, value in payload["control_card"].items():
        lines.append(f"- `{key}`: {value}")
    return "\n".join(lines) + "\n"


def emit(payload: dict[str, Any], args: argparse.Namespace) -> None:
    text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.out_dir is not None:
        args.out_dir.mkdir(parents=True, exist_ok=True)
        (args.out_dir / SUMMARY_NAME).write_text(text, encoding="utf-8")
        if args.markdown:
            (args.out_dir / REPORT_NAME).write_text(render_markdown(payload), encoding="utf-8")
    print(text, end="")


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    payload = build_audit(args.repo_root.resolve())
    emit(payload, args)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

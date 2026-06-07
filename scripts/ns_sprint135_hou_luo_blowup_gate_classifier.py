#!/usr/bin/env python3
"""Sprint 135 Hou-Luo blowup gate classifier.

This emitter records the exact proof gates that remain after the Sprint 134
correction sprint:

* u1 is not a pure diffusion variable;
* Gamma = r u^theta is the maximum-principle variable;
* the uniform no-log axisymmetric Biot-Savart claim is false away from the
  axis; and
* the Hou-Luo axisymmetric Navier-Stokes route is open/live rather than
  obstructed.

The artifact is deliberately bidirectional.  It lists the gates needed to turn
the corrected Hou-Luo route into a genuine finite-time BKM blowup proof, and
the alternative gates that would turn the same route into a regularity
obstruction.  It does not promote Clay or assert that either path is closed.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


CONTRACT = "ns_sprint135_hou_luo_blowup_gate_classifier"
OUT_DIR_DEFAULT = Path("outputs/ns_sprint135_hou_luo_blowup_gate_classifier")
SUMMARY_NAME = CONTRACT + "_summary.json"
ROWS_JSON_NAME = CONTRACT + "_rows.json"
ROWS_CSV_NAME = CONTRACT + "_rows.csv"
REPORT_NAME = CONTRACT + ".md"

ROUTE = "HouLuoAxisymmetricNSRoute"
ROUTE_STATUS = "open_live_candidate"

REQUIRED_BLOWUP_GATES = (
    "LogLossSourceLowerBound",
    "SourceVorticityMaxAlignment",
    "AnnularGammaToU1Persistence",
    "ViscousDampingNonDominance",
    "SelfSimilarScalingClosure",
    "SmoothFiniteEnergyInitialDataConstruction",
    "BKMIntegralDivergenceVerification",
)

REGULARITY_ALTERNATIVE_GATES = (
    "LogLossSourceUpperControl",
    "SourceVorticityMaxDecorrelation",
    "AnnularGammaLeakageOrDiffusiveDecay",
    "ViscousDampingEventualDominance",
    "SelfSimilarScalingExclusion",
    "AxisymmetricContinuationCriterionFromCorrectedVariables",
)


@dataclass(frozen=True)
class HouLuoGate:
    gate_id: str
    gate_name: str
    path: str
    status: str
    route: str
    route_status: str
    corrected_sprint134_dependency: str
    proof_objective: str
    required_estimate_or_construction: str
    existing_repo_support: tuple[str, ...]
    missing_evidence: tuple[str, ...]
    closes_blowup_path_if_proved: bool
    closes_regularity_path_if_proved: bool
    failure_consequence: str
    full_clay_ns_solved: bool
    clay_navier_stokes_promoted: bool

    def as_row(self) -> dict[str, Any]:
        row = asdict(self)
        row["existing_repo_support"] = list(self.existing_repo_support)
        row["missing_evidence"] = list(self.missing_evidence)
        return row


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--out-dir", type=Path, default=OUT_DIR_DEFAULT)
    return parser.parse_args()


def build_rows() -> list[dict[str, Any]]:
    rows = [
        HouLuoGate(
            gate_id="blowup_log_loss_source_lower_bound",
            gate_name="LogLossSourceLowerBound",
            path="blowup",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "NoLogAxisymmetricBiotSavartUniform is false; strain carries "
                "the standard logarithmic loss away from the axis."
            ),
            proof_objective=(
                "Turn the corrected logarithmic Biot-Savart loss from a loose "
                "upper-growth risk into a PDE lower bound for source growth."
            ),
            required_estimate_or_construction=(
                "partial_z(u1^2) produces a positive lower contribution at "
                "the vorticity growth site with at least the log-Gronwall "
                "strength needed to compete with viscosity."
            ),
            existing_repo_support=(
                "Sprint134:BiotSavartLogSingularityAudit",
                "Sprint134:CorrectedSourceGradientLogGronwall",
                "Sprint134:HouLuoRetractionStatus",
            ),
            missing_evidence=(
                "lower-bound sign control",
                "localized kernel positivity or monotone compression estimate",
                "non-cancellation of log-enhanced source",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "The log loss remains only an upper-bound hazard and cannot "
                "support a blowup proof."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="blowup_source_vorticity_max_alignment",
            gate_name="SourceVorticityMaxAlignment",
            path="blowup",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "omega1 evolves by D_t omega1 = partial_z(u1^2) + nu Ltilde omega1."
            ),
            proof_objective=(
                "Show the positive source maximum and the omega1 maximum "
                "remain sufficiently co-located along the candidate singular "
                "trajectory."
            ),
            required_estimate_or_construction=(
                "At times approaching T*, source lower bounds apply at, or "
                "within a controlled parabolic neighborhood of, points where "
                "||omega1||_infty is realized."
            ),
            existing_repo_support=(
                "Sprint128:SourceAlignmentWithVorticityMaximum named gap",
                "Sprint134:AxisymmetricEquationCorrection",
            ),
            missing_evidence=(
                "maximum-point tracking lemma",
                "source-vorticity phase-locking estimate",
                "control of adverse axial sign changes",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "Large source away from the vorticity maximum does not force "
                "BKM divergence."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="blowup_annular_gamma_to_u1_persistence",
            gate_name="AnnularGammaToU1Persistence",
            path="blowup",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "Gamma = r utheta = r^2 u1 satisfies the maximum principle; "
                "u1 control is recovered only on r in [r0,1]."
            ),
            proof_objective=(
                "Construct or prove persistence of a boundary-annulus swirl "
                "profile whose u1 amplitude does not collapse before the "
                "candidate blowup time."
            ),
            required_estimate_or_construction=(
                "There exists r0>0 and c>0 such that |u1| >= c on the active "
                "annular source region for a time sequence approaching T*."
            ),
            existing_repo_support=(
                "Sprint134:SwirlCirculationMaximumPrinciple",
                "Sprint134:BoundaryAnnulusU1Bound",
            ),
            missing_evidence=(
                "lower persistence, not merely upper boundedness",
                "annular support confinement",
                "control of Gamma transport away from the boundary layer",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "Gamma may stay bounded while the active u1 source amplitude "
                "decays or moves out of the annular conversion region."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="blowup_viscous_damping_non_dominance",
            gate_name="ViscousDampingNonDominance",
            path="blowup",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "Sprint134 retracts the old polynomial viscous dominance "
                "comparison because log-Gronwall source factors may be "
                "super-polynomial."
            ),
            proof_objective=(
                "Show viscosity does not dominate the corrected source before "
                "BKM divergence in the live Hou-Luo geometry."
            ),
            required_estimate_or_construction=(
                "Along the candidate profile, positive source production minus "
                "nu Ltilde omega1 remains large enough to drive Omega' >= "
                "c Omega^{1+epsilon} or an equivalent divergent criterion."
            ),
            existing_repo_support=(
                "Sprint131:LocalizedViscousComparison was retracted as an obstruction",
                "Sprint134:HouLuoRetractionStatus",
            ),
            missing_evidence=(
                "signed viscous/source comparison",
                "profile curvature control",
                "localized lower inequality robust under diffusion",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "Even strong formal source growth may be erased by localized "
                "viscous smoothing."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="blowup_self_similar_scaling_closure",
            gate_name="SelfSimilarScalingClosure",
            path="blowup",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "Corrected variables require simultaneous consistency of "
                "Gamma transport, u1 source gradients, omega1 growth, and "
                "log-loss Biot-Savart strain."
            ),
            proof_objective=(
                "Close a finite-dimensional or PDE self-similar scaling system "
                "whose exponents and profiles satisfy the corrected equations."
            ),
            required_estimate_or_construction=(
                "Find alpha, beta, profile shape, annular location, and log "
                "modulation satisfying all source, transport, Biot-Savart, and "
                "viscous scaling constraints."
            ),
            existing_repo_support=(
                "Sprint133:AxisymmetricSwirlTarget finite gates",
                "Sprint134:AxisymmetricEquationCorrection",
                "Sprint134:BiotSavartLogSingularityAudit",
            ),
            missing_evidence=(
                "consistent exponent/log-modulation algebra",
                "profile compactness or stability",
                "boundary compatibility",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "The route may remain a formal amplification story without a "
                "PDE-compatible singular scaling."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="blowup_smooth_finite_energy_initial_data_construction",
            gate_name="SmoothFiniteEnergyInitialDataConstruction",
            path="blowup",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "Any blowup proof must start from smooth divergence-free "
                "finite-energy axisymmetric-with-swirl data, not just an ODE "
                "profile."
            ),
            proof_objective=(
                "Construct initial data that enters the closed Hou-Luo "
                "amplification regime while satisfying all regularity, "
                "boundary, symmetry, and energy constraints."
            ),
            required_estimate_or_construction=(
                "A smooth finite-energy u0 with compatible Gamma, u1, omega1, "
                "and psi1 profiles whose evolution remains in the bootstrap "
                "class until BKM divergence."
            ),
            existing_repo_support=(
                "Sprint133:AxisymmetricNSWithSwirlGlobalRegularity target",
                "Sprint134:Corrected variable definitions",
            ),
            missing_evidence=(
                "compatible divergence-free reconstruction",
                "finite-energy annular profile realization",
                "bootstrap-entry proof",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "A singular profile without admissible smooth data does not "
                "address the Navier-Stokes existence problem."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="blowup_bkm_integral_divergence_verification",
            gate_name="BKMIntegralDivergenceVerification",
            path="blowup",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "The final blowup gate must verify BKM divergence for the "
                "actual PDE solution, not merely source growth."
            ),
            proof_objective=(
                "Convert the closed source/scaling/data bootstrap into "
                "integral divergence of ||omega(t)||_infty before or at T*."
            ),
            required_estimate_or_construction=(
                "integral_0^T ||omega(t)||_infty dt = infinity, with finite "
                "T and smooth finite-energy data on [0,T)."
            ),
            existing_repo_support=(
                "Sprint130-134 promotion guards",
                "BKM criterion used throughout the NS route audits",
            ),
            missing_evidence=(
                "sharp lower growth rate for Omega",
                "continuation-to-singularity argument",
                "exclusion of norm inflation without BKM divergence",
            ),
            closes_blowup_path_if_proved=True,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "The route may produce strong transient amplification without "
                "a Clay-relevant singularity."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="regularity_log_loss_source_upper_control",
            gate_name="LogLossSourceUpperControl",
            path="regularity_alternative",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "The corrected log-loss strain estimate is dangerous only if "
                "it can be saturated by the PDE geometry."
            ),
            proof_objective=(
                "Prove a non-circular upper control showing the log-loss "
                "Gronwall hazard cannot be saturated by smooth finite-energy "
                "axisymmetric-with-swirl solutions."
            ),
            required_estimate_or_construction=(
                "|partial_z(u1^2)| admits an integrable or sub-BKM upper bound "
                "from Gamma control, energy, and axisymmetric structure."
            ),
            existing_repo_support=(
                "Sprint134:Gamma maximum principle correction",
                "Sprint134:log singularity audit",
            ),
            missing_evidence=(
                "energy-to-source continuation estimate",
                "non-saturation of logarithmic Biot-Savart bound",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "The regularity path lacks a replacement for the retracted "
                "viscous dominance theorem."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="regularity_source_vorticity_max_decorrelation",
            gate_name="SourceVorticityMaxDecorrelation",
            path="regularity_alternative",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "Blowup needs source alignment with the omega1 maximum; "
                "regularity can follow from robust misalignment."
            ),
            proof_objective=(
                "Show source peaks and vorticity maxima cannot remain aligned "
                "strongly enough to force BKM divergence."
            ),
            required_estimate_or_construction=(
                "A quantitative decorrelation or sign-oscillation bound for "
                "partial_z(u1^2) at high-omega1 points."
            ),
            existing_repo_support=(
                "Sprint134:source-vorticity alignment listed as live gap",
            ),
            missing_evidence=(
                "axisymmetric maximum-principle geometry for omega1",
                "source sign cancellation estimate",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "The blowup path's alignment gate remains viable."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="regularity_annular_gamma_leakage_or_diffusive_decay",
            gate_name="AnnularGammaLeakageOrDiffusiveDecay",
            path="regularity_alternative",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "Gamma is bounded above, but blowup requires persistent active "
                "annular u1 amplitude."
            ),
            proof_objective=(
                "Prove that active annular u1 amplitude either leaks away from "
                "the Hou-Luo source region or decays under diffusion/transport."
            ),
            required_estimate_or_construction=(
                "A quantitative bound preventing lower persistence of u1 in "
                "the same annular region where omega1 concentrates."
            ),
            existing_repo_support=(
                "Sprint134:BoundaryAnnulusU1Bound",
            ),
            missing_evidence=(
                "lower-amplitude decay mechanism",
                "annular transport leakage estimate",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "Gamma boundedness alone remains compatible with persistent "
                "annular forcing."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="regularity_viscous_damping_eventual_dominance",
            gate_name="ViscousDampingEventualDominance",
            path="regularity_alternative",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "The old polynomial dominance ratio was invalid; a new "
                "dominance result must handle log-loss source growth directly."
            ),
            proof_objective=(
                "Recover an eventual viscous dominance theorem under corrected "
                "source-gradient and log Biot-Savart accounting."
            ),
            required_estimate_or_construction=(
                "nu Ltilde omega1 controls the positive source at the active "
                "scale in every admissible axisymmetric blowup sequence."
            ),
            existing_repo_support=(
                "Sprint131 localized comparison surface as historical scaffold",
                "Sprint134 retraction status identifying the failed assumption",
            ),
            missing_evidence=(
                "log-aware localized parabolic comparison",
                "large-Re transient exclusion",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "Large-Re Hou-Luo transients remain live."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="regularity_self_similar_scaling_exclusion",
            gate_name="SelfSimilarScalingExclusion",
            path="regularity_alternative",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "A live blowup route needs a corrected self-similar or "
                "log-modulated profile; regularity can close by excluding all "
                "such profiles in the axisymmetric class."
            ),
            proof_objective=(
                "Prove no corrected Hou-Luo scaling profile satisfies the "
                "axisymmetric PDE, boundary compatibility, energy, Gamma, and "
                "BKM constraints."
            ),
            required_estimate_or_construction=(
                "A contradiction among exponent/log-modulation constraints or "
                "a compactness theorem ruling out nontrivial ancient profiles."
            ),
            existing_repo_support=(
                "Sprint133:finite axisymmetric target gates",
                "Sprint134:corrected equations",
            ),
            missing_evidence=(
                "profile Liouville theorem",
                "corrected exponent feasibility audit",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=False,
            failure_consequence=(
                "The scaling route remains an admissible organizing ansatz."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
        HouLuoGate(
            gate_id="regularity_axisymmetric_continuation_criterion",
            gate_name="AxisymmetricContinuationCriterionFromCorrectedVariables",
            path="regularity_alternative",
            status="open",
            route=ROUTE,
            route_status=ROUTE_STATUS,
            corrected_sprint134_dependency=(
                "A regularity conclusion must be non-circular and stated in "
                "the corrected variables Gamma, u1, omega1, psi1."
            ),
            proof_objective=(
                "Assemble a continuation criterion for axisymmetric NS with "
                "swirl that follows from corrected-variable estimates rather "
                "than assuming Serrin/BKM control."
            ),
            required_estimate_or_construction=(
                "Energy plus Gamma control plus axisymmetric structure imply a "
                "finite continuation norm up to arbitrary time."
            ),
            existing_repo_support=(
                "Sprint133:axisymmetric-with-swirl global regularity target",
                "Sprint134:corrected Gamma maximum principle",
            ),
            missing_evidence=(
                "non-circular continuation norm",
                "axisymmetric class exhaustion after corrected equations",
            ),
            closes_blowup_path_if_proved=False,
            closes_regularity_path_if_proved=True,
            failure_consequence=(
                "The regularity alternative remains only a list of obstructions "
                "rather than a theorem."
            ),
            full_clay_ns_solved=False,
            clay_navier_stokes_promoted=False,
        ),
    ]
    taxonomy_gates = (
        (
            "corrected_axisymmetric_equations",
            "Corrected axisymmetric equations are the baseline gate for every "
            "post-retraction Hou-Luo argument.",
        ),
        (
            "swirl_circulation_maximum_principle",
            "Gamma, not u1, supplies the corrected maximum-principle control.",
        ),
        (
            "boundary_annulus_u1_bound",
            "Gamma control must be converted to u1 only on r >= r0 annuli.",
        ),
        (
            "log_biot_savart_growth",
            "The restored logarithmic Biot-Savart loss is the live source-growth hazard.",
        ),
        (
            "source_vs_viscosity_model",
            "The source/viscosity phase map separates polynomial and log-Gronwall regimes.",
        ),
        (
            "large_re_transient_control",
            "Large-Re transient growth remains an open Hou-Luo gate.",
        ),
        (
            "marginal_beta_zero_case",
            "The beta=0 boundary case remains separate from beta>0 concentration.",
        ),
        (
            "bkm_blowup_alignment",
            "A Clay-relevant blowup proof still needs source alignment and BKM divergence.",
        ),
    )
    for gate_id, objective in taxonomy_gates:
        rows.append(
            HouLuoGate(
                gate_id=gate_id,
                gate_name=gate_id,
                path="taxonomy",
                status="open",
                route=ROUTE,
                route_status=ROUTE_STATUS,
                corrected_sprint134_dependency=(
                    "Sprint134 corrected equations, false uniform no-log "
                    "Biot-Savart, and Hou-Luo retraction status."
                ),
                proof_objective=objective,
                required_estimate_or_construction=(
                    "Taxonomy row only: refine into one of the concrete "
                    "blowup or regularity gates before any theorem claim."
                ),
                existing_repo_support=(
                    "Sprint134:AxisymmetricEquationCorrection",
                    "Sprint134:BiotSavartLogSingularityAudit",
                    "Sprint134:HouLuoRetractionStatus",
                    "Sprint135:SourceViscosityPhaseMap",
                ),
                missing_evidence=(
                    "concrete PDE estimate",
                    "closed bootstrap or exclusion argument",
                ),
                closes_blowup_path_if_proved=False,
                closes_regularity_path_if_proved=False,
                failure_consequence=(
                    "The umbrella gate remains an organizing label, not a "
                    "closed analytic lemma."
                ),
                full_clay_ns_solved=False,
                clay_navier_stokes_promoted=False,
            )
        )
    return [row.as_row() for row in rows]


def build_summary(rows: list[dict[str, Any]]) -> dict[str, Any]:
    blowup = [row for row in rows if row["path"] == "blowup"]
    regularity = [row for row in rows if row["path"] == "regularity_alternative"]
    open_rows = [row for row in rows if row["status"] == "open"]
    blowup_required = {row["gate_name"] for row in blowup}
    regularity_required = {row["gate_name"] for row in regularity}

    return {
        "contract": CONTRACT,
        "route": ROUTE,
        "route_status": ROUTE_STATUS,
        "gate_count": len(rows),
        "blowup_gate_count": len(blowup),
        "regularity_alternative_gate_count": len(regularity),
        "open_gate_count": len(open_rows),
        "required_blowup_gates_present": all(
            name in blowup_required for name in REQUIRED_BLOWUP_GATES
        ),
        "regularity_alternative_gates_present": all(
            name in regularity_required for name in REGULARITY_ALTERNATIVE_GATES
        ),
        "blowup_path_closed": False,
        "regularity_path_closed": False,
        "corrected_sprint134_assumptions": {
            "u1_pure_diffusion_retracted": True,
            "gamma_is_maximum_principle_variable": True,
            "uniform_no_log_biot_savart_false": True,
            "hou_luo_axisymmetric_ns_route_open_live_candidate": True,
        },
        "highest_alpha_next_gate": "LogLossSourceLowerBound",
        "regularity_fallback_gate": "LogLossSourceUpperControl",
        "full_clay_ns_solved": False,
        "clay_navier_stokes_promoted": False,
        "complete": True,
        "exit_code": 0,
    }


def validate(rows: list[dict[str, Any]], summary: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    if summary["gate_count"] < 8:
        errors.append("gate_count must be at least 8")
    if summary["gate_count"] != len(rows):
        errors.append("summary gate_count does not match row count")
    if not summary["required_blowup_gates_present"]:
        errors.append("not all required blowup gates are present")
    if not summary["regularity_alternative_gates_present"]:
        errors.append("not all regularity alternative gates are present")
    if summary["route_status"] != ROUTE_STATUS:
        errors.append("route_status must remain open_live_candidate")
    for flag in (
        "blowup_path_closed",
        "regularity_path_closed",
        "full_clay_ns_solved",
        "clay_navier_stokes_promoted",
    ):
        if summary[flag] is not False:
            errors.append(f"{flag} must be false")
    if summary["complete"] is not True or summary["exit_code"] != 0:
        errors.append("summary must be complete with exit_code 0")
    for row in rows:
        if row["status"] != "open":
            errors.append(f"{row['gate_id']} must remain open")
        if row["route_status"] != ROUTE_STATUS:
            errors.append(f"{row['gate_id']} route_status changed")
        if row["full_clay_ns_solved"] or row["clay_navier_stokes_promoted"]:
            errors.append(f"{row['gate_id']} promoted Clay incorrectly")
    return errors


def write_json(path: Path, data: Any) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]]) -> None:
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    fieldnames = list(rows[0].keys())
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames)
        writer.writeheader()
        for row in rows:
            serializable = {
                key: json.dumps(value, sort_keys=True) if isinstance(value, (list, dict)) else value
                for key, value in row.items()
            }
            writer.writerow(serializable)


def write_report(path: Path, rows: list[dict[str, Any]], summary: dict[str, Any]) -> None:
    lines = [
        f"# {CONTRACT}",
        "",
        f"- route: `{summary['route']}`",
        f"- route_status: `{summary['route_status']}`",
        f"- gate_count: `{summary['gate_count']}`",
        f"- blowup_path_closed: `{summary['blowup_path_closed']}`",
        f"- regularity_path_closed: `{summary['regularity_path_closed']}`",
        f"- full_clay_ns_solved: `{summary['full_clay_ns_solved']}`",
        f"- clay_navier_stokes_promoted: `{summary['clay_navier_stokes_promoted']}`",
        "",
        "## Corrected Sprint 134 Assumptions",
        "",
    ]
    for key, value in summary["corrected_sprint134_assumptions"].items():
        lines.append(f"- `{key}`: `{value}`")
    lines.extend(
        [
            "",
            "## Gates",
            "",
            "| gate | path | status | objective | missing evidence |",
            "|---|---|---|---|---|",
        ]
    )
    for row in rows:
        missing = "; ".join(row["missing_evidence"])
        lines.append(
            "| {gate} | {path} | {status} | {objective} | {missing} |".format(
                gate=row["gate_name"],
                path=row["path"],
                status=row["status"],
                objective=row["proof_objective"],
                missing=missing,
            )
        )
    lines.append("")
    path.write_text("\n".join(lines), encoding="utf-8")


def main() -> int:
    args = parse_args()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = args.repo_root / out_dir
    out_dir.mkdir(parents=True, exist_ok=True)

    rows = build_rows()
    summary = build_summary(rows)
    errors = validate(rows, summary)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    write_json(out_dir / SUMMARY_NAME, summary)
    write_json(out_dir / ROWS_JSON_NAME, rows)
    write_csv(out_dir / ROWS_CSV_NAME, rows)
    write_report(out_dir / REPORT_NAME, rows, summary)

    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

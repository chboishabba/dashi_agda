#!/usr/bin/env python3
"""EPBC 2019/8575: source-typed proponent evidence and offset model audit.

Original authors: Saunders Havill / Cherish (Springfield and MWW); One
Environment (Avonvale); BAAM (Esk). Applies paired challenge to all MATERIAL
families of proponent evidence, but DOES NOT claim full sentence-by-sentence
coverage of every preliminary-documentation volume or a review of future
approved 15 October 2026 OAMP versions.

Source facts are what those authors REPORT. They are not independently
confirmed fauna observations, viable population estimates, true ecological
occupancy, a re-run OAG, or an agency/court decision. Proponent admissions
against its model do not make the source independently verified either.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path

CASE = "EPBC 2019/8575"
MWW_TABLE44 = (0, 2, 0, 1, 0)
AVONVALE_TABLE33 = (11, 5, 0, 0, 1)
SATS_PER_SITE = 5
TREES_PER_SAT = 30

# Source A16, Table 45. The question is TABLE vs published TOTAL, not
# whether the categorical "presence detected on-site" rubric is lawful.
MWW_A16_COMPONENTS = {
    "presence": (10, 10, 10, 10),       # /10
    "usage": (5, 5, 15, 5),             # /15
    "density": (0, 0, 10, 10),          # /30
    "population_role": (5, 5, 5, 5),   # /15
}
MWW_A16_PUBLISHED_TOTALS = (20, 20, 40, 40)
MWW_A16_PUBLISHED_RESCALED = (1.14, 1.14, 2.29, 2.29)
MWW_A16_PROSE_AU4_USAGE = 15
MWW_METHODOLOGY_IDS = ("T1", "T2", "T3", "T7", "T8")
MWW_LATER_PROSE_IDS = ("T1", "T6", "T7", "T8", "T10")

# A16 Table 13. Credits are percentages of the TOTAL impacted Koala
# quantum, not area fractions. Recorded as hundredths of 1%.
MWW_AREAS_TENTHS = (508, 1047, 620, 81)
MWW_KOALA_CREDIT_BPS = (1634, 3368, 0, 0)
MWW_KOALA_BASELINE_HUNDREDTHS = (340, 344, 651, 671)
MWW_KOALA_FUTURE_HUNDREDTHS = (686, 671, 710, 710)
MWW_QUALITY_CONFIDENCE = (75, 75, 85, 85)
MWW_TIME_TO_BENEFIT_YEARS = 20
MWW_WITHOUT_OFFSET_RISK_LOSS = 0
MWW_WITH_OFFSET_RISK_LOSS = 0

# A16 Table 2 lists 110.89 + 16.13, while main PD Table A26 lists
# 111.87 + 16.13 for the impact site. Source-map reconciliation needed.
A16_TABLE2_IMPACT_HUNDREDTHS = (11089, 1613)
PD_TABLE_A26_IMPACT_HUNDREDTHS = (11187, 1613)

# Mirror the golden Agda's MATERIAL review domain, including decision/
# compliance consumers that must NEVER be sourced from a proponent claim.
FAMILIES = (
    "actionGeometry", "impactKoala", "impactFlyingFox",
    "impactSwiftParrot", "impactRegentHoneyeater",
    "speciesOccurrence", "surveyDesign", "surveySpatialJoin",
    "habitatCondition", "habitatConnectivity", "habitatPopulationFunction",
    "offsetAreaAccounting", "qualityScoring", "futureHabitatValue",
    "futureTreeCounts", "counterfactualRisk", "confidenceAssumptions",
    "ecologicalTimeLag", "ecologicalAdditionality", "proposedMitigation",
    "retainedHabitat", "cumulativeFragmentation", "legalSecurity",
    "declarationsRegistration", "commencementCompliance",
    "financialAgreement", "landTenure", "commentResponses",
    "decisionReasons",
)

# Every family has a falsification/acquisition route and a status. This
# is domain coverage, not a claim that all the source's assertions are paid.
SOURCE_ROUTE = {
    "actionGeometry": "Verify AU polygons, area discrepancy and map versions.",
    "impactKoala": "Independently calibrate 128ha, MHQA 6.78 and local use.",
    "impactFlyingFox": "Verify 128ha, FHA 7.47, seasonal nectar supply and use.",
    "impactSwiftParrot": "Audit 9983 mapped habitat features against tree data.",
    "impactRegentHoneyeater": "Audit 9868 mapped habitat features against tree data.",
    "speciesOccurrence": "Original SAT/photo/GPS; species-use not merely occurrence.",
    "surveyDesign": "Check sampling, 30-tree eligibility and transect IDs.",
    "surveySpatialJoin": "Join each surveyed tree to its assessment-unit polygon.",
    "habitatCondition": "Compare baseline mature structure, food and shelter.",
    "habitatConnectivity": "Map same-action corridor continuity before/after.",
    "habitatPopulationFunction": "Independently test dispersal/breeding/viability.",
    "offsetAreaAccounting": "Verify 3 offset polygons, exclusions and area sums.",
    "qualityScoring": "Reconcile A16 Table 45 sum, AU4 usage and model inputs.",
    "futureHabitatValue": "Independent year-20 quality trajectory and milestones.",
    "futureTreeCounts": "Audit species planting, 80% assumed survival, maturity.",
    "counterfactualRisk": "Check both 0% risk-of-loss inputs and land use baseline.",
    "confidenceAssumptions": "Justify 75/85% future-gain confidence independently.",
    "ecologicalTimeLag": "Distinguish canopy remnant thresholds from mature function.",
    "ecologicalAdditionality": "Deduct pre-existing obligations/protections.",
    "proposedMitigation": "Distinguish promised controls from actual implementation.",
    "retainedHabitat": "Check after-clearing functional corridor, not only area.",
    "cumulativeFragmentation": "Inspect actual Item 4.6(c) action-specific analysis.",
    "legalSecurity": "Obtain s19F declaration and registered legal instruments.",
    "declarationsRegistration": "Match QLD title dealing dates to original polygons.",
    "commencementCompliance": "Find original notifications and verified works.",
    "financialAgreement": "Agreement statement is not bank/payment receipt.",
    "landTenure": "Current titles and subdivision stage, not land name alone.",
    "commentResponses": "Get 95B comment/response bundle, not one-page notice.",
    "decisionReasons": "Get 95C recommendation and genuine consideration evidence.",
}

# Hard categories distinguish reproducible internal faults from hypotheses.
DIRECT_INTERNAL_CONFLICTS = (
    "A16 Table 45 AU4 listed 30/70 vs printed 40/70",
    "A16 A16/PD conflicting AU1 impacted hectares 110.89 vs 111.87",
    "A16 SAT identifiers differ between methodology/table and later prose",
)
MODEL_EXTRAPOLATIONS = (
    "Site-positive scat data assigned 10/10 presence in every MWW AU",
    "Presence on a site != all four AUs occupied or equivalent habitat",
    "AU1/AU2 receive all 50.02% Koala credit despite zero density subscore",
    "Future year-20 quality uplift credited now despite no outcomes yet",
    "75/85% quality confidence and 80% tree survival require calibration",
    "Offset for mobile birds based on suitable/planted foraging resources, not sightings",
)

def arithmetic_checks() -> dict:
    row_sums = tuple(sum(MWW_A16_COMPONENTS[k][j] for k in MWW_A16_COMPONENTS)
                     for j in range(4))
    assert row_sums == (20, 20, 40, 30)
    assert MWW_A16_PUBLISHED_TOTALS == (20, 20, 40, 40)
    assert MWW_A16_PROSE_AU4_USAGE == 15
    assert row_sums[3] != MWW_A16_PUBLISHED_TOTALS[3]
    assert (row_sums[3] + (MWW_A16_PROSE_AU4_USAGE - MWW_A16_COMPONENTS["usage"][3])) == 40

    # Official-style 4/70 subscore rescaling, NOT the OAG percentage.
    corrected_au4_ssr = Fraction(row_sums[3] * 4, 70)
    printed_au4_ssr = Fraction(MWW_A16_PUBLISHED_TOTALS[3] * 4, 70)
    delta = printed_au4_ssr - corrected_au4_ssr
    assert corrected_au4_ssr == Fraction(12, 7)
    assert printed_au4_ssr == Fraction(16, 7)
    assert delta == Fraction(4, 7)

    assert sum(MWW_TABLE44) == 3
    assert sum(1 for n in MWW_TABLE44 if n) == 2
    assert sum(AVONVALE_TABLE33) == 17
    assert sum(1 for n in AVONVALE_TABLE33 if n) == 3
    assert len(MWW_TABLE44) == len(AVONVALE_TABLE33) == SATS_PER_SITE
    assert MWW_METHODOLOGY_IDS != MWW_LATER_PROSE_IDS

    assert sum(MWW_KOALA_CREDIT_BPS) == 5002
    assert sum(MWW_KOALA_CREDIT_BPS[:2]) == 5002
    assert sum(MWW_KOALA_CREDIT_BPS[2:]) == 0
    assert sum(MWW_AREAS_TENTHS) == 2256
    assert (MWW_KOALA_BASELINE_HUNDREDTHS[0],
            MWW_KOALA_BASELINE_HUNDREDTHS[1]) == (340, 344)
    assert sum(A16_TABLE2_IMPACT_HUNDREDTHS) == 12702
    assert sum(PD_TABLE_A26_IMPACT_HUNDREDTHS) == 12800
    assert sum(PD_TABLE_A26_IMPACT_HUNDREDTHS) - sum(A16_TABLE2_IMPACT_HUNDREDTHS) == 98
    assert len(FAMILIES) == len(set(FAMILIES)) == len(SOURCE_ROUTE) == 29

    return {
        "source_checked_contradictions": {
            "mww_A16_table45_recomputed_numerators": row_sums,
            "mww_A16_table45_published_numerators": MWW_A16_PUBLISHED_TOTALS,
            "AU4_table_component_sum_vs_printed_total": [30, 40],
            "AU4_prose_usage_vs_table_usage": [15, 5],
            "AU4_corrected_rescaled_ssr_IF_table_components_control":
                f"{corrected_au4_ssr.numerator}/{corrected_au4_ssr.denominator}",
            "AU4_printed_rescaled_ssr":
                f"{printed_au4_ssr.numerator}/{printed_au4_ssr.denominator}",
            "AU4_component_delta_only":
                f"{delta.numerator}/{delta.denominator}",
            "A16_impact_AU_sum_ha": 127.02,
            "main_PD_A26_impact_AU_sum_ha": 128.0,
            "difference_ha": 0.98,
            "different_MWW_transect_label_lists": True,
        },
        "concentration": {
            "MWW_AU1_and_AU2_of_four_reported_koala_credit_percent": 50.02,
            "MWW_AU3_and_AU4_of_four_reported_koala_credit_percent": 0.0,
            "MWW_AU1_AU2_baseline_density_subscore": [0, 0],
            "MWW_AU1_AU2_presence_subscore": [10, 10],
            "MWW_AU1_AU2_area_ha": 155.5,
            "MWW_total_area_ha": 225.6,
            "AU4_arithmetic_fix_directly_changes_50_02": False,
        },
        "conditional_forecasts_not_observations": {
            "koala_years_to_quality_benefit": MWW_TIME_TO_BENEFIT_YEARS,
            "risk_loss_without_offset_percent": MWW_WITHOUT_OFFSET_RISK_LOSS,
            "risk_loss_with_offset_percent": MWW_WITH_OFFSET_RISK_LOSS,
            "future_quality_confidence_percent": MWW_QUALITY_CONFIDENCE,
            "recalculated_OAG": False,
            "habitat_function_independently_verified": False,
        },
    }

def reference_audit(agda: str | None = None) -> dict:
    checked = arithmetic_checks()
    if agda is not None:
        for tok in (
            "au4TableComponentsSumTo30", "au4TableCannotSumToPublished40",
            "bothLowUseAUsExplainEntirePublishedKoalaCredit",
            "crossTableAreaDifferenceHundredths", "review : EvidenceFamily",
            "noSourcePromotion", "priorLegalHabitatCountermodel",
        ):
            assert tok in agda, tok
        for bad in ("postulate ", "{!!}", "{! !}", "allow-unsolved-metas", "TERMINATING"):
            assert bad not in agda, bad
    return {
        "case": CASE,
        "status": "finite-reference-checks-passed",
        "evidence_status": "proponent-source-reported; not independent",
        "date_of_approval_instrument": "2026-10-16",
        "material_evidence_families_covered": len(FAMILIES),
        "families_and_next_evidence": SOURCE_ROUTE,
        "hard_source_internal_conflicts": DIRECT_INTERNAL_CONFLICTS,
        "proponent_model_extrapolation_questions": MODEL_EXTRAPOLATIONS,
        "calculations": checked,
        "illustration_only_not_project_data": {
            "one_positive_tree_of_one_sampled_tree_positive_fraction": "1/1",
            "inference_to_100_percent_occupied_habitat": False,
            "real_SAT_protocol_not_one_tree_sample": True,
        },
        "must_not_promote_to": [
            "actual koala population density",
            "AU-wide absence or presence in a spatially unjoined assessment",
            "independently validated ecology",
            "adjusted OAG percentages",
            "registered declarations, compliance breach or court finding",
            "financial consideration or transaction",
        ],
        "exact_approved_OAMP_version_reconciled": False,
        "agda_source_contract_checked": agda is not None,
        "agda_kernel_verified": False,
    }

def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument("--agda-file", type=Path)
    ap.add_argument("--output", type=Path)
    args=ap.parse_args()
    result=reference_audit(args.agda_file.read_text() if args.agda_file else None)
    payload=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.output: args.output.write_text(payload)
    print(payload,end="")

if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""EPBC 2019/8575 independent-professional/community adversarial audit.

Original authors: Monica Taylor, Rowena Maguire, Bridget Lewis (QUT School
of Law submission, 12 March 2026); Anthony Gough (QCC submission, 12 March
2026). This is a source-typed interrogation, not an ungrounded popularity
vote. Do not silently turn submitted opinions into field measurements or
binding legal findings. Treat proponent studies as interested model
assertions and verify direct source contradictions on their own terms.

References:
QUT original:
https://img1.wsimg.com/blobby/go/c204ebbc-02bb-46d9-ad71-ed7d494e752a/QUT%20LTR%20EPBC%20referral%20Woogaroo%20-%2012032026.pdf
QCC original:
https://assets.nationbuilder.com/queenslandconservation/pages/4724/attachments/original/1773626602/QCC-Submission-EPBC-2019_8575-SpringviewVillage-Stages-2-3-WoogarooCreekForestLandscape.pdf
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
import argparse
import json
from pathlib import Path

CASE = "2019/8575"
QUT = "QUT School of Law, Taylor/Maguire/Lewis, 12 March 2026"
QCC = "Queensland Conservation Council, Anthony Gough, 12 March 2026"
RSPCA = "RSPCA Queensland, Emma Lagoon, April-June 2025"
HOLDING = "Shannon Mooney and Andrew Davidson, QCC commissioned Holding the Line v2.0, 31 August 2023"

@dataclass(frozen=True)
class Claim:
    id: str
    original_author: str
    observed_source_class: str
    claimed: str
    original_field_receipt: bool
    same_action: bool
    legal_or_agency_finding: bool
    counter_evidence_required: str

LEADS=(
    Claim("QUT.01",QUT,"independent_professional_original_submission",
          "mature eucalypt canopy, shaded gullies and riparian heat/moisture refuges are site functions",
          False,True,False,"same-site current remote-sensing, floristic/thermal plot, food chemistry and climate refuge survey"),
    Claim("QUT.02",QUT,"independent_professional_original_submission",
          "movement-home-range/thermal-refuge model not credibly provided; corridor loss",
          False,True,False,"full original commissioned movement model, telemetry, riparian/canopy connectivity before-after"),
    Claim("QUT.03",QUT,"independent_professional_original_submission",
          "396 ha prior regional clearance, 500 ha connected block and associated cumulative risk",
          False,True,False,"dated disturbance GIS polygons and C4 lineage; distinguish prior actions from 2019/8575 impacts"),
    Claim("QCC.01",QCC,"independent_peak_body_original_submission",
          "Woogaroo Creek-Opossum Creek habitat corridor and fragmentation",
          False,True,False,"local-movement habitat polygons, telemetry, DEM, offsite genetic/viability joins"),
    Claim("QCC.02",QCC,"independent_peak_body_original_submission",
          "survey effort insufficient for hollow-dependent arboreal fauna",
          False,True,False,"original survey timetable/protocol, current spotlighting/acoustic/camera data and hollow inventory"),
    Claim("QCC.03",QCC,"independent_peak_body_original_submission",
          "RSPCA reportedly treated and returned koalas to the site",
          False,True,False,"dated RSPCA case records and releases with exact project polygon and privacy controls"),
    Claim("QCC.04",QCC,"independent_peak_body_original_submission",
          "Ipswich ~21% native vegetation; 30% minimum-function heuristic",
          False,True,False,"original Holding the Line denominator, date, scale, uncertainty and threshold literature"),
    Claim("QCC.05",QCC,"independent_peak_body_original_submission",
          "Woogaroo overlap with irreplaceable red-zone habitat",
          False,True,False,"original Bioregional Planning report's polygons and formal same-action spatial intersection"),
)

# Claim types must not be collapsed merely because they all concern koalas.
FUNCTIONS = {
    "mature_canopy": "QUT.01",
    "thermal_refuge": "QUT.01",
    "local_corridor_connectivity": "QUT.02",
    "regional_fragmentation": "QUT.03",
    "survey_exclusion_reliability": "QCC.02",
    "observed_released_koalas": "QCC.03",
    "regional_landscape_cover": "QCC.04",
    "irreplaceable_function_red_zone": "QCC.05",
}
PROXY_COVERAGE={
    "OAG_koala_quality_score": {"mature_canopy":False,"thermal_refuge":False,
                                 "local_corridor_connectivity":False,
                                 "observed_released_koalas":False},
    "OAG_bird_future_feature_count":{"thermal_refuge":False,
        "irreplaceable_function_red_zone":False,"local_corridor_connectivity":False},
    "OAG_percent_compensated":{"mature_canopy":False,
        "thermal_refuge":False,"local_corridor_connectivity":False,
        "regional_fragmentation":False},
}
# False means 'no logical entailment from this proxy alone', not proof of
# biological impossibility or definitive claim that source authors are right.
NON_ADJUDICATIVE=("community_submitted","original_professional_opinion",
                  "proponent_source_assertion","government_original_instrument")

def run():
    assert len(LEADS)==8
    assert len({l.id for l in LEADS})==len(LEADS)
    assert all(l.same_action for l in LEADS)
    assert all(l.original_author in (QUT,QCC) for l in LEADS)
    assert all(not l.original_field_receipt for l in LEADS)
    assert all(not l.legal_or_agency_finding for l in LEADS)
    assert sum(l.original_author==QUT for l in LEADS)==3
    assert sum(l.original_author==QCC for l in LEADS)==5
    assert set(FUNCTIONS.values()).issubset({l.id for l in LEADS})
    assert all(not value for coverage in PROXY_COVERAGE.values() for value in coverage.values())

    # Source acquisition has advanced beyond QCC's secondhand account:
    # RSPCA Queensland public articles directly attest return of Maximus
    # to Woogaroo and William to bordering Woogaroo woodland, but do not
    # provide treatment case IDs or selected EPBC impact polygon GPS.
    original_organisation_records = {
        "maximus": {"publisher": RSPCA, "publication_date": "2025-06-02",
            "source_url": "https://www.rspcaqld.org.au/resources/wildlife/maximus-the-koala-returns-to-woogaroo-forest-MCFYVERYNGXNCQBFHBTLBTRMTCG4",
            "reported_return_location": "Woogaroo Forest",
            "2019_8575_impact_polygon_matched": False,
            "original_clinical_case_ID_obtained": False},
        "william": {"publisher": RSPCA, "publication_date": "2025-04-11",
            "source_url": "https://www.rspcaqld.org.au/resources/wildlife/william-the-koala-returns-home-MCTXS73T5DCJB27OKMKOYOXCLEEE",
            "reported_return_location": "bordering Woogaroo Forest",
            "2019_8575_impact_polygon_matched": False,
            "original_clinical_case_ID_obtained": False},
    }
    holding_original = {
        "authors": HOLDING,
        "source_url": "https://assets.nationbuilder.com/queenslandconservation/pages/5629/attachments/original/1694603342/QCC_Holding_The_Line_Reversing_Biodiversity_Decline.pdf",
        "original_page":31,
        "source_table":"Table 8, vegetation extent by region and LGA (HLW 2021)",
        "council":"Ipswich City",
        "council_area_ha":109315,
        "percentage_remnant_vegetation":21,
        "data_basis_year":2021,
        "is_same_as_2019_8575_impact_polygon":False,
        "is_2026_updated_vegetation_measurement":False,
        "is_universal_legal_30_percent_threshold":False,
    }
    assert set(original_organisation_records)=={"maximus","william"}
    assert holding_original["percentage_remnant_vegetation"]==21
    assert not any(v["2019_8575_impact_polygon_matched"] for v in original_organisation_records.values())

    # Adversarial burden is claim-specific, not a credibility ranking
    # based merely on being a campaigning organisation, academic or
    # commissioned consultant. Primary proof of original authored speech
    # is already paid; independently observed underlying site effect isn't.
    return {
        "case":CASE,
        "original_independent_written_submissions":2,
        "leads":len(LEADS),
        "original_QUT_leads":3,
        "original_QCC_leads":5,
        "lead_records":[asdict(x) for x in LEADS],
        "new_primary_RSPCA_organisation_reports":original_organisation_records,
        "QCC_commissioned_original_remnant_report":holding_original,
        "ecological_function_distinctions":FUNCTIONS,
        "automatic_proxy_to_function_inference_prohibited":PROXY_COVERAGE,
        "material_scope_gates":[
          "QUT cites 136ha mature forest, proponent OAG assesses 128ha: compare exact geometry/scope and dates, do not assume numeric contradiction",
          "QUT cites 500ha functional block: establish GIS polygon, not identical 2019/8575 approved impact",
          "QUT cites 396ha regional historical clearing: context, not same-action 2019/8575 authorized area",
          "QCC 21% original report/HLW 2021 Table 8 located; original mapping layer and site polygon still needed; 30% is not an automatic legal threshold",
          "QCC relay corroborated by RSPCA original public reports for Maximus/William; clinical case IDs and EPBC 2019/8575 polygon remain open",
          "QUT cites Possingham/Zdenek: explicit author or cross-project DOI/record required before treating them as individual authors of QUT submission",
          "Save Woogaroo submission index includes Scenic 2020/8651 and Peninsula 2020/8629 documents: do not convert to 2019/8575",
        ],
        "review_status":{
          "original_author_submissions_in_hand":True,
          "underlying_direct_observation_for_all_leads":False,
          "independent_RSPCA_original_public_organisation_reports_found":True,
          "QCC_commissioned_2023_report_original_found":True,
          "agency_consideration_in_95C_or_95B":False,
          "approved_15October_offset_calculator_reconciled":False,
          "legally_decided":False
        },
        "agda_kernel_verified":False,
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--agda-file",type=Path)
    ap.add_argument("--output",type=Path)
    a=ap.parse_args()
    if a.agda_file:
        txt=a.agda_file.read_text()
        for k in ("qutCorridor","qutClimate","qutCumulative","qccConnectivity",
                  "qccSurvey","qccRescue","qccLandscape","qccRedZone", "rspcaMaximusDirectOriginal",
                  "rspcaWilliamDirectOriginal", "holdingTheLineOriginal",
                  "noAutomaticMatureForestEquivalence","noAutomaticCorridorEquivalence",
                  "noAutomaticClimateRefugeEquivalence","priorQUTAttribution"):
            assert k in txt,k
        assert "postulate " not in txt and "{!!}" not in txt
    obj=run()
    obj["agda_source_contract_checked"]=a.agda_file is not None
    j=json.dumps(obj,indent=2,sort_keys=True)+"\n"
    if a.output:a.output.write_text(j)
    print(j,end="")
if __name__=="__main__":main()

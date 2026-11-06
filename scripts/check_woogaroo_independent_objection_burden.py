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
        "ecological_function_distinctions":FUNCTIONS,
        "automatic_proxy_to_function_inference_prohibited":PROXY_COVERAGE,
        "material_scope_gates":[
          "QUT cites 136ha mature forest, proponent OAG assesses 128ha: compare exact geometry/scope and dates, do not assume numeric contradiction",
          "QUT cites 500ha functional block: establish GIS polygon, not identical 2019/8575 approved impact",
          "QUT cites 396ha regional historical clearing: context, not same-action 2019/8575 authorized area",
          "QCC cites Ipswich ~21% native cover and generic 30% ecological heuristic: obtain denominator and species-specific support",
          "QCC relays RSPCA rescue/return: seek original field case before claiming exact on-site rescue",
          "QUT cites Possingham/Zdenek: explicit author or cross-project DOI/record required before treating them as individual authors of QUT submission",
          "Save Woogaroo submission index includes Scenic 2020/8651 and Peninsula 2020/8629 documents: do not convert to 2019/8575",
        ],
        "review_status":{
          "original_author_submissions_in_hand":True,
          "underlying_direct_observation_for_all_leads":False,
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
                  "qccSurvey","qccRescue","qccLandscape","qccRedZone",
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

#!/usr/bin/env python3
"""EPBC 2019/8575, additional adversarial decision tests (source-typed).

The original QUT/QCC case-specific submissions and independent RSPCA public
wildlife sources outrank unsupported proponent *inferences* as evidence of
what those independently authored materials state, without turning QCC
hearsay or professional opinion into verified GPS/field observations.
Original 2012 EPBC offset principles govern the policy check: the 2026
National Environmental Standard has been registered/in force since Aug,
but the Department says its new approval tests were NOT yet operative on
the 16 Oct 2026 decision. Only authorised original legislation/transition
texts could settle legal applicability, not this model.

No actual 2019/8575 clearing, breach, registered declarations, fraud,
s95C consideration, filed case or judgment is derived from these tests.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path

CASE="EPBC 2019/8575"
TESTS={
"sameProtectedAttribute":{
    "origin":"2012 policy principle 1 / QUT and QCC",
    "falsifier":"mapped pre-impact mature feeding/breeding/corridor function and equivalent offset function", "status":"OPEN"},
"directVsIndirectAndResidual":{
    "origin":"2012 policy principle 2",
    "falsifier":"same-action 90-percent-direct requirement plus lawful indirect balance, not 100-percent-direct automatic rule", "status":"OPEN"},
"avoidanceBeforeOffsets":{
    "origin":"2012 policy hierarchy / QUT",
    "falsifier":"every feasible avoidance and mitigation alternative spatially compared before residual", "status":"OPEN"},
"localConnectivityCounterfactual":{
    "origin":"QUT/QCC 12 March 2026",
    "falsifier":"matched before/after local koala movement, corridor graph and road/mortality risks", "status":"OPEN"},
"sameHabitatMaturityAndThermalRefuge":{
    "origin":"QUT",
    "falsifier":"heat/moisture refuge, hollows, mature trees and seasonal food at site and offset", "status":"OPEN"},
"sourceAreaAndBoundaryConsistency":{
    "origin":"QUT 136ha/26ha and January 2026 PD 128ha/127.02ha",
    "falsifier":"definition and spatial overlay of same date/scope/action polygons", "status":"OPEN"},
"temporalSurvivalAndTimeLag":{
    "origin":"MWW/Avonvale OAMP, 20-year model",
    "falsifier":"actual survival/flowering/quality trajectory and confidence calibration", "status":"OPEN"},
"impactOffsetAsymmetricScoring":{
    "origin":"PD A16 3/150 SAT, 10/10 all four AU; AU4 30 vs 40",
    "falsifier":"same-method impact/offset scoring, GPS-AU join and actual OAG cells", "status":"SOURCE_CONTRADICTION_PAID"},
"speciesStatusAndTransitionLaw":{
    "origin":"2019 Vulnerable/0.2 versus 2022 Endangered/1.2",
    "falsifier":"applicable saved/transitional law and actual delegate worksheet/reasons", "status":"CONDITIONAL_NUMERICAL_CUT"},
"sourceIndependenceAndDeduplication":{
    "origin":"RSPCA original 2025 Impact Report and wildlife stories",
    "falsifier":"released animals' original GPS/case ID exact 2019/8575 footprint", "status":"FOREST_LEVEL_DIRECT_ORGANISATION_REPORT"},
"priorOffsetsAndAdditionality":{
    "origin":"2012 policy principle 6 / Avonvale prior projects",
    "falsifier":"registered historical polygons, independent extra benefit and obligations", "status":"OPEN"},
"legallySecuredBeforeRelevantImpact":{
    "origin":"16 Oct 2026 Annexure A conditions 24-27",
    "falsifier":"section 19F declarations and dated phase-specific commencement/works records", "status":"OPEN"},
"meaningfulMonitoringAndRemedy":{
    "origin":"Annexure A conditions 48-69 / 2012 policy principles 7-8",
    "falsifier":"verified monitoring, milestones, trigger/remedy and actual works", "status":"OPEN"},
"completeCommentsAndDecisionConsideration":{
    "origin":"95B one-page notice for 1786 comments; signed approval",
    "falsifier":"whole original 95B comment + response package, 95C and actual consideration", "status":"OPEN"},
}
RSPCA={
 "original_reports":[
   {"publisher":"RSPCA Queensland","source":"2025 Impact Report p 11",
    "forest":"Woogaroo Forest","named_animals":["Maximus","William"],
    "exact_2019_8575_polygon":False},
   {"publisher":"RSPCA Queensland","source":"Maximus article 2 June 2025",
    "forest":"Woogaroo Forest","exact_2019_8575_polygon":False},
   {"publisher":"RSPCA Queensland","source":"William article 11 April 2025",
    "forest":"bordering Woogaroo Forest","exact_2019_8575_polygon":False}
 ],
 "independent_organisation_confirmation_of_forest_level_release":True,
 "number_of_independent_released_animals_in_reports":2,
 "case_or_geotag_coordinates_received":False
}
POLICY={
 "2012_environmental_offsets_policy":{
  "principle_1_same_attribute":True,"principle_2_direct_90_norm":True,
  "principle_6_additionality":True,"principle_7_timely_scientifically_robust":True,
  "principle_8_transparent_measurement_enforcement":True},
 "F2026L01093":{
  "registered":"2026-08-21","whole_instrument_commenced":"2026-08-22",
  "decision_date":"2026-10-16",
  "department_says_new_tests_not_applied_yet":True,
  "automatic_binding_in_october_approval":False,
  "legal_savings_or_transition_finalised_here":False}
}
def run():
 assert len(TESTS)==14
 assert len(set(TESTS))==len(TESTS)
 assert len(RSPCA["original_reports"])==3
 assert RSPCA["number_of_independent_released_animals_in_reports"]==2
 assert all(not x["exact_2019_8575_polygon"] for x in RSPCA["original_reports"])
 assert POLICY["F2026L01093"]["automatic_binding_in_october_approval"] is False
 assert POLICY["F2026L01093"]["registered"] < POLICY["F2026L01093"]["decision_date"]
 assert TESTS["speciesStatusAndTransitionLaw"]["status"]=="CONDITIONAL_NUMERICAL_CUT"
 assert TESTS["impactOffsetAsymmetricScoring"]["status"]=="SOURCE_CONTRADICTION_PAID"
 assert set(x["status"] for x in TESTS.values()) <= {
     "OPEN","SOURCE_CONTRADICTION_PAID","CONDITIONAL_NUMERICAL_CUT",
     "FOREST_LEVEL_DIRECT_ORGANISATION_REPORT"}
 assert all("falsifier" in x for x in TESTS.values())
 return {"case":CASE,"material_decisive_tests":len(TESTS),"tests":TESTS,
   "RSPCA":RSPCA,"policy_date_guard":POLICY,
   "new_sources_not_assigned_2019_8575_polygon_automatically":True,
   "full_OAG_56_AU_row_source_audit_exists":True,
   "functional_equivalence_observation_witness_supplied":False,
   "independent_community_field_GPS_supplied":False,
   "actual_approved_OAMP_version_join":False,
   "section95C_decision_reasoning_received":False,
   "Queensland_section19F_registered_declarations_received":False,
   "compliance_breach_observed":False,
   "all_tests_empirically_closed":False,
   "agda_kernel_verified":False}
def main():
 p=argparse.ArgumentParser()
 p.add_argument("--agda-file",type=Path)
 p.add_argument("--out",type=Path)
 a=p.parse_args()
 if a.agda_file:
  s=a.agda_file.read_text()
  for marker in ["challengeFor : Test → Challenge","rspcaForestLevelConfirmedByOrganisation",
    "doNotPromoteRegistered2026StandardToOctoberBinding",
    "priorAU4Contradiction","sameProtectedAttribute","completeCommentsAndDecisionConsideration"]:
   assert marker in s,marker
  assert not any(z in s for z in ["postulate ","{!!}","allow-unsolved-metas"])
 o=run()
 o["agda_source_marker_check"]=bool(a.agda_file)
 encoded=json.dumps(o,indent=2,sort_keys=True)+"\n"
 if a.out:a.out.write_text(encoded)
 print(encoded,end="")
if __name__=="__main__":main()

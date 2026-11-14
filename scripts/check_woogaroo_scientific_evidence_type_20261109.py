#!/usr/bin/env python3
"""EPBC 2019/8575: evidence-type cut for source-reported MWW forecasts.

January 30 2026 Saunders Havill MWW OAMP Tables 12-13 and Appendix A:
- 20-year regrowth proposed to qualify as remnant using canopy
  structure benchmarks (>=50% cover and >=70% benchmark height).
- MWW AU1: 3.40 -> 6.86; AU2 3.44 -> 6.71; rounded OAG 3 -> 7.
- 75% confidence in non-remnant AU future habitat quality, attributed
  by proponent to rehabilitation plan. NOT an independent observed
  frequency of restored/koala-used sites.
- Signed Part 9 16 Oct 2026 defines LATER MWW OAMP Issue D dated
  15 Oct 2026, so these January rows cannot be presumed operative.

No assertion of empirical falsehood, fraud, 2019/8575 breach or
unlawful approval without admitted originals and independent expertise.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse,json

SOURCES={
  "January_MWW_AU1":{"baseline":F("3.40"),"year20":F("6.86"),"OAG_rounded_baseline":3,"OAG_rounded_year20":7,"area":F("50.8"),"confidence":F("0.75")},
  "January_MWW_AU2":{"baseline":F("3.44"),"year20":F("6.71"),"OAG_rounded_baseline":3,"OAG_rounded_year20":7,"area":F("104.7"),"confidence":F("0.75")},
}
REQUIRED_WELDS=[
  "exact_official_october_approved_9612_E_Issue_D_source",
  "native_baseline_transects_and_location",
  "field_calibrated_year5_10_15_20_growth_survival",
  "independent_confidence_interval_method_for_75_percent",
  "actual_koala_occurrence_abundance_breeding_or_dispersal",
  "heat_refuge_microclimate_and_same_attribute_equivalence",
  "authorised_minister_writing_if_offset_plan_revised",
]
def run():
  assert len(SOURCES)==2
  assert all(x["OAG_rounded_year20"]-x["OAG_rounded_baseline"]==4 for x in SOURCES.values())
  assert SOURCES["January_MWW_AU1"]["year20"]-SOURCES["January_MWW_AU1"]["baseline"]==F("3.46")
  assert SOURCES["January_MWW_AU2"]["year20"]-SOURCES["January_MWW_AU2"]["baseline"]==F("3.27")
  assert sum(x["area"] for x in SOURCES.values())==F("155.5")
  assert all(x["confidence"]==F("0.75") for x in SOURCES.values())
  assert sum(x["area"]*4*75*10 for x in SOURCES.values())==466500
  return {
    "case":"EPBC 2019/8575",
    "source_revision":"January 2026 Preliminary Documentation v5 MWW plan (historical)",
    "signed_approval_MWW_revision":"9612-E Issue D, 15 October 2026 (not received/verified)",
    "structural_remnant_mapping_benchmark":{"cover_fraction":"0.50","height_fraction":"0.70","year":20},
    "remnant_benchmark_proves_koala_function_alone":False,
    "AU_reported_gains":{k:{"unrounded":str(v["year20"]-v["baseline"]),"rounded":4,"confidence":str(v["confidence"])} for k,v in SOURCES.items()},
    "proponent_jan_MWW_quality_input_coefficient":466500,
    "independently_calibrated_75_percent_success_probability_received":False,
    "current_signed_OAMP_in_hand":False,
    "distinct_evidence_welds":REQUIRED_WELDS,
    "all_welds_paid":False,
    "current_actual_site_breach":None,
    "Agda_typechecked":False,
  }
def main():
 p=argparse.ArgumentParser()
 p.add_argument("--agda-file",type=Path)
 p.add_argument("--out",type=Path)
 a=p.parse_args()
 if a.agda_file:
  s=a.agda_file.read_text()
  for term in ("structuralBenchmarksSource","planSupportsForecastAsProponentClaim",
               "confidenceIsProponentAssertionNotIndependentlyCalibrated",
               "originalSignedPlanIdentityIsStillOpen",
               "originalJanuaryAreaCoefficient"):
   assert term in s,term
  assert "{!!}" not in s and "postulate " not in s
 obj=run()
 obj["agda_source_contract_checked"]=bool(a.agda_file)
 data=json.dumps(obj,indent=2,sort_keys=True)+"\n"
 if a.out:a.out.write_text(data)
 print(data,end="")
if __name__=="__main__":main()

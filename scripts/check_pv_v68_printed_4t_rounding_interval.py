#!/usr/bin/env python3
"""M2 strictly separate source-printed precision from measurement uncertainty.

The 2026 Green v68 Table 4 NREL GaInP/GaAs//Si 4T mechanical stack reports
35.9±0.5% PCE under one-sun same designated area. Two published electrical
group values (Voc,Jsc,FF) can only reproduce a rounded sum, not an exact
calibrated instrument receipt. Treat each displayed decimal as rounding to
nearest ONE LAST PRINTED DIGIT and compute the sharp rectangular source
interval by exact Fraction rational arithmetic.

The resulting rounding envelope is NOT a confidence interval or certified
laboratory uncertainty. Physical source, aperture, IV/MPPT and 369 gates
remain unsatisfied. No measurements are synthesized.
"""
from fractions import Fraction as F
import json

SOURCE="https://doi.org/10.1016/j.joule.2026.102494"
DATA=[
    {"contact":"GaInP/GaAs top","voc":"2.52","jsc":"13.6","ff":"87.5"},
    {"contact":"Si bottom","voc":"0.681","jsc":"11.0","ff":"78.5"},
]
PUBLISHED_PCE="35.9"
PUBLISHED_UNCERTAINTY_PP="0.5"

def displayed_interval(s):
    if not isinstance(s,str) or not s or s.count(".")>1:
        raise ValueError("explicit decimal source string required")
    d=len(s.split(".")[1]) if "." in s else 0
    radius=F(1,2*10**d)
    midpoint=F(s)
    if midpoint<radius:raise ValueError("negative optical or electrical source parameter")
    return midpoint-radius,midpoint+radius

def mpp_from_print(voc,jsc,ff):
    return voc*jsc*ff/F(100)

def identity():
    check=[]
    def ck(label,ok):
        assert bool(ok),label
        check.append(label)
    lo=F(0);hi=F(0);mid=F(0);parts=[]
    for row in DATA:
        bounds=[displayed_interval(row[k]) for k in ("voc","jsc","ff")]
        m=mpp_from_print(*(F(row[k]) for k in ("voc","jsc","ff")))
        low=mpp_from_print(*(x[0] for x in bounds))
        high=mpp_from_print(*(x[1] for x in bounds))
        ck(row["contact"]+" midpoint in printed precision range",low<=m<=high)
        ck(row["contact"]+" all values positive",low>0)
        ck(row["contact"]+" positive roundoff width",high>low)
        parts.append({"contact":row["contact"],"printed_Voc":row["voc"],
            "printed_Jsc_mA_cm2":row["jsc"],"printed_FF_percent":row["ff"],
            "printed_central_reconstructed_pce_pp":float(m),
            "rounding_only_lower_pce_pp":float(low),
            "rounding_only_upper_pce_pp":float(high)})
        lo+=low;hi+=high;mid+=m
    reported=F(PUBLISHED_PCE)
    ck("published report enclosed by displayed field rounding",lo<=reported<=hi)
    ck("published 35.9 is not exact printed multiplication",mid!=reported)
    ck("central 4T printed sum",mid==F("35.868435"))
    ck("central 4T published difference",reported-mid==F("0.031565"))
    ck("rounding-only lower exact",lo==F("35.6471117625"))
    ck("rounding-only upper exact",hi==F("36.0904685375"))
    ck("rounded data interval not reported certified uncertainty",hi-lo!=F(PUBLISHED_UNCERTAINTY_PP)*2)
    ck("conventional 4T upper remains below 50%",hi<50)
    ck("the 4T consists of two independently contacted groups",len(DATA)==2)
    return {"all_passed":True,"checks_passed":len(check),
      "publication":"Green et al. Joule 2026 Solar Cell Efficiency Tables v68 Table 4",
      "source_url":SOURCE,"device":"NREL Feb 2017 GaInP/GaAs//Si 4T",
      "rounding_model":"nearest last displayed decimal digit; independent rectangular uncertainty in PRINTED FIELDS, NOT instrument confidence",
      "groups":parts,
      "reconstructed_midpoint_pce_percent":float(mid),
      "publication_precision_lower_pce_percent":float(lo),
      "publication_precision_upper_pce_percent":float(hi),
      "independent_reported_pce_percent":float(reported),
      "published_plus_minus_uncertainty_percentage_points":float(F(PUBLISHED_UNCERTAINTY_PP)),
      "measured_IV_data_supplied":False,
      "independent_certification_created_by_this_script":False,
      "369_specific_material_advantage_measured":False,
      "checks":check}
if __name__=="__main__":
    print(json.dumps(identity(),indent=2))

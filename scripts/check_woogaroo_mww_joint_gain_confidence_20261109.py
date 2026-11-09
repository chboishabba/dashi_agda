#!/usr/bin/env python3
"""Exact joint gain/confidence audit for historical January 2026 OAG.

EPBC 2019/8575. Attribution remains BAAM Esk, One Environment Avonvale,
Saunders Havill Mount Walker West, QUT Taylor/Maguire/Lewis, QCC Gough.
The October 2026 approved plan/workbook is a DIFFERENT unverified version.
Arithmetic sensitivity is not an observed ecological success or failure,
legal invalidity, condition breach, court filing or agency decision.
"""
from fractions import Fraction as F
import json
import argparse
from pathlib import Path

P = 1000**20
D = 8960*(1002**20)
OTHER = 543850
MWW_AREA_TENTHS = 1555

def percent(gain, confidence):
    return F((OTHER + MWW_AREA_TENTHS*gain*confidence)*P, D)

def required_confidence(target, gain):
    return (F(target*D, P)-OTHER)/(MWW_AREA_TENTHS*gain)

WITNESSES = [
    (4,50,90, "above",15573718717785965077071123936135752170135771728773576333564313600),
    (4,50,100,"below",77679201424682261025476528959849164255404698079140470740484096000),
    (4,60,100,"below",15479201424682261025476528959849164255404698079140470740484096000),
    (4,65,100,"above",15620798575317738974523471040150835744595301920859529259515904000),
]

def check():
    rows = []
    for gain, confidence, target, relation, diff in WITNESSES:
        lhs = (OTHER + MWW_AREA_TENTHS*gain*confidence)*P
        delta = lhs-target*D
        assert (delta>0) == (relation == "above")
        assert abs(delta) == diff
        rows.append({"gain":gain,"confidence_percent":confidence,
            "comparison_target_percent":target,"relation":relation,
            "exact_nat_witness":str(diff),
            "model_compensation_percent":f"{float(percent(gain,confidence)):.10f}"})
    # Finite no-inverse counterexample: the coefficient and discounted
    # outcome alone cannot identify gain, confidence or scenario selection.
    indistinguishable=[(4,75),(3,100),(5,60)]
    coefficients=[OTHER+MWW_AREA_TENTHS*g*c for g,c in indistinguishable]
    assert coefficients==[1010350]*3
    assert len({g for g,c in indistinguishable})==3
    assert len({c for g,c in indistinguishable})==3
    assert len({percent(g,c) for g,c in indistinguishable})==1
    assert percent(4,75) > 100
    assert percent(3,75) > 90 > percent(2,75)
    assert 47 < required_confidence(90,4) < 48
    assert 62 < required_confidence(100,4) < 63
    return {"case":"EPBC 2019/8575","source":"30 January 2026 PD v5; NOT accepted 15 October workbook",
      "target_90_percent_required_confidence_given_gain4":f"{float(required_confidence(90,4)):.10f}",
      "target_100_percent_required_confidence_given_gain4":f"{float(required_confidence(100,4)):.10f}",
      "same_output_distinct_parameters":{
          "parameter_pairs":[{"gain":g,"confidence_percent":c} for g,c in indistinguishable],
          "common_coefficient":coefficients[0],
          "same_discounted_output":True,
          "cannot_identify_optimiser_or_scientific_justification_from_output_alone":True
      },
      "proponent_january_assumption":{"MWW_AU1_AU2_common_gain":4,"confidence_percent":75},
      "exact_integer_witnesses":rows,
      "scientific_probability_calibration_or_independent_koala_evidence_obtained":False,
      "approved_OAMP_2026_verified":False,"agda_kernel_verified":False}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--agda-file",type=Path)
    parser.add_argument("--out",type=Path)
    args=parser.parse_args()
    if args.agda_file:
        content=args.agda_file.read_text()
        for marker in ("fiftyAbove90Exact","fiftyBelow100Exact",
                       "sixtyBelow100Exact","sixtyFiveAbove100Exact",
                       "originalCoefficientCannotIdentifyGain",
                       "originalCoefficientCannotIdentifyConfidence"):
            assert marker in content, marker
        assert "{!!}" not in content and "postulate " not in content
    result=check()
    result["agda_contract_checked"]=args.agda_file is not None
    payload=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.out:args.out.write_text(payload)
    print(payload,end="")

if __name__=="__main__":
    main()

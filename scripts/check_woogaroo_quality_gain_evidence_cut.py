#!/usr/bin/env python3
"""2019/8575 -- source-exact koala OAG quality-gain exception test.

Primary proponent: Springfield PD v5 (30 Jan 2026), Part A.i
Tables A62, A69, A76 (BAAM Esk, One Environment Avonvale,
Saunders Havill Mount Walker West).
Primary government guidance: Commonwealth 2012 OAG instructions and
National EPA official 'Offsets assessment guide' page. The latter says
future with/without quality changes are normally capped at one point
and larger gains require strong scientific evidence.

A conditional score cap is NOT a finding that the approved gains are
unlawful, impossible, unscientific, or failed. It is a scenario until
the proponent's source-specific justifications, final October 2026
versions, and decision-maker reasoning are inspected.

No original QUT/QCC attribution is modified, and no FOI, clearing,
compliance breach, legal filing, or payment is inferred.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse
import json

ROWS={
 "Esk":((1501,1,75),(448,2,75),(759,1,85),(94,1,85)),
 "Avonvale":((493,3,75),(152,4,75),(20,1,85),(868,2,75),(110,0,85),(37,1,85)),
 "Mount Walker West":((508,4,75),(1047,4,75),(620,0,85),(81,0,85)),
}
DENOMINATOR=8960 * (1002**20)
MULTIPLIER=1000**20
EXPECTED_COEFFICIENTS={None:1010350, 3:882325, 2:717325, 1:453625}

def weighted_coefficient(rows, cap=None):
    return sum(area*min(gain,cap)*confidence if cap is not None
               else area*gain*confidence for area,gain,confidence in rows)

def scenario(cap):
    by_site={s:weighted_coefficient(rows,cap) for s,rows in ROWS.items()}
    coefficient=sum(by_site.values())
    assert coefficient==EXPECTED_COEFFICIENTS[cap]
    exact=F(coefficient*MULTIPLIER,DENOMINATOR)
    return {
       "quality_gain_maximum":cap,
       "total_percent_decimal":f"{float(exact):.12f}",
       "total_percent_exact":f"{exact.numerator}/{exact.denominator}",
       "above_90_direct_threshold":exact>=90,
       "above_100_full_compensation":exact>=100,
       "weighted_integer_coefficient":coefficient,
       "by_site_percent":{
          site:f"{float(F(weight*MULTIPLIER,DENOMINATOR)):.12f}"
          for site,weight in by_site.items()
       },
    }

def run():
    assert sum(map(len,ROWS.values()))==14
    assert sum(1 for rows in ROWS.values() for _,gain,_ in rows if gain>1)==7
    assert sum(1 for rows in ROWS.values() for _,gain,_ in rows if gain>2)==4
    assert sum(1 for rows in ROWS.values() for _,gain,_ in rows if gain>3)==3
    results={("source" if cap is None else "cap_"+str(cap)):scenario(cap)
             for cap in (None,3,2,1)}
    assert results["source"]["above_100_full_compensation"]
    assert results["cap_3"]["above_90_direct_threshold"]
    assert not results["cap_2"]["above_90_direct_threshold"]
    assert not results["cap_1"]["above_90_direct_threshold"]
    return {
       "case":"EPBC 2019/8575",
       "source_stage":"proponent reported, not independent ecological verification",
       "guidance":"Normally no more than one point gain absent strong scientific evidence for a larger change",
       "one_point_rule_is_exception_allowing_not_absolute":True,
       "source_OAG_stage":"January 2026 PD, not joined to final 15 October OAMPs",
       "impact_quantum_adjusted_ha":"89.6",
       "annual_extinction_probability_source":"0.2 percent vulnerable",
       "time_until_benefit_years":20,
       "zero_avoided_loss_only":True,
       "results":results,
       "above_one_gain_rows":7,
       "above_two_gain_rows":4,
       "above_three_gain_rows":3,
       "legal_or_scientific_adequacy_proved":False,
       "direct_approved_workbook_verified":False,
       "original_exception_justifications_verified":False,
       "agda_kernel_verified":False,
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--agda-file",type=Path)
    ap.add_argument("--out",type=Path)
    args=ap.parse_args()
    if args.agda_file:
        contents=args.agda_file.read_text()
        for marker in ("onePointCoefficient","twoPointCoefficient",
                       "threePointCoefficient","ExceptionalGainJustification"):
            assert marker in contents,marker
        assert not any(marker in contents for marker in ("postulate ","{!!}","allow-unsolved-metas"))
    obj=run()
    obj["agda_source_markers_checked"]=args.agda_file is not None
    s=json.dumps(obj,indent=2,sort_keys=True)+"\n"
    if args.out:args.out.write_text(s)
    print(s,end="")
if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""PV P5/P7: certified arithmetic FRONTIER over prior G173 model outputs.

The stored ideal efficiency percentages are historical exploratory,
multi-start numerical optimizations from check_pv_astm_g173_radiative.py,
NOT certified global efficiency bounds or real photovoltaic devices.
All rows are the SAME one-sun AM1.5G incident spectrum, and treat 4T and
2T architecture contact/optical/thermal/auxiliary losses separately.
Source: NLR ASTM G173-03 (2002 rows), as incorporated by original checker.
Certified comparator: Green et al., Solar Cell Efficiency Tables v68,
Joule 10 (2026) 102494, DOI 10.1016/j.joule.2026.102494.
"""
import json
from fractions import Fraction as F

ONE_SUN_W_M2=F(10003706555734,10**10)  # ≈1000.3706555734
IDEAL_PCT_THOUSANDTH={
    "2T_1J":33773,"2T_2J":45824,"2T_3J":51741,
    "2T_4J":52162,"2T_5J":53553,
    "4T_1J":33773,"4T_2J":46177,"4T_3J":51867,
    "4T_4J":56077,"4T_5J":58532,
}
HALF=50000
def row(architecture):
    ideal=IDEAL_PCT_THOUSANDTH[architecture]
    headroom=ideal-HALF
    return {"architecture":architecture,"ideal_model_pct":ideal/1000,
            "model_headroom_percentage_points":headroom/1000,
            "model_gross_W_m2":float(ONE_SUN_W_M2*ideal/100000),
            "total_allowed_loss_strict_W_m2":float(ONE_SUN_W_M2*headroom/100000),
            "fraction_of_ideal_output_spendable_pct":float(F(100*headroom,ideal)),
            "50pct_possible_in_idealized_ledger":headroom>0}
def net_after_losses(architecture,loss_pp_thousandths):
    return IDEAL_PCT_THOUSANDTH[architecture]-sum(loss_pp_thousandths)
def validate():
    t=[]
    def check(name,v):
        assert bool(v),name
        t.append(name)
    check("ten architecture cases",len(IDEAL_PCT_THOUSANDTH)==10)
    check("same one sun source",abs(float(ONE_SUN_W_M2)-1000.3706555734)<1e-8)
    for label,ideal in IDEAL_PCT_THOUSANDTH.items():
        h=ideal-HALF
        check(label+" exact threshold",net_after_losses(label,[h])==HALF)
        check(label+" strict threshold tie fails",not(net_after_losses(label,[h])>HALF))
        if h>0:
            check(label+" one unit below headroom passes",net_after_losses(label,[h-1])>HALF)
            check(label+" one unit above headroom fails",not(net_after_losses(label,[h+1])>HALF))
        else:
            check(label+" no loss cannot reach >50",net_after_losses(label,[0])<=HALF)
        r=row(label)
        check(label+" reproducible headroom",abs(r["model_headroom_percentage_points"]-(ideal-50000)/1000)<1e-10)
        check(label+" positive output",r["model_gross_W_m2"]>0)
    check("4T3J >= 2T3J",IDEAL_PCT_THOUSANDTH["4T_3J"]>=IDEAL_PCT_THOUSANDTH["2T_3J"])
    check("4T4J >= 2T4J",IDEAL_PCT_THOUSANDTH["4T_4J"]>=IDEAL_PCT_THOUSANDTH["2T_4J"])
    check("4T5J >= 2T5J",IDEAL_PCT_THOUSANDTH["4T_5J"]>=IDEAL_PCT_THOUSANDTH["2T_5J"])
    check("4T independent contact extra losses can reverse advantage",
          net_after_losses("4T_4J",[5000])<net_after_losses("2T_4J",[500]))
    check("4T4J 6pp loss passes",net_after_losses("4T_4J",[6000])>HALF)
    check("4T4J 6.077pp loss ties",net_after_losses("4T_4J",[6077])==HALF)
    check("3J2T 1.741pp loss ties",net_after_losses("2T_3J",[1741])==HALF)
    check("multiphysics sum of losses crosses limit",
          net_after_losses("4T_4J",[1000,1500,900,1000,1200])>HALF
          and net_after_losses("4T_4J",[1000,1500,900,1000,1800])<=HALF)
    return t
if __name__=="__main__":
    checks=validate()
    print(json.dumps({
        "passed":len(checks),"all_passed":True,
        "qualifier":"conditional on previous exploratory numerical G173 radiative model; no certified bounds",
        "units":"one-sun AM1.5G percentage points and W/m2, all losses are additive fractions of incident solar",
        "loss_categories":["optical escape / parasitic absorption",
          "radiative+nonradiative voltage/current loss","2T current mismatch or 4T DC conversion",
          "contacts+series resistance","thermal, control, tracking, RF & auxiliary"],
        "frontier":[row(k) for k in sorted(IDEAL_PCT_THOUSANDTH)],
        "tests":checks
    },indent=2))

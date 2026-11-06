#!/usr/bin/env python3
"""EPBC 2019/8575, paper-reported rounded versus unrounded MHQA values.

Exact Fraction calculation isolating Mount Walker West AU1/2 (the only
credit-bearing Koala MWW AUs) from PD v5 OAMP Table 13 / A76.
This is conditional and does not replace the official accepted OAG,
a legally allowed rounding rule or a real-world ecological measurement.
"""
from fractions import Fraction as F
import json
from pathlib import Path
import argparse

def run():
    original=1010350
    # source AU1 3.40->6.86 (=3.46) vs OAG 3->7 (=4)
    # source AU2 3.44->6.71 (=3.27) vs OAG 3->7 (=4)
    removal_hundredths=508*(400-346)*75+1047*(400-327)*75
    assert removal_hundredths==7789725
    modified=F(original,1)-F(removal_hundredths,100)
    assert modified==F(93245275,100)
    discount=F(1000,1002)**20
    old=F(original,8960)*discount
    new=modified/F(8960)*discount
    assert old>100 and F(99)<new<100
    assert F(8)<old-new<F(9)
    return {
        "case":"EPBC 2019/8575",
        "source":"PD v5 Mount Walker West OAMP Table 13 / Part A.i A76",
        "original_koala_percentage":format(float(old),".12f"),
        "conditional_unrounded_only_AU1_AU2_percentage":format(float(new),".12f"),
        "percentage_point_reduction":format(float(old-new),".12f"),
        "source_unrounded_quality_gains":["3.46","3.27"],
        "printed_OAG_rounded_quality_gains":[4,4],
        "all_else_fixed":True,
        "paper_precision_might_be_allowed":True,
        "original_OAG_xlsm_verified":False,
        "approved_OAMP_version_verified":False,
        "Agda_kernel_certified":False}
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--agda-file",type=Path)
    ap.add_argument("--out",type=Path)
    args=ap.parse_args()
    if args.agda_file:
        s=args.agda_file.read_text()
        for marker in ("mwwAU1RoundedInflationHundredths","mwwAU2RoundedInflationHundredths","unroundedOnlyTwoMWWAUCoefficient"):
            assert marker in s
        assert "postulate " not in s and "{!!}" not in s
    o=run()
    o["source_marker_check"]=bool(args.agda_file)
    s=json.dumps(o,indent=2,sort_keys=True)+"\n"
    if args.out:args.out.write_text(s)
    print(s,end="")
if __name__=="__main__":main()

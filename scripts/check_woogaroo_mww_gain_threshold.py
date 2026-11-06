#!/usr/bin/env python3
"""Source-exact koala 90/100% OAG break-even improvement, EPBC 2019/8575.

The model fixes all other 30 Jan 2026 PD v5 OAG quality inputs at their
published source values (Tables A62/A69/A76). This is a mathematical
sensitivity only; not an official approved 15 Oct 2026 XLSM run, proof of
failure, independent viability study, binding legal standard or breach.
Original QUT/QCC authorship and source audit remain the governing context.
"""
from fractions import Fraction as F
import argparse,json
from pathlib import Path

OTHER=543850
PER_GAIN=(508+1047)*75
P=1000**20
DEN=8960*1002**20
def coverage(g1,g2):
    return F((OTHER+508*75*g1+1047*75*g2)*P,DEN)
def break_even(t):
    """Identical improvement in both MWW AUs, all other rows fixed."""
    return (F(t*DEN,P)-OTHER)/PER_GAIN
def main_audit():
    assert OTHER+PER_GAIN*4 == 1010350
    assert coverage(2,2)<90<coverage(3,3)<100<coverage(4,4)
    assert 2<break_even(90)<3
    assert 3<break_even(100)<4
    # General AU-specific threshold for AU2, if AU1 is fixed at 4.
    au2_for_90=(F(90*DEN,P)-OTHER-508*75*4)/(1047*75)
    au2_for_100=(F(100*DEN,P)-OTHER-508*75*4)/(1047*75)
    # Source AU2 change from four to three is still >90; below 100.
    assert coverage(4,3)<100 and coverage(4,3)>90
    return {
      "case":"EPBC 2019/8575",
      "source":"PD v5, 30 Jan 2026, Part A.i Tables A62/A69/A76",
      "other_AU_coefficient":OTHER,
      "one_equal_MWW_gain_point_coefficient":PER_GAIN,
      "annual_extinction_assumption":"2019 Vulnerable 0.2%, s158A legal status separate",
      "year20_discount":"(1.002)^(-20)",
      "common_gain_threshold_90_points_exact":str(break_even(90)),
      "common_gain_threshold_100_points_exact":str(break_even(100)),
      "common_gain_threshold_90_points_approx":f"{float(break_even(90)):.8f}",
      "common_gain_threshold_100_points_approx":f"{float(break_even(100)):.8f}",
      "AU2_gain_threshold_if_AU1_is_4_for_90":f"{float(au2_for_90):.8f}",
      "AU2_gain_threshold_if_AU1_is_4_for_100":f"{float(au2_for_100):.8f}",
      "coverage_percent_common_gain_2":f"{float(coverage(2,2)):.8f}",
      "coverage_percent_common_gain_3":f"{float(coverage(3,3)):.8f}",
      "coverage_percent_common_gain_4":f"{float(coverage(4,4)):.8f}",
      "90_percent_is_ordinary_direct_offset_policy_benchmark_not_automatic_legal_validity":True,
      "approved_OAMP_and_calculator_received":False,
      "measured_ecological_function":False,
      "kernel_certified":False
    }
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--agda-file",type=Path)
    p.add_argument("--out",type=Path)
    a=p.parse_args()
    if a.agda_file:
        s=a.agda_file.read_text()
        for k in ("twoPointBelow90Witness","threePointAbove90Witness",
                  "threePointBelow100Witness","fourPointAbove100Witness"):
            assert k in s,k
        assert "postulate " not in s and "{!!}" not in s
    obj=main_audit()
    obj["agda_marker_check"]=bool(a.agda_file)
    payload=json.dumps(obj,sort_keys=True,indent=2)+"\n"
    if a.out:a.out.write_text(payload)
    print(payload,end="")
if __name__=="__main__":main()

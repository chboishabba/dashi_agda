#!/usr/bin/env python3
"""EPBC 2019/8575: reconstruct the 14 reported koala quality-gain OAG rows.

SOURCES:
- Proponent's 30 Jan 2026 Springfield PD v5 Part A.i Tables A62 (Esk),
  A69 (Avonvale), A76 (Mount Walker West) and A59 (published totals).
- 2012 Commonwealth 'How to use the Offsets assessment guide', §§2 A,C,G,H.
- Official Commonwealth koala listing: QLD/NSW/ACT Endangered 12 Feb 2022.

The PD and annexed OAG sheets explicitly use *Vulnerable* 0.2% annual
extinction parameter (original 2019 referral status). The distinct
Endangered parameter is 1.2%. This is an adversarial CONDITIONAL
counterfactual, not a determination of saved/transitional EPBC law, what
the decision-maker was bound to use, source version consistency, a breach,
fraud, original spreadsheet execution, or any real ecological outcome.

Area and quality gains are explicitly rounded to OAG integer inputs, not
unrounded MHQA predictions. The model assumes zero averted-loss gain as
reported in all three offset plans. All numeric computation uses exact
fractions, no float. Preserve QUT/QCC and all original report authors.
"""
from __future__ import annotations
from fractions import Fraction as F
from dataclasses import dataclass
import argparse
import json
from pathlib import Path

IMPACT_QUANTUM = F("89.6")
YEARS = 20
SOURCE_PRINTED = {"Esk":(F("12.07"),F("7.21"),F("6.92"),F("0.86")),
                  "Avonvale":(F("11.90"),F("4.89"),F("0.18"),F("13.96"),F("0"),F("0.34")),
                  "Mount Walker West":(F("16.34"),F("33.68"),F("0"),F("0"))}
SOURCE_TOTALS = {"Esk":F("27.06"),"Avonvale":F("31.27"),
                 "Mount Walker West":F("50.02")}
SOURCE_ALL = F("108.35")

@dataclass(frozen=True)
class Row:
    area_tenths: int
    q_without: int
    q_with: int
    confidence_percent: int
    # Values are OAG worksheet inputs, NOT unrounded consultant MHQA scores.
    def __post_init__(self):
        assert 0 <= self.q_without <= self.q_with <= 10
        assert 0<=self.confidence_percent<=100 and self.area_tenths>=0

ROWS = {
    "Esk":(
        Row(1501,6,7,75),Row(448,5,7,75),
        Row(759,6,7,85),Row(94,6,7,85)),
    "Avonvale":(
        Row(493,4,7,75),Row(152,3,7,75),
        Row(20,6,7,85),Row(868,5,7,75),
        Row(110,7,7,85),Row(37,6,7,85)),
    "Mount Walker West":(
        Row(508,3,7,75),Row(1047,3,7,75),
        Row(620,7,7,85),Row(81,7,7,85)),
}

def discount(annual_extinction:F) -> F:
    assert F(0) <= annual_extinction <= F(1)
    return (F(1)+annual_extinction)**(-YEARS)

def contribution_percent(row:Row, annual_extinction:F) -> F:
    raw_gain=F(row.area_tenths,10)*F(row.q_with-row.q_without,10)
    adjusted=raw_gain*F(row.confidence_percent,100)
    return F(100)*adjusted*discount(annual_extinction)/IMPACT_QUANTUM

def contribution_by_site(annual_extinction:F) -> dict[str,tuple[F,...]]:
    return {site:tuple(contribution_percent(row,annual_extinction) for row in rows)
            for site,rows in ROWS.items()}

def exact_sum(p:F) -> F:
    return sum((v for values in contribution_by_site(p).values() for v in values),F())

def formatted(x:F,places:int=6) -> str:
    # Decimal formatting is ONLY for display; tests use Fraction.
    return f"{float(x):.{places}f}"

def verify_source():
    assert sum(len(x) for x in ROWS.values())==14
    assert set(ROWS)==set(SOURCE_TOTALS)
    assert sum(SOURCE_TOTALS.values())==SOURCE_ALL
    assert sum(r.area_tenths for s in ROWS for r in ROWS[s])==6738  # 280.2+168+225.6
    weight=sum(r.area_tenths*(r.q_with-r.q_without)*r.confidence_percent
               for rows in ROWS.values() for r in rows)
    assert weight==1010350
    vulnerable=F(2,1000)
    endangered=F(12,1000)
    model=contribution_by_site(vulnerable)
    # Per-AU printed roundings may mix 1/2-decimal display conventions.
    for site,vals in model.items():
        assert len(vals)==len(SOURCE_PRINTED[site])
        assert all(abs(a-b) <= F(11,1000)
                   for a,b in zip(vals,SOURCE_PRINTED[site])),site
        assert abs(sum(vals)-SOURCE_TOTALS[site]) < F(2,100),site
    assert abs(exact_sum(vulnerable)-SOURCE_ALL) < F(2,100)

    # All 14 quality-gain lines share exactly the same discount exponent.
    ratio=discount(endangered)/discount(vulnerable)
    assert exact_sum(endangered)==exact_sum(vulnerable)*ratio
    assert exact_sum(vulnerable)>100
    assert exact_sum(endangered)<90
    assert exact_sum(endangered)<100

    # One point lower future quality for MWW AU2, everything else fixed.
    au2=ROWS["Mount Walker West"][1]
    lower=Row(au2.area_tenths,au2.q_without,6,au2.confidence_percent)
    loss=contribution_percent(au2,vulnerable)-contribution_percent(lower,vulnerable)
    adjusted=exact_sum(vulnerable)-loss
    assert F(0)<loss<F(10)
    assert F(90)<adjusted<F(100)

    # One-point change in future quality is NOT a finding that such
    # future quality will actually be reached.
    return {
        "case":"EPBC 2019/8575",
        "source":"PD v5 (30 Jan 2026), Part A.i A62/A69/A76; A59",
        "guide":"2012 Commonwealth Offsets assessment guide §§2 A,C,G,H",
        "model":"reconstructed quality-only OAG row; zero averted-loss component",
        "quality_input":"rounded integer OAG start/future values",
        "rows":14,
        "site_areas_ha":{"Esk":"280.2","Avonvale":"168",
                         "Mount Walker West":"225.6"},
        "row_coefficient_integer":weight,
        "reported_source_percent":{k:str(v) for k,v in SOURCE_TOTALS.items()},
        "reconstructed_vulnerable_percent_by_site":{
            k:formatted(sum(v)) for k,v in model.items()},
        "reconstructed_vulnerable_percent":formatted(exact_sum(vulnerable)),
        "reconstructed_endangered_percent":formatted(exact_sum(endangered)),
        "discounter_vulnerable":"(1.002)^(-20)",
        "discounter_endangered":"(1.012)^(-20)",
        "discount_ratio_exact":f"{ratio.numerator}/{ratio.denominator}",
        "AU2_one_point_quality_loss_percent_points":formatted(loss),
        "AU2_one_point_lower_aggregate_percent":formatted(adjusted),
        "vulnerable_above_100":bool(exact_sum(vulnerable)>100),
        "endangered_below_90":bool(exact_sum(endangered)<90),
        "one_point_MWW_AU2_below_100":bool(adjusted<100),
        "legal_transition_status":"OPEN: 2019 referral vs 2022 endangered listing vs 2026 decision",
        "approved_15Oct_OAMP_version_equivalence":"OPEN",
        "real_ecological_occupancy_or_gain_observed":False,
        "independent_OAG_spreadsheet_execution":False,
        "agda_kernel_checked":False,
    }

def check_agda_source(path:Path):
    source=path.read_text()
    for marker in ("sourceWeightSum","separateSitesAddToSameWeight",
                   "vulnerableAbove100Exact","endangeredBelow90Exact",
                   "mwwAU2ScenarioNumerator","oagDenominator"):
        assert marker in source,marker
    for banned in ("postulate ","{!!}","allow-unsolved-metas","TERMINATING"):
        assert banned not in source,banned

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--agda-file",type=Path)
    ap.add_argument("--out",type=Path)
    args=ap.parse_args()
    if args.agda_file: check_agda_source(args.agda_file)
    r=verify_source()
    r["agda_source_marker_check"]=bool(args.agda_file)
    s=json.dumps(r,indent=2,sort_keys=True)+"\n"
    if args.out: args.out.write_text(s)
    print(s,end="")

if __name__=="__main__":main()

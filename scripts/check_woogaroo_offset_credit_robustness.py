#!/usr/bin/env python3
"""EPBC 2019/8575: exact rational conditional CREDIT robustness, 4 species.

Source: proponent Springfield PD v5 (30 Jan 2026) Part A.i Table A59.
This is NOT an official 2012/2026 OAG spreadsheet recalculation.
A scenario haircut to already-reported output credits is not a validated
change to confidence/quality/time inputs. Causality, ecology, recorded
declarations, legal merits and the signed approved 15 Oct 2026 offset
plans cannot be inferred from this file. Original QUT/QCC sources retain
their original authorship and separate scientific provenance.
"""
from __future__ import annotations
from fractions import Fraction as F
import argparse, itertools, json
from pathlib import Path

BPS = 10000
SOURCE = {
    "koala": {"esk":2706,"avonvale":3127,"mount_walker_west":5002},
    "grey_headed_flying_fox": {"esk":6344,"avonvale":6059,"mount_walker_west":6689},
    "swift_parrot": {"esk":5458,"avonvale":5349,"mount_walker_west":9192},
    "regent_honeyeater": {"esk":5495,"avonvale":1207,"mount_walker_west":3740},
}
TABLE_TOTALS = {"koala":10835,"grey_headed_flying_fox":19092,
                "swift_parrot":19999,"regent_honeyeater":10442}
SITES = ("esk","avonvale","mount_walker_west")
def exact_str(x):
    return str(x.numerator) if x.denominator == 1 else f"{x.numerator}/{x.denominator}"

def percent_str_from_bps(x):
    x = F(x,100)
    return exact_str(x)

def credit_bps(matter, retained):
    """Retained fractions are conditional CREDIT fractions, NOT OAG inputs."""
    assert set(retained) == set(SITES)
    assert all(F(0)<=F(v)<=F(1) for v in retained.values())
    return sum((F(SOURCE[matter][site])*F(retained[site]) for site in SITES),F())

def intervals(matter, bounds):
    """Exact rectangular scenario bounds; monotonic in retained CREDIT."""
    assert set(bounds) == set(SITES)
    lo,hi = {},{}
    for site in SITES:
        l,h=map(F,bounds[site])
        assert F(0)<=l<=h<=F(1)
        lo[site],hi[site]=l,h
    lower=credit_bps(matter,lo)
    upper=credit_bps(matter,hi)
    # Enumerate all eight vertices as independent reference.
    vertices=[credit_bps(matter,dict(zip(SITES,corner))) for corner in
              itertools.product(*(bounds[s] for s in SITES))]
    assert min(vertices)==lower and max(vertices)==upper
    return {"low_percent":percent_str_from_bps(lower),
            "high_percent":percent_str_from_bps(upper),
            "all_vertices":len(vertices),
            "100_percent_robust_for_this_assumed_rectangle":lower>=BPS,
            "100_percent_unattainable_for_this_assumed_rectangle":upper<BPS,
            "90_percent_direct_robust_for_this_assumed_rectangle":lower>=9000}

def boundary_mww(matter,target):
    """Minimum retained MWW credit, holding two other sites at source claims."""
    other=SOURCE[matter]["esk"]+SOURCE[matter]["avonvale"]
    mww=SOURCE[matter]["mount_walker_west"]
    required=target-other
    if required<=0:
        return {"already_met_by_other_sites":True,"needed_mww_bps":0}
    if required>mww:
        return {"unattainable_even_full_MWW":True,"needed_mww_bps":required}
    assert other+required == target and other+(required-1)==target-1
    return {
        "other_sites_claim_bps":other,
        "needed_mww_bps":required,
        "mww_original_bps":mww,
        "max_mww_credit_loss_bps":mww-required,
        "mww_credit_retention_fraction":exact_str(F(required,mww)),
        "mww_credit_loss_fraction":exact_str(F(mww-required,mww)),
        "one_basis_point_less_fails": True
    }

def run():
    assert set(SOURCE) == set(TABLE_TOTALS)
    for k,row in SOURCE.items():
        assert set(row)==set(SITES)
        assert sum(row.values())==TABLE_TOTALS[k],(k,row)
        assert TABLE_TOTALS[k]>=10000
    # Primary original-source values are reported percent of impact x100.
    margins={k: TABLE_TOTALS[k]-BPS for k in TABLE_TOTALS}
    assert margins == {"koala":835,"grey_headed_flying_fox":9092,
                        "swift_parrot":9999,"regent_honeyeater":442}
    assert SOURCE["koala"]["esk"]+SOURCE["koala"]["avonvale"] == 5833
    assert SOURCE["regent_honeyeater"]["esk"]+SOURCE["regent_honeyeater"]["avonvale"]==6702

    # MWW-only shock examples. 90% retention is an illustrative 10%
    # haircut of REPORTED CREDITS, not a 10% change in habitat success.
    scenario={}
    for retention in (F(9,10),F(22,25),F(4,5)):
        by={k:credit_bps(k,{"esk":1,"avonvale":1,
                            "mount_walker_west":retention}) for k in SOURCE}
        scenario[f"mww_retains_{exact_str(100*retention)}_percent_of_reported_credit"]={
            k:percent_str_from_bps(v) for k,v in by.items()}
    assert credit_bps("koala",{"esk":1,"avonvale":1,"mount_walker_west":F(4,5)})==F(98346,10)
    assert credit_bps("regent_honeyeater",{"esk":1,"avonvale":1,"mount_walker_west":F(22,25)})==F(99932,10)

    all_bounds = {s:(F(9,10),F(1)) for s in SITES}
    example_10pct_all = {k:intervals(k,all_bounds) for k in SOURCE}
    assert example_10pct_all["koala"]["100_percent_robust_for_this_assumed_rectangle"] is False
    assert example_10pct_all["regent_honeyeater"]["100_percent_robust_for_this_assumed_rectangle"] is False
    assert example_10pct_all["grey_headed_flying_fox"]["100_percent_robust_for_this_assumed_rectangle"] is True
    assert example_10pct_all["swift_parrot"]["100_percent_robust_for_this_assumed_rectangle"] is True

    # Thresholds at 100 and 90 are DIFFERENT comparisons. The OAG
    # guide distinguishes minimum 90% DIRECT offsets and other measures.
    # No claim is made that "100% direct" is the universal legal test.
    return {
        "case":"EPBC 2019/8575",
        "source":"Springfield Preliminary Documentation v5 Part A.i Table A59",
        "source_stage":"PROPROPONENT_REPORTED_NOT_INDEPENDENTLY_VERIFIED",
        "unit":"basis points of reported percent of impact offset, 10000=100%",
        "source_totals_percent":{k:percent_str_from_bps(v) for k,v in TABLE_TOTALS.items()},
        "margin_above_100_percent_points":{k:percent_str_from_bps(v) for k,v in margins.items()},
        "mww_only_100_percent_boundaries":{k:boundary_mww(k,BPS) for k in SOURCE},
        "mww_only_90_percent_boundaries":{k:boundary_mww(k,9000) for k in SOURCE},
        "conditional_mww_only_shocks":scenario,
        "illustrative_all_site_10_percent_credit_haircut":example_10pct_all,
        "source_conflicts_unresolved":[
            "BAAM Esk OAMP text gives Regent Honeyeater 54.96%; Part A.i A59 54.95%",
            "A16 Table 45 AU4 30/70 component sum vs printed 40/70 total",
            "A16 impacted area 127.02 ha vs main PD 128.00 ha",
            "Original final 15 October 2026 OAMPs not reconciled"
        ],
        "cannot_conclude":[
            "that any hypothetical credit reduction is observed or probable",
            "actual OAG output after changing future habitat quality/confidence",
            "full 2012 OAG net-present-value / extinction discount formula acceptance",
            "actual 2026 approved plan identity or Commonwealth reliance",
            "ecological functional equivalence, compliance breach, litigation or court outcome",
        ],
        "agda_kernel_accepted":False,
    }

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--agda-file",type=Path)
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    if args.agda_file:
        source=args.agda_file.read_text()
        for marker in ("regentHoneyeaterMargin","koalaMWW100Boundary",
                       "regentMWW100Boundary","koalaMWW80PercentRetained",
                       "regentMWW88PercentRetained","sourceCreditNotReality"):
            assert marker in source,marker
        for forbidden in ("postulate ","{!!}","allow-unsolved-metas","TERMINATING"):
            assert forbidden not in source,forbidden
    r=run()
    r["agda_source_markers_checked"]=bool(args.agda_file)
    s=json.dumps(r,indent=2,sort_keys=True)+"\n"
    if args.output:args.output.write_text(s)
    print(s,end="")
if __name__=="__main__":main()

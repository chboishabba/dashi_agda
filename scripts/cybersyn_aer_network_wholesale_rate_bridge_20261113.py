#!/usr/bin/env python3
"""AER actual 2026-27 Ausgrid cost-stack decomposition and hypothetical CPI/rate bridge.

Different benchmark load profiles produce different dollar changes. Neither
published network-charge movement identifies data-centre causation. Electricity
CPI weights, household pass-through and policy response are assumptions.
"""
from __future__ import annotations
import argparse, csv, json
from itertools import product
from pathlib import Path

SOURCES={
 "aer_final_dmo":"https://www.aer.gov.au/system/files/2026-05/AER%20-%20Final%20determination%20-%20Default%20market%20offer%202026%E2%80%9327.pdf",
 "aer_ausgrid":"https://www.aer.gov.au/system/files/2026-04/Ausgrid%20%E2%80%93%202026%E2%80%9327%20%E2%80%93%20Pricing%20Proposal%20Overview%20%E2%80%93%2031%20March%202026.pdf",
 "aer_reasons":"https://www.aer.gov.au/system/files/2026-04/AER%20%E2%80%93%202026%E2%80%9327%20%E2%80%93%20Statement%20of%20Reasons%20%E2%80%93%20Ausgrid%20Pricing%20Proposal.pdf",
 "aemo_q3":"https://www.aemo.com.au/newsroom/media-release/qed-q3-2026"}
# Table F.1 AER DMO, nominal, residential flat, NSW Ausgrid.
STACK={"wholesale":(753.97,653.79),"network":(711.92,778.23),
       "environment":(68.33,47.57),"retail":(312.51,305.55),
       "retail_margin":(117.88,113.95)}
TOTAL_FY26=1965
TOTAL_FY27=1899

def compute():
    differences={name:round(after-before,2) for name,(before,after) in STACK.items()}
    sum_components=round(sum(differences.values()),2)
    # Rounding difference is in the source components, not a hidden charge.
    assert abs(sum_components-(TOTAL_FY27-TOTAL_FY26))<1
    assert differences["network"]>0
    assert differences["wholesale"]<0
    assert sum_components<0
    incidence=[]
    for cpi_weight,pass_through,case in product(
        (.01,.02,.03),(.25,.5,1.),("all_cost_components","network_only")):
        dollars=sum_components if case=="all_cost_components" else differences["network"]
        bill_pct=100*dollars/TOTAL_FY26
        cpi_pp=cpi_weight*bill_pct*pass_through
        incidence.append({
          "hypothetical_electricity_CPI_weight":cpi_weight,
          "hypothetical_retail_pass_through":pass_through,
          "cost_case":case,
          "hypothetical_electricity_bill_change_pct":round(bill_pct,5),
          "hypothetical_CPI_contribution_pp":round(cpi_pp,5),
          "hypothetical_1p5_inflation_rate_rule_bp":round(150*cpi_pp,4)})
    return {"schema":"dashi-cybersyn-AER-DMO-cost-decomposition-v1",
        "source_urls":SOURCES,"year_on_year_cost_stack_aud":differences,
        "rounded_component_sum_aud":sum_components,
        "AER_published_wholesale_change_aud":-100.19,
        "published_total_change_aud":TOTAL_FY27-TOTAL_FY26,
        "Ausgrid_illustrative_5MWh_network_increase_aud":73.81,
        "AER_average_4044kWh_flat_network_increase_aud":63.81,
        "AEMO_Q3_2026_average_NEM_spot_price_yoy_pct":-27.,
        "data_centre_cost_causal_share":"unidentified",
        "empirical_CPI_pass_through_estimated":False,
        "monetary_rate_rule_estimated":False,
        "incidence":incidence}

def main():
    p=argparse.ArgumentParser();p.add_argument("--out",required=True,type=Path)
    args=p.parse_args();args.out.mkdir(parents=True,exist_ok=True)
    r=compute()
    (args.out/"aer_network_wholesale_receipt.json").write_text(
        json.dumps({k:v for k,v in r.items() if k!="incidence"},indent=2)+"\n")
    with (args.out/"conditional_cpi_rate_cases.csv").open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=r["incidence"][0].keys())
        w.writeheader();w.writerows(r["incidence"])
    print(json.dumps({"cost_changes":r["year_on_year_cost_stack_aud"],
                      "conditional_cases":len(r["incidence"])},indent=2))
if __name__=="__main__":
    main()

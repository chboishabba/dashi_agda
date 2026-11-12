#!/usr/bin/env python3
"""As-of-2026-11-12 Fed/RBA futures and Australian regulated-network cost ledger.

All policy futures are market prices, not independent probabilities of truth.
Network changes are published regulated amounts, NOT attributed to data centres.
"""
from __future__ import annotations
import argparse, csv, json
from pathlib import Path

SOURCES={
 "fed_target":"https://www.federalreserve.gov/newsevents/pressreleases/monetary20261028a.htm",
 "rba_target":"https://www.rba.gov.au/statistics/cash-rate/",
 "fed_futures_third_party":"https://terminal.kryptomagazin.cz/en/macro/fedwatch",
 "rba_asx_futures":"https://www.asx.com.au/markets/trade-our-derivatives-market/futures-market/rba-rate-tracker",
 "ausgrid_aer":"https://www.aer.gov.au/industry/networks/pricing-proposals/ausgrid-2026-27-pricing-proposal",
 "rba_datacentres":"https://www.rba.gov.au/publications/insights/australian-economy/2026/data-centre-investment-in-australia.html"
}
FED_MIDPOINT_DISTRIBUTIONS={
 "2026-12-09":{4.125:88.1,4.375:11.9},
 "2027-01-27":{4.125:33.4,4.375:59.2,4.625:7.4},
 "2027-03-17":{4.125:11.2,4.375:42.1,4.625:41.8,4.875:4.9},
 "2027-12-08":{3.875:.9,4.125:8.2,4.375:25.5,4.625:35.1,4.875:22.4,5.125:6.9,5.375:1.0}
}
# ASX values are 30-day overnight contract implied yields, NOT cash-rate
# target outcome probabilities. Latest close Nov 11, 2026.
RBA_ASX_YIELDS={
 "2026-11":4.82,"2026-12":4.855,"2027-03":4.91,
 "2027-06":4.865,"2027-09":4.75,"2027-12":4.65}
AUSGRID_NETWORK_ALLOWANCE_M=(2528,2881)
AUSGRID_CHANGE_COMPONENTS_M={
 "distribution":152,"ausgrid_transmission":28,"transgrid":129,
 "climate_change_fund":4,"nsw_roadmap":41}

def monthly_mortgage_payment(principal:float,rate:float,years:int=25)->float:
    m=rate/12
    n=12*years
    return principal*m/(1-(1+m)**(-n))

def calculate()->dict:
    fed=[]
    for meeting,dist in FED_MIDPOINT_DISTRIBUTIONS.items():
        assert abs(sum(dist.values())-100)<1e-8
        expected=sum(mid*prob/100 for mid,prob in dist.items())
        likely=max(dist,key=dist.get)
        fed.append({"meeting":meeting,"implied_expected_target_midpoint_pct":round(expected,4),
                    "modal_target_midpoint_pct":likely,"modal_probability_pct":dist[likely],
                    "market_implied_not_independent_model":True})
    actual_change=AUSGRID_NETWORK_ALLOWANCE_M[1]-AUSGRID_NETWORK_ALLOWANCE_M[0]
    # Rounded component amounts may differ from approved allowance delta.
    assert abs(sum(AUSGRID_CHANGE_COMPONENTS_M.values())-actual_change)<=2
    rate_delta_25bp_500k=monthly_mortgage_payment(500000,.0625)-monthly_mortgage_payment(500000,.06)
    sensitivity=[]
    for debt_bn in (1,5):
        for bp in (0,25,50,100):
            cost_m=debt_bn*1000*bp/10000
            for share in (0,.25,1.0):
                sensitivity.append({
                    "assumed_debt_aud_bn":debt_bn,"assumed_rate_increase_bp":bp,
                    "hypothetical_interest_increase_aud_m_year":cost_m,
                    "assumed_household_recovery_share":share,
                    "hypothetical_per_account_aud_year_at_1m_accounts":cost_m*share})
    return {"schema":"dashi-cybersyn-policy-rate-network-cost-v1",
      "as_of":"2026-11-12","sources":SOURCES,
      "fed_current_target_range_pct":[3.75,4.0],
      "rba_current_cash_rate_target_pct":4.85,
      "fed_market_implied":fed,"rba_asx_overnight_implied_yields_pct":RBA_ASX_YIELDS,
      "ausgrid_fy26_allowance_aud_m":2528,"ausgrid_fy27_allowance_aud_m":2881,
      "ausgrid_allowance_change_aud_m":actual_change,
      "ausgrid_rounded_revenue_components_aud_m":AUSGRID_CHANGE_COMPONENTS_M,
      "ausgrid_typical_residential_network_bill_increase_aud_year":73.81,
      "example_mortgage_500k_25yr_25bp_payment_increase_aud_month":round(rate_delta_25bp_500k,2),
      "rba_investment_projection_aud_bn":115,
      "rba_estimated_import_fraction":.70,
      "illustrative_network_debt_rate_sensitivity":sensitivity,
      "data_centre_attribution_of_network_allowance":"not identified",
      "real_world_marginal_cost_causality_established":False,
      "independent_policy_rate_forecast_validated":False,
      "kernel_proof_accepted":False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--out",type=Path,required=True)
    args=p.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    result=calculate()
    (args.out/"policy_rates_network_cost_receipt.json").write_text(
        json.dumps(result,indent=2,sort_keys=True)+"\n")
    with (args.out/"rate_network_debt_sensitivity.csv").open("w",newline="") as file:
        rows=result["illustrative_network_debt_rate_sensitivity"]
        writer=csv.DictWriter(file,fieldnames=rows[0].keys())
        writer.writeheader()
        writer.writerows(rows)
    print(json.dumps({"fed_dec2026_expected_midpoint_pct":
      result["fed_market_implied"][0]["implied_expected_target_midpoint_pct"],
      "rba_dec2026_asx_overnight_yield_pct":RBA_ASX_YIELDS["2026-12"],
      "ausgrid_revenue_allowance_change_aud_m":353,
      "data_centre_attribution_verified":False},indent=2))

if __name__=="__main__":main()

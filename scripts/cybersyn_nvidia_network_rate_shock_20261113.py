#!/usr/bin/env python3
"""NVIDIA funding, Australian grid and conditional rates stress model (13 Nov 2026).

All economic transmission coefficients are hypothetical; source anchors are
reported public figures. In particular US$164.5bn commitments, US$125bn
optional support, and US$500bn proposed platform are not additive.
"""
from __future__ import annotations
import argparse, csv, json
from pathlib import Path
from itertools import product

SOURCES = {
 "nvidia": "https://www.reuters.com/business/finance/investors-worry-ai-trade-needs-nvidias-huang-its-largesse-2026-11-12/",
 "nvidia_sec": "https://www.sec.gov/Archives/edgar/data/1045810/000104581026000082/nvda-20261111.htm",
 "rba": "https://www.rba.gov.au/publications/insights/australian-economy/2026/data-centre-investment-in-australia.html",
 "rba_decision": "https://www.rba.gov.au/speeches/2026/mc-gov-2026-11-03.html",
 "fed": "https://www.federalreserve.gov/newsevents/pressreleases/monetary20261028a.htm",
 "ausgrid": "https://www.aer.gov.au/system/files/2026-04/Ausgrid%20%E2%80%93%202026%E2%80%9327%20%E2%80%93%20Pricing%20Proposal%20Overview%20%E2%80%93%2031%20March%202026.pdf"
}
ANCHORS = {
 "nvidia_financial_commitments_usd_bn":164.5,
 "nvidia_ohio_obligation_cap_usd_bn":105.,
 "nvidia_lease_other_guarantees_lower_bound_usd_bn":50.,
 "nvidia_proposed_third_party_platform_usd_bn":500.,
 "nvidia_optional_platform_backstop_usd_bn":125.,
 "australian_dc_expected_2026_to_2028_aud_bn":115.,
 "rba_central_import_share":.70,
 "ausgrid_fy27_revenue_increase_aud_m":353.,
 "ausgrid_transgrid_increase_aud_m":129.,
 "rba_rate_pct":4.85,"fed_target_midpoint_pct":3.875
}

def compute():
    assert ANCHORS["nvidia_optional_platform_backstop_usd_bn"] <= ANCHORS["nvidia_proposed_third_party_platform_usd_bn"]
    grid = []
    for cancel, network_fraction, imported, recovery, spread_bp in product(
        (0.,.1,.25,.5),(0.,.25,.5,1.),(.5,.7,.8),(0.,.25,.5,1.),(0,100,300)
    ):
        # Independent, hypothetical shocks; no equation asserts NVIDIA caused
        # actual cancellation of Australian projects.
        delayed = 115*cancel
        domestic = delayed*(1-imported)
        imports = delayed*imported
        # This treats $353m as a comparison upper-bound envelope, NOT as an
        # observed data-centre cost. Its data-centre attributable share is unknown.
        assumed_network = 353*network_fraction
        household = assumed_network*recovery
        interest = 50*spread_bp/10 # USD m / year on assumed USD 50bn debt
        assert abs(delayed-domestic-imports)<1e-8
        assert 0<=household<=assumed_network<=353
        grid.append({
            "assumed_fraction_of_AU_pipeline_delayed":cancel,
            "assumed_fraction_of_Ausgrid_movement_DC_attributable":network_fraction,
            "assumed_import_share":imported,
            "assumed_network_recovery_from_households":recovery,
            "assumed_loan_spread_increase_bp":spread_bp,
            "AU_investment_delayed_aud_bn":round(delayed,6),
            "AU_domestic_spend_delayed_aud_bn":round(domestic,6),
            "AU_imports_delayed_aud_bn":round(imports,6),
            "hypo_Ausgrid_DC_component_aud_m":round(assumed_network,6),
            "hypo_household_network_incidence_aud_m":round(household,6),
            "hypo_US_annual_interest_cost_usd_m":round(interest,6)
        })
    rate = []
    # Rule response, not estimated FOMC/RBA reaction function or rate forecast.
    for delta_inflation, delta_gap in product((-.25,0,.25,.5),(-.5,0,.5)):
        delta = 1.5*delta_inflation+.5*delta_gap
        rate.append({"assumed_underlying_inflation_shock_pp":delta_inflation,
            "assumed_output_gap_shock_pp":delta_gap,
            "hypo_policy_rule_change_bp":100*delta,
            "rba_hypo_rate_pct":round(4.85+delta,4),
            "fed_hypo_midpoint_pct":round(3.875+delta,4)})
    return {
       "schema":"dashi-cybersyn-nvidia-network-monetary-sensitivity-v1",
       "as_of":"2026-11-13", "sources":SOURCES,"anchors":ANCHORS,
       "cases":grid,"rate_cases":rate,
       "optional_backstop_reduction_usd_bn":{
            "0pct":0.,"10pct":12.5,"25pct":31.25,"50pct":62.5},
       "current_actual_cancelled_AU_pipeline":"not measured",
       "source_verified_as_implications":False,"empirically_calibrated":False,
       "JMD_builder_integrated":False,"Agda_kernel_accepted":False}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--out",required=True,type=Path)
    a=p.parse_args(); a.out.mkdir(parents=True,exist_ok=True)
    r=compute()
    for field,name in [("cases","scenario_grid.csv"),("rate_cases","conditional_rate_grid.csv")]:
        with (a.out/name).open("w",newline="") as f:
            writer=csv.DictWriter(f,fieldnames=r[field][0].keys())
            writer.writeheader();writer.writerows(r[field])
    (a.out/"receipt.json").write_text(json.dumps(
        {k:v for k,v in r.items() if k not in ("cases","rate_cases")},indent=2,sort_keys=True)+"\n")
    print(json.dumps({"scenario_rows":len(r["cases"]),"conditional_rate_rows":len(r["rate_cases"]),
       "max_delayed_domestic_aud_bn":max(x["AU_domestic_spend_delayed_aud_bn"] for x in r["cases"]),
       "max_illustrative_network_household_aud_m":max(x["hypo_household_network_incidence_aud_m"] for x in r["cases"])},sort_keys=True))

if __name__=="__main__":
    main()

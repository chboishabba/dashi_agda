#!/usr/bin/env python3
"""Source-anchored Australian AI power/financing sensitivity (not causal inference).

Sources, available 12 Nov 2026:
* AEMO + Oxford Economics, Data Centres Energy Demand Outlook in Australia,
  25 Aug 2026: NEM FY26 5.1 TWh, FY30 15.5 TWh, FY36 33.7 TWh.
  https://www.oxfordeconomics.com/resource/data-centres-energy-demand-outlook-in-australia/
* Reuters, 21 Oct 2026: NEXTDC deferred A$140m of customer revenue,
  equity value fell ~A$3bn, FY27 guidance ranges as below.
  https://www.reuters.com/world/asia-pacific/australian-ai-data-centre-operator-nextdc-shares-shed-44-revenue-delay-2026-10-21/

Synthetic parameters: tariff, customer/public incidence, guarantee fraction.
No actual tariff, guarantee or marginal grid cost is claimed.
"""
from __future__ import annotations
from decimal import Decimal as D
from itertools import product
import csv, json
from pathlib import Path
import argparse

NEM_FY_TWH = {2026:D("5.1"),2030:D("15.5"),2036:D("33.7")}
TARIFF_AUD_MWH = (D(100),D(200),D(300))
CONSUMER_INCIDENCE = (D(0),D(".25"),D(".5"),D(1))
GUARANTEE_SHARE = (D(0),D(".1"),D(".25"))
NEXTDC_DEFERRED_AUD_M = D(140)
NEXTDC_LOST_MARKET_VALUE_AUD_M = D(3000)
NEXTDC_PRIOR_FY27_NET_REVENUE_M = (D(615),D(640))
NEXTDC_NEW_FY27_NET_REVENUE_M = (D(475),D(500))
NEXTDC_PRIOR_FY27_EBITDA_M = (D(385),D(410))
NEXTDC_NEW_FY27_EBITDA_M = (D(245),D(265))
SOURCES = {
 "demand": "https://www.oxfordeconomics.com/resource/data-centres-energy-demand-outlook-in-australia/",
 "NEXTDC": "https://www.reuters.com/world/asia-pacific/australian-ai-data-centre-operator-nextdc-shares-shed-44-revenue-delay-2026-10-21/"}

def midpoint(x): return sum(x)/2

def compute():
    energy=[]
    for (year,demand),price,share in product(NEM_FY_TWH.items(),TARIFF_AUD_MWH,CONSUMER_INCIDENCE):
        # TWh × $/MWh = millions of AUD (1 TWh = 1,000,000 MWh)
        gross=demand*price
        consumer=gross*share
        remaining=gross-consumer
        assert consumer+remaining==gross
        energy.append({"fy":year,"nem_twh":float(demand),
            "mean_gw":float(demand/D("8.76")),
            "tariff_assumption_aud_mwh":float(price),
            "consumer_incidence_assumption":float(share),
            "gross_value_aud_m":float(gross),
            "consumer_incidence_aud_m":float(consumer),
            "other_incidence_aud_m":float(remaining)})
    guarantees=[]
    for share in GUARANTEE_SHARE:
        public=share*NEXTDC_DEFERRED_AUD_M
        private=NEXTDC_DEFERRED_AUD_M-public
        assert public+private==NEXTDC_DEFERRED_AUD_M
        guarantees.append({"guarantee_share_assumption":float(share),
                           "public_exposure_aud_m":float(public),
                           "private_exposure_aud_m":float(private)})
    rev=midpoint(NEXTDC_PRIOR_FY27_NET_REVENUE_M)-midpoint(NEXTDC_NEW_FY27_NET_REVENUE_M)
    ebitda=midpoint(NEXTDC_PRIOR_FY27_EBITDA_M)-midpoint(NEXTDC_NEW_FY27_EBITDA_M)
    return {
      "schema":"dashi-cybersyn-source-anchored-sensitivity-v1",
      "sources":SOURCES, "energy":energy, "guarantees":guarantees,
      "diagnostics":{"fy36_over_fy26_demand_multiple":float(NEM_FY_TWH[2036]/NEM_FY_TWH[2026]),
        "incremental_fy36_over_fy26_twh":float(NEM_FY_TWH[2036]-NEM_FY_TWH[2026]),
        "nextdc_revenue_midpoint_revision_aud_m":float(rev),
        "nextdc_ebitda_midpoint_revision_aud_m":float(ebitda),
        "nextdc_ebitda_midpoint_drop_percent":float(100*ebitda/midpoint(NEXTDC_PRIOR_FY27_EBITDA_M)),
        "market_value_repricing_over_deferred_revenue":float(NEXTDC_LOST_MARKET_VALUE_AUD_M/NEXTDC_DEFERRED_AUD_M)},
      "conservation_checked":True,"real_data_timeseries_backtest":False,
      "empirical_macro_validation_completed":False,
      "authoritative_jmd_builder_integrated":False,
      "agda_kernel_accepted":False}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--out",type=Path,required=True)
    args=p.parse_args()
    args.out.mkdir(parents=True,exist_ok=True)
    r=compute()
    (args.out/"sourced_sensitivity.json").write_text(json.dumps(r,indent=2,sort_keys=True)+"\n")
    for field in ("energy","guarantees"):
        with (args.out/(field+".csv")).open("w",newline="") as f:
            writer=csv.DictWriter(f,fieldnames=r[field][0].keys())
            writer.writeheader();writer.writerows(r[field])
    print(json.dumps({"energy_cases":len(r["energy"]),"guarantee_cases":len(r["guarantees"]),**r["diagnostics"]},indent=2))

if __name__=="__main__": main()

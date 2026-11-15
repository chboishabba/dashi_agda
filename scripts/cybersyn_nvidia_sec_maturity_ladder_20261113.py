#!/usr/bin/env python3
"""SEC primary-source NVIDIA fiscal-2027 10-Q contractual-commitment timing.

Main scheduled commitments ($366bn), separately reported additional commitments
($56bn), $3.5bn AI-cloud guarantee gross cap, and $105bn phased Ohio guarantee
are DISTINCT accounting classes, potentially overlapping; never sum into
immediate loss or present guarantee caps as dollars drawn.
"""
from __future__ import annotations
import argparse,csv,json
from pathlib import Path

SOURCE="https://www.sec.gov/Archives/edgar/data/1045810/000104581026000075/nvda-20260726.htm"
YEARS=("FY2027_remainder","FY2028","FY2029","FY2030","FY2031","FY2032_plus")
MAIN={
 "supply_and_capacity":(92,87,88,6,5,1),
 "cloud_service_agreements":(3,8,7,6,4,1),
 "uncommenced_data_centre_leases":(0,1,1,2,1,20),
 "equity_investments":(18,3,2,2,0,0),
 "capital_expenditures":(7,1,0,0,0,0)}
ADDITIONAL={
 "AI_cloud_agreements":(0,6,8,7,6,9),
 "third_party_uncommenced_leases":(0,0,1,1,1,17)}

def compute():
    ledger=[]
    for family,table in (("main_scheduled",MAIN),("additional",ADDITIONAL)):
        for i,year in enumerate(YEARS):
            row={"family":family,"fiscal_year":year,
                 "components_total_usd_bn":sum(v[i] for v in table.values())}
            row.update({key:v[i] for key,v in table.items()})
            ledger.append(row)
    main=sum(r["components_total_usd_bn"] for r in ledger if r["family"]=="main_scheduled")
    extra=sum(r["components_total_usd_bn"] for r in ledger if r["family"]=="additional")
    assert main==366 and extra==56
    assert sum(MAIN["supply_and_capacity"])==279
    assert sum(ADDITIONAL["AI_cloud_agreements"])==36
    return {
      "source":SOURCE, "as_of_source":"2026-07-26",
      "ledger":ledger, "main_scheduled_total_usd_bn":main,
      "additional_commitments_total_usd_bn":extra,
      "main_first_three_fiscal_years_usd_bn":
         sum(r["components_total_usd_bn"] for r in ledger[:3]),
      "Ohio_guarantee_max_usd_bn":105,
      "AI_cloud_guarantee_gross_cap_usd_bn":3.5,
      "Ohio_guarantee_earliest_first_phase_expected":"FY2029",
      "warning":"Do not add heterogeneous totals/caps or infer immediate payment. The Ohio guarantee is phase-triggered.",
      "kernel_certified":False,"empirical_loss_realisation_proven":False}
def main():
    p=argparse.ArgumentParser();p.add_argument("--out",type=Path,required=True)
    a=p.parse_args();a.out.mkdir(parents=True,exist_ok=True)
    r=compute()
    for family in ("main_scheduled","additional"):
        rows=[x for x in r["ledger"] if x["family"]==family]
        with (a.out/(family+".csv")).open("w",newline="") as f:
            w=csv.DictWriter(f,fieldnames=rows[0].keys())
            w.writeheader();w.writerows(rows)
    (a.out/"nvidia_sec_maturity_receipt.json").write_text(json.dumps(
      {k:v for k,v in r.items() if k!="ledger"},indent=2)+"\n")
    print(json.dumps({"main_usd_bn":r["main_scheduled_total_usd_bn"],
          "additional_usd_bn":r["additional_commitments_total_usd_bn"]},sort_keys=True))
if __name__=="__main__":main()

#!/usr/bin/env python3
"""Woogaroo 2019/8575 Avonvale prior-legal-security identity cut.

Source A: Providence East/South EPBC 2018/8347 Year-1 ACR (SHG 13 Mar
2024), Appendix F reproduces Queensland Department of Resources' own
21 December 2022 VMA s19F decision (DAM 2022/002500; PMAV 2022/002505).
Source B: Springfield EPBC 2019/8575 January 30 PD v5 Part A.i 6.4,
Avonvale OAMP A.iii: 168 ha 'balance land' ADJACENT to older offsets.
The state 2022 notice is first-party ORIGINAL GOVERNMENT TEXT reproduced
in a separate project's proponent PDF. Original current titles/GIS and
the new October 2026 official OAMP remain unverified. No cross-matter
condition breach or double credit proven. Preserve original authorship.
"""
import json,argparse
from pathlib import Path
OLD = {"1 CSH1549","4 SP327519","5 SP327519","9 SP327519","10 SP327519"}
NEW = {"2 SP330365","3 SP327519","1 RP75222","98 CA31786","61 CA31716"}
def run():
    assert len(OLD)==len(NEW)==5
    assert not (OLD & NEW)
    assert {"4 SP327519","10 SP327519"} <= OLD
    assert "3 SP327519" in NEW
    return {
      "original_earlier_EPBC_action":"2018/8347 Providence East and South",
      "original_later_EPBC_action":"2019/8575 Springfield Residential Development",
      "original_state_declaration_notice_date":"2022-12-21",
      "original_declared_area_map":"DAM 2022/002500",
      "original_PMAV":"PMAV 2022/002505",
      "prior_notice_original_source_class":"Queensland Department of Resources section 19F decision, reproduced in Providence 2024 ACR Appendix F",
      "earlier_source_url":"https://www.stockland.com.au/globalassets/residential/qld/providence/offset-management-plan/providence-east-epbc-acr--year-1-13032024.pdf",
      "earlier_original_notice_parcels":sorted(OLD),
      "later_original_PD_v5_parcels":sorted(NEW),
      "later_reported_168ha_balance_land_adjacent_to_older_EPBC_offsets":True,
      "literal_parcel_identifier_intersection":sorted(OLD & NEW),
      "identical_reported_lot_plan_references":False,
      "spatial_nonoverlap_proved":False,
      "earlier_current_registered_title_verified":False,
      "later_2026_October_approved_OAMP_verified":False,
      "independent_incremental_benefit_calibrated":False,
      "double_counting_or_financial_transfer_proved":False,
      "actual_C24_2019_8575_VDEC_proved":False,
      "actual_filing_or_breach_proved":False,
      "notified_prior_EPBC_project_date_per_proponent_report":"2022-12-23",
      "independent_cadastre_and_management_ledger_still_required":True
    }
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--agda-file",type=Path)
    ap.add_argument("--out",type=Path)
    a=ap.parse_args()
    if a.agda_file:
        s=a.agda_file.read_text()
        for k in ("priorDeclarationSourceFound","laterAdjacentClaimSourceFound",
                  "doubleCreditingNotEstablished","existingStateDeclaration"):
            assert k in s,k
        assert "{!!}" not in s and "postulate " not in s
    obj=run()
    obj["agda_source_marker_checked"]=bool(a.agda_file)
    blob=json.dumps(obj,indent=2,sort_keys=True)+"\n"
    if a.out:a.out.write_text(blob)
    print(blob,end="")
if __name__=="__main__":main()

#!/usr/bin/env python3
"""EPBC 2019/8575, source-qualified original s158A listing event gate.

Primary law: EPBC Act s158A(1)(k), (2)-(5), 1 July 2026 compilation.
2010 Commonwealth 'Listing Events under the EPBC Act' policy statement.
Original controlled-action date 9 April 2020 is from project consultant
PD rather than an obtained official 2020 s75 determination. Official 2026
s95A notice independently confirms the action was already controlled.
Koala relisted Endangered 12 February 2022. Approval 16 October 2026.

This is an interpretative compliance/litigation boundary, not legal
advice or a binding ruling. The 1.2%-discount OAG scenario remains an
ecological counterfactual, *not* an established invalidity ground.
"""
import json
import argparse
from datetime import date
from pathlib import Path

def run():
    controlled=date(2020,4,9)
    uplisting=date(2022,2,12)
    approval=date(2026,10,16)
    assert controlled < uplisting < approval
    relevant="EPBC 2019/8575"
    return {
      "case":relevant,
      "source_75_date_as_proponent_reports":controlled.isoformat(),
      "section75_original_instrument_obtained":False,
      "official_controlled_action_existential_notice":True,
      "uplisting_date_official":uplisting.isoformat(),
      "approval_instrument_date":approval.isoformat(),
      "original_statutory_owner":"EPBC Act 1999 s158A(1)(k),(2),(3),(4),(5)",
      "pre2022_original_s158a_exists":True,
      "uplisting_event_after_section75":True,
      "section158a_apparent_applicability":"strong statutory obstacle to using 2022 uplisting alone as legal invalidity ground",
      "2019_vulnerable_OAG_percentage_reconstruction":"108.3451326196",
      "2022_endangered_OAG_percentage_counterfactual":"88.8287572224",
      "endangered_OAG_legally_required_proved":False,
      "independent_scientific_offset_adequacy_resolved":False,
      "record_of_minister_actual_consideration":False,
      "legal_counsel_or_judgment_receipt":False,
      "Agda_kernel_accepted":False
    }
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--agda-file",type=Path)
    p.add_argument("--out",type=Path)
    a=p.parse_args()
    if a.agda_file:
        s=a.agda_file.read_text()
        for marker in ("section75OriginalStillUnacquired","noAutomaticStatusBasedInvalidity","doesNotRemoveScientificOffsetReview"):
            assert marker in s,marker
        assert "postulate " not in s and "{!!}" not in s
    d=run()
    d["source_contract_checked"]=a.agda_file is not None
    text=json.dumps(d,sort_keys=True,indent=2)+"\n"
    if a.out:a.out.write_text(text)
    print(text,end="")
if __name__=="__main__":
    main()

#!/usr/bin/env python3
"""EPBC 2019/8575 signed 16-Oct-2026 instrument: falsifiable P0 record gates.

SOURCE: local independently SHA-256-identified 50-page signed decision.
All action-area and habitat numbers are *printed map labels*, not an
independently verified spatial polygon intersection. 128 ha is from the
older January PD/OAG and is NOT assumed identical to the signed
development footprint or the 3 July 2026 PD Issue F.

Original authors remain attributed: National EPA 2026 signed decision;
Saunders Havill, BAAM, One Environment plans; QUT/QCC/RSPCA outside this
primary government instrument. Nothing implies actual commencement,
missing declaration, legal breach, ministerial extension, FOI, litigation,
money transfer or off-action Scenic 2020/8651 evidence.
"""
from __future__ import annotations
import argparse, hashlib, json
from datetime import date, timedelta
from pathlib import Path
from fractions import Fraction as F

CASE="EPBC 2019/8575"
PDF_SHA256="f9b591f230458939dbeafc8b6178c148dbbec3e68e5e75f66fd187e2a402b808"
APPROVAL=date(2026,10,16)
AS_OF=date(2026,11,9)
PLANS={
 "Avonvale":{"author":"One Environment",
             "reference":"Oes1:v1.2(e)","date":"2026-10-15"},
 "Esk":{"author":"BAAM Ecological Consultants",
        "reference":"0102-059 Version 6","date":"2026-10-15"},
 "Mount Walker West":{"author":"Saunders Havill Pty Ltd",
                      "reference":"9612-E Issue D","date":"2026-10-15"}
}
APPROVED_PD={"author":"Saunders Havill Group","reference":"Preliminary Report (Part A), issue F","date":"2026-07-03"}
KNOWN_UNVERIFIED={
 "source_exact_2026_07_PD_Issue_F":None,
 "downloaded_OAMPs_content_revisions_match_signed_identifiers":None,
 "written_ministerial_exception_C48":None,
 "website_timestamped_version_publication":None,
 "Avonvale_original_s19F_declaration":None,
 "Esk_original_s19F_declaration":None,
 "MWW_original_s19F_declaration":None,
 "actual_2019_8575_action_commencement":None,
 "actual_2019_8575_outside_phase_one_commencement":None,
 "s95B_full_comments_and_response_packet":None,
 "s95C_recommendation":None,
 "dated_original_2020_section75_instrument":None,
 "original_AU_GPS_scientific_justification":None,
}
# None is explicit UNKNOWN, not False (a verified negative record).
def business_days_after(start, n, holidays=()):
    h=set(holidays)
    day=start
    passed=[]
    while len(passed)<n:
        day+=timedelta(days=1)
        if day.weekday()<5 and day not in h:passed.append(day)
    return day,passed

def audit(signed_pdf:Path|None=None,agda:Path|None=None):
    # Official QLD holiday list shows no general Queensland holiday in window.
    deadline,dates=business_days_after(APPROVAL,15)
    assert deadline==date(2026,11,6),dates
    assert deadline<AS_OF
    assert len(PLANS)==3
    assert F("123.0")+F("8.2")+F("1.2")+F("2.5")==F("134.9")
    assert F("162.3")-F("27.3")==F("135.0")
    assert F("135.0")-F("134.9")==F("0.1")
    assert F("134.9")-F("128.0")==F("6.9")
    assert F("162.3")-F("128.0")==F("34.3")
    assert F("34.3")-F("27.3")==F("7.0")
    assert F("134.9")-F("56.4")==F("78.5")
    assert all(v is None for v in KNOWN_UNVERIFIED.values())
    if signed_pdf is not None:
        digest=hashlib.sha256(signed_pdf.read_bytes()).hexdigest()
        assert digest==PDF_SHA256,digest
    if agda is not None:
        src=agda.read_text()
        for marker in (
          "definedImpactFootprintTenths","historicalOAGImpactVsDefinedFootprint",
          "minimumUnclearedKoalaAreaIfFullHabitatMap", "minimumOutsideRetentionUnclearedKoalaArea",
          "phaseOneDoesNotRequireMWWDeclarationUnderC25",
          "outsidePhaseOneNeedsMWWDeclaration",
          "currentPubliclyAcquiredEvidence",
          "ordinary15thBusinessDayYYYYMMDD",
          "avonvaleFinal","eskFinal","mountWalkerFinal"):
            assert marker in src,marker
        assert "postulate " not in src and "{!!}" not in src
    return {
      "case":CASE,
      "as_of":str(AS_OF),
      "signed_approval_date":str(APPROVAL),
      "signed_approval_sha256":PDF_SHA256,
      "pdf_sha256_locally_verified":signed_pdf is not None,
      "agda_source_contract_checked":agda is not None,
      "binding_document_revisions_named_by_signed_instrument":PLANS,
      "later_preliminary_documentation_issue_F":APPROVED_PD,
      "historical_calculator_input_source":"Jan 2026 preliminary documentation v5",
      "historical_calculator_not_assumed_approved":True,
      "operative_condition4_per_species_maximum_habitat_clearing_ha":{"Koala":"128.0","Grey-headed Flying-fox":"128.0","Swift Parrot":"128.0","Regent Honeyeater":"128.0","Collared Delma":"0.77"},
      "conditionally_required_un-cleared_mapped_koala_habitat_ha":"34.3",
      "minimum_koala_habitat_uncleared_outside_27_3ha_retention_ha":"7.0",
      "these_area_numbers_are_not_independently_overlaid_GIS":True,
      "approved_impact_footprint_ha":"134.9",
      "mapped_koala_habitat_in_action_area_ha":"162.3",
      "retained_vegetation_ha":"27.3",
      "habitat_minus_retention_ha":"135.0",
      "difference_habitat_minus_retention_to_footprint_ha":"0.1",
      "difference_footprint_to_historical_koala_OAG_input_ha":"6.9",
      "action_phase_one_ha":"56.4",
      "other_phases_within_footprint_difference_ha":"78.5",
      "condition_24":"Avonvale + Esk Voluntary Declarations prior to ANY commencement",
      "condition_25":"MWW Voluntary Declaration before CLEARING/CONSTRUCTION OUTSIDE Phase One",
      "condition_27":"offset plan implementation at the times specified in signed approval",
      "condition_48":"named plans published within 15 business days of decision unless Minister agrees otherwise in writing",
      "condition_49":"current/superseded plans easily accessible and downloadable",
      "condition_52":"notice to agency within 5 business days after action commencement",
      "ordinary_condition_48_deadline":str(deadline),
      "workdays_counted":[str(d) for d in dates],
      "publication_requirement_elapsed_as_of_today":True,
      "actual_publication_or_extension_status":"UNVERIFIED",
      "actual_breach_proved":False,
      "all_remaining_primary_receipts":KNOWN_UNVERIFIED,
      "website_evidence":"Stockland Springview page lists 3 OMP downloads, but revisions and first-publication timestamps not established",
      "transitional_listing":"section 158A adverse-authority remains; status-only legal invalidity not proved",
      "off_action_Scenic_2020_8651_excluded":True,
      "agda_kernel_checked":False
    }

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--signed-pdf",type=Path)
    p.add_argument("--agda-file",type=Path)
    p.add_argument("--output",type=Path)
    args=p.parse_args()
    result=audit(args.signed_pdf,args.agda_file)
    blob=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if args.output:args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(blob)
    print(blob,end="")

if __name__=="__main__":main()

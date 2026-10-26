#!/usr/bin/env python3
"""Fail-closed structural audit of the sourced 3B-centralizer D4 GAP receipt.

This audits the internal consistency of a generated receipt, NOT execution
authenticity of GAP/AtlasRep and NOT validity of an alleged Monster embedding.
No receipt => no external-world claim. Pair characters are in Z[zeta].
"""
import argparse,json
from pathlib import Path

def verify(x):
    if not isinstance(x,dict) or x.get("source_table")!="MN3B":
        raise ValueError("actual MN3B source group marker required")
    if x.get("centralizer_only") is not True or x.get("centralizer_index_in_normalizer")!=2:
        raise ValueError("D4 must act within the chosen phase-preserving 3B centralizer")
    if x.get("actual_checked_extraspecial_E") is not True:
        raise ValueError("requires selected actual E,z verification, not just arbitrary group")
    if x.get("identity_zeta_trace")!=[65610,0]:
        raise ValueError("selected 3B phase must have dimension 65610")
    expected=[65610,810,90,2430,2430]
    if x.get("geometric_D4_character")!=expected:
        raise ValueError("wrong exact geometric D4 character")
    match=x.get("actual_D4_witness_runtime_observed")
    truncated=x.get("search_truncated")
    exhausted=x.get("screen_exhausted")
    negative=x.get("certified_no_compatible_D4")
    if any(type(flag) is not bool for flag in (match,truncated,exhausted,negative)):
        raise ValueError("all proof-status flags must be booleans")
    count=x.get("pairs_tested")
    tested=x.get("d4_subgroups_tested_with_duplicates")
    ambiguous=x.get("ambiguous_source_class_tests")
    if any(type(v) is not int or v<0 for v in (count,tested,ambiguous)):
        raise ValueError("nonnegative integer screening counts required")
    if tested>count or ambiguous>tested:
        raise ValueError("inconsistent subgroup screening inventory")
    if match and (negative or exhausted or truncated):
        raise ValueError("a witness cannot coexist with no-go or truncated status")
    if exhausted != (not match and not truncated):
        raise ValueError("exhaustion status incoherent")
    if negative != (exhausted and ambiguous==0):
        raise ValueError("no-go requires completed exhaustion and no unresolved class values")
    rows=x.get("matched_first_witness")
    if not isinstance(rows,list):raise ValueError("witness list missing")
    if match:
        if len(rows)!=8:raise ValueError("matched D4 must have exactly eight group elements")
        orders=[v.get("element_order") for v in rows]
        if orders.count(1)!=1 or orders.count(4)!=2 or orders.count(2)!=5:
            raise ValueError("D4 element order distribution must be 1,5,2")
        wanted=[v.get("expected") for v in rows]
        if (wanted.count(65610),wanted.count(810),wanted.count(90),
            wanted.count(2430))!=(1,1,2,4):
            raise ValueError("expected D4 character class multiplicity wrong")
        for row in rows:
            trace=row.get("ordinary_trace_triple")
            phase=row.get("zeta_trace_pair")
            w=row.get("expected")
            if not (isinstance(trace,list) and len(trace)==3 and
                    all(type(t) is int for t in trace)):
                raise ValueError("three exact ordinary character values required")
            A,B,C=trace
            if (A-B)%3 or (C-B)%3 or phase!=[(A-B)//3,(C-B)//3] or phase!=[w,0]:
                raise ValueError("claimed D4 trace fails the exact zeta projector")
            if type(row.get("uniquePositions")) is not bool:
                raise ValueError("class-position uniqueness status missing")
        identity=next(row for row in rows if row["element_order"]==1)
        if identity["ordinary_trace_triple"]!=[196883,53,53]:
            raise ValueError("selected Monster 3B identity triple mismatches sources")
    elif rows:
        raise ValueError("unsuccessful screen cannot expose a matched witness")
    if negative and truncated:
        raise ValueError("partial screen cannot certify universal obstruction")
    return dict(status="receipt_structurally_consistent_not_independently_authenticated",
                actual_subgroup_execution_authenticated=False,
                phase_preserving_input=True,
                candidate_D4_matches_geometry=match,
                exhausted_all_tested_pairs=exhausted,
                conditional_no_compatible_D4=negative,
                unresolved_subgroups=ambiguous,
                distinguished_3B_sector_dimension=65610,
                no_mmgroup_required=True)

def selftest():
    base=dict(source_table="MN3B",centralizer_only=True,
        centralizer_index_in_normalizer=2,actual_checked_extraspecial_E=True,
        identity_zeta_trace=[65610,0],geometric_D4_character=[65610,810,90,2430,2430],
        actual_D4_witness_runtime_observed=False,screen_exhausted=False,
        search_truncated=True,pairs_tested=3,d4_subgroups_tested_with_duplicates=3,
        ambiguous_source_class_tests=1,certified_no_compatible_D4=False,
        matched_first_witness=[])
    assert verify(base)["conditional_no_compatible_D4"] is False
    for change in ({"certified_no_compatible_D4":True},
                   {"centralizer_only":False},
                   {"identity_zeta_trace":[65610,1]},
                   {"actual_D4_witness_runtime_observed":True}):
        bad=dict(base,**change)
        try:verify(bad)
        except ValueError:pass
        else:raise AssertionError("invalid claim was accepted: "+str(change))
    return dict(status="structural positive and four negative controls passed",
                authentic_GAP_receipt_supplied=False,mmgroup_required=False)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("receipt",nargs="?",type=Path)
    p.add_argument("--selftest",action="store_true")
    a=p.parse_args()
    if a.selftest:result=selftest()
    elif a.receipt and a.receipt.is_file():result=verify(json.loads(a.receipt.read_text()))
    else:p.error("real GAP receipt required (or --selftest for limited harness)")
    print(json.dumps(result,indent=2))
if __name__=="__main__":main()

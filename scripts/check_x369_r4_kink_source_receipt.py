#!/usr/bin/env python3
"""Fail-closed four-stage SAME-SOURCE ResponseKink interval adapter for R4.

This implements the comparison contract of existing
DASHI.Cognition.ResponseKink.RecruitmentSuppressionProfile.
It does not verify claimed checkpoint hashes, trained-model observations,
or biological mechanism. All interval endpoints are exact rational strings.
"""
import json
import re
import sys
from fractions import Fraction as Q

def refuse(reason):
    raise ValueError("R4_KINK_SOURCE_REFUSED "+reason)

def rational(text):
    if not isinstance(text,str) or not re.fullmatch(r"-?\d+(?:/\d+|\.\d+)?",text):
        refuse("not a rational-string endpoint")
    return Q(text)

def certify(data):
    if data.get("schema")!="x369_r4_original_kink_v1":
        refuse("wrong schema")
    if data.get("original_source_export_verified") is not True:
        refuse("original source export not verified")
    if data.get("interval_error_receipt_verified") is not True:
        refuse("source response errors not verified")
    sha=data.get("checkpoint_sha256")
    if not isinstance(sha,str) or not re.fullmatch(r"[a-f0-9]{64}",sha):
        refuse("checkpoint SHA syntax")
    if not isinstance(data.get("history_revision"),str) or not data["history_revision"]:
        refuse("missing original history revision")
    observable=data.get("response_observable")
    if not isinstance(observable,str) or not observable:
        refuse("missing typed response observable")
    states=data.get("stages")
    if not isinstance(states,list) or len(states)!=4:
        refuse("exactly four ordered comparable source states required")
    loads=[];bounds=[]
    expected=["insufficient","recruited","selected","overloaded"]
    for name,st in zip(expected,states):
        if not isinstance(st,dict) or st.get("stage")!=name:
            refuse("ordered regime identity mismatch")
        if st.get("checkpoint_sha256")!=sha or st.get("history_revision")!=data["history_revision"]:
            refuse("states must bind same checkpoint and authoritative history")
        if st.get("response_observable")!=observable:
            refuse("mixed response types")
        if st.get("source_state_verified") is not True:
            refuse("unverified original source state")
        load=rational(st.get("load"))
        low=rational(st.get("response_lower"))
        high=rational(st.get("response_upper"))
        if low>high:refuse("inverted response interval")
        loads.append(load)
        bounds.append((low,high))
    if not all(a<b for a,b in zip(loads,loads[1:])):
        refuse("source loads must be strictly increasing")
    comparisons=((0,1),(1,2),(3,2))
    for i,j in comparisons:
        if not bounds[i][1]<bounds[j][0]:
            refuse("four-stage order undecidable or false "+str((i,j)))
    return {
        "status":"CONDITIONAL_SAME_SOURCE_KINK_INTERVAL",
        "source_response_observable":observable,
        "source_shape_deduced":True,
        "checkpoint_authenticated_by_this_script":False,
        "biological_or_causal_mechanism_certified":False,
        "original_R4_FFN_execution_verified":False}

if __name__=="__main__":
    if len(sys.argv)!=2:raise SystemExit("usage: check_x369_r4_kink_source_receipt.py receipt.json")
    try:
        with open(sys.argv[1],encoding="utf8") as f: data=json.load(f)
        print(json.dumps(certify(data),sort_keys=True))
    except (OSError,ValueError,KeyError,TypeError) as exc:
        raise SystemExit(str(exc))

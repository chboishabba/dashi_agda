#!/usr/bin/env python3
"""Fail-closed CONSUMER for the source-first GAP class-fusion receipt.

A JSON fixture, by itself, cannot authenticate CTblLib/GAP or original
Monster classes. Only a genuine unmodified source GAP session plus
published ATLAS/Barraclough--Wilson maps can pay that source obligation.
This checks schema, nonpromotion, totality/uniqueness and routes the
RESULT into the already-existing #1250 Suzuki phase-parity checker.
"""
import argparse
import json
from pathlib import Path
from monster_3b_suzuki_c2_parity_6class_conditional_gate import (
    select_rotation_class,
)

SCHEMA="monster3b-atlas-source-Suz2B-to-Monster4-fusion-v1"
BOUNDED={"4A","4C","4D"}
KEYS=("two_suz_class_position","six_suz_class_position",
      "main_class_position","mn3b_class_position","monster_class_position")
SOURCE_NOT_PROMOTED=("literal_source_word_2Suz_class_individually_identified",
                     "actual_6Suz_degree78_family_selected",
                     "full_actual_Monster_Hom_constructed")

def validate(p):
    if not isinstance(p,dict) or p.get("schema")!=SCHEMA:
        raise ValueError("unexpected source class-fusion receipt schema")
    rows=p.get("candidates")
    if not isinstance(rows,list) or not rows:
        raise ValueError("nonempty source class list required")
    if type(p.get("source_two_suz_order4_candidates_count")) is not int or (
      p["source_two_suz_order4_candidates_count"]!=len(rows)):
        raise ValueError("source twoSuz candidate count mismatch")
    for k in ("source_suz_2b_position","source_suz_outer_position",
              "source_two_suz_central_minus_one_position",
              "actual_monster_twoB_position"):
        if type(p.get(k)) is not int or p[k]<1:
            raise ValueError("invalid original source class coordinate: "+k)
    seen=set()
    for row in rows:
        if not isinstance(row,dict):
            raise ValueError("source candidate must be object")
        for key in KEYS:
            if type(row.get(key)) is not int or row[key]<=0:
                raise ValueError("invalid class index "+key)
        lbl=row.get("monster_four_label")
        if lbl not in BOUNDED:
            raise ValueError("source candidate outside Monster 4A/4C/4D")
        key=row["two_suz_class_position"]
        if key in seen:
            raise ValueError("duplicate source twoSuz class")
        seen.add(key)
    labels=sorted({row["monster_four_label"] for row in rows})
    if p.get("all_possible_monster_four_labels")!=labels:
        raise ValueError("candidate Monster class labels are not exhaustive")
    unique=len(labels)==1
    if p.get("actual_monster_four_class_uniquely_forced_by_class_fusions") is not unique:
        raise ValueError("source fusion uniqueness flag inconsistent")
    if p.get("status")!=(
       "UNIQUE_SOURCE_FUSION" if unique else "AMBIGUOUS_SOURCE_FUSION"):
        raise ValueError("source fusion status inconsistent")
    for k in SOURCE_NOT_PROMOTED:
        if p.get(k) is not False:
            raise ValueError("source receipt falsely promotes unpaid identity: "+k)
    allbranches={
        k:select_rotation_class(k) for k in labels
    }
    return {
      "schema":"monster3b-source-fusion-receipt-semantic-validation-v1",
      "validation_passed":True,
      "source_gap_execution_authenticated_by_python":False,
      "source_twoSuz_candidate_count":len(rows),
      "admissible_monster_four_classes":labels,
      "selected_monster_four_class":labels[0] if unique else None,
      "conditional_class_phase_branches":allbranches,
      "source_selected_degree78_claim_allowed":False,
      "actual_Monster_Hom_claim_allowed":False,
      "next_source_obligation":(
        "Authenticate the actual source GAP receipt and group-class generator weld"
        if unique else
        "Resolve the actual source r conjugacy class among remaining 2.Suz.2 classes"
      ),
    }

if __name__=="__main__":
    a=argparse.ArgumentParser()
    a.add_argument("receipt",type=Path)
    a.add_argument("--out",type=Path)
    ns=a.parse_args()
    v=validate(json.loads(ns.receipt.read_text()))
    blob=json.dumps(v,indent=2,sort_keys=True)+"\n"
    if ns.out:ns.out.write_text(blob)
    print(blob,end="")

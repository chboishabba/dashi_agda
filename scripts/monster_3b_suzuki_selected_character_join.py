#!/usr/bin/env python3
"""Source-relative join of existing 6.Suz full-class and Monster-selected receipts.

Consumers (DO NOT duplicate their character/quotient algorithms):
  monster_3b_suzuki_all_conductors_character_audit.audit
  render_monster_3b_suzuki_main_quotient_match.validate

Original roots: Barraclough--Wilson (2007), Monster N(3B) table and
character fusions; Nebe (2025), degree-78 Suzuki symmetric square.
An authenticated actual-source/GAP run, full normalizer action and Agda
kernel typecheck are NOT established merely by passing this contract.
"""
import argparse
import hashlib
import json
from pathlib import Path

def check(source, selected, *, audit_fn, selected_validate_fn):
    if not isinstance(source,dict) or not isinstance(selected,dict):
        raise ValueError("two exact source JSON objects required")
    if source.get("table_id") != "6.Suz" or selected.get("six_suz_table") != "6.Suz":
        raise ValueError("both sources must identify 6.Suz")
    # RECOMPUTE, rather than trusting flags from a separately supplied audit.
    report=audit_fn(source)
    sel=selected_validate_fn(selected)
    # Bind ALL 6.Suz conjugacy-class coordinates, not merely the order,
    # class count, two central positions and source Irr row indices.
    # A noncentral class permutation can preserve those weaker fingerprints.
    signature_fields=(
        ("class_orders","six_suz_class_orders"),
        ("class_sizes","six_suz_class_sizes"),
        ("power_map_2_zero_based","six_suz_power_map_2_zero_based"),
    )
    for exported,selected_field in signature_fields:
        raw=source.get(exported)
        validated=sel[exported]
        if (not isinstance(raw,list) or not isinstance(validated,list)
                or len(raw)!=len(validated)
                or any(type(x) is not int for x in raw+validated)
                or raw!=validated or selected.get(selected_field)!=validated):
            raise ValueError("source class-coordinate signature mismatch: "+exported)
    signature={k:source[k] for k,_ in signature_fields}
    signature_hash=hashlib.sha256(
        json.dumps(signature,sort_keys=True,separators=(",",":")).encode("utf-8")
    ).hexdigest()
    if not report.get("orthogonality_executed"):
        raise ValueError("full class-weighted source character orthogonality required")
    for key,value in [
       ("suzuki_central_involution_class_position","central_c2_zero_based"),
       ("suzuki_central_order_three_class_position","central_c3_zero_based")]:
        if selected[key]-1 != source.get(value):
            raise ValueError("central class mismatch: "+key)
    table12={r["label"]:r for r in source["degree12"]}
    table78={r["label"]:r for r in source["degree78"]}
    pair12=sel["labels12"];pair78=sel["labels78"]
    if set(pair12)!=set(table12) or not set(pair78).issubset(table78):
        raise ValueError("source-selected pair absent from exported full-class rows")
    # Atlas labels are descriptive, not a sufficient same-table binding.
    # Bind each selected character to its literal source Irr position.
    # The original CTblLib head and class numbering are source data, not
    # independently inferred from a filename or a successful mock receipt.
    if source.get("group_order") != sel["source_order"]:
        raise ValueError("source group order differs between selected/exported tables")
    if len(source.get("class_orders",[])) != sel["source_classes"]:
        raise ValueError("source conjugacy-class count differs between the two receipts")
    if set(sel["positions12"]) & set(sel["positions78"]):
        raise ValueError("selected source irreducible 12/78 positions overlap")
    for labels,positions,table in (
        (pair12,sel["positions12"],table12),
        (pair78,sel["positions78"],table78)):
        if len(labels)!=len(positions):
            raise ValueError("selected source label and Irr position length mismatch")
        for label,position in zip(labels,positions):
            recorded=table[label].get("source_irreducible_position_1_based")
            if type(recorded) is not int or recorded!=position:
                raise ValueError("selected source Irr position mismatches ATLAS label "+label)
    all_positions=[
       v.get("source_irreducible_position_1_based")
       for v in (source["degree12"]+source["degree78"])
    ]
    if any(type(v) is not int or v<1 or v>sel["source_classes"]
           for v in all_positions) or len(set(all_positions))!=len(all_positions):
        raise ValueError("exported source Irr positions missing/invalid/duplicated")
    from monster_3b_suzuki_all_conductors_character_audit import Cyc
    c2=source["central_c2_zero_based"];c3=source["central_c3_zero_based"]
    p12vals=[Cyc.wire(table12[x]["values"][c3]) for x in pair12]
    p78vals=[Cyc.wire(table78[x]["values"][c3]) for x in pair78]
    roots=[Cyc.scalar(1),Cyc.from_coeffs(3,[0,1,0]),
           Cyc.from_coeffs(3,[0,0,1])]
    def phase(value,degree):
        hits=[k for k,z in enumerate(roots) if value==z*degree]
        if len(hits)!=1:
            raise ValueError("central C3 not pure scalar on irreducible")
        return hits[0]
    p12=[phase(x,12) for x in p12vals]
    p78=[phase(x,78) for x in p78vals]
    if sorted(p12)!=[1,2]:
        raise ValueError("faithful 12 conjugate C3 orientations absent")
    matching=sum(a==b for a in p12 for b in p78)
    if matching!=sel["common729_pairs"]:
        raise ValueError("original-source common-729 C3 phase count disagrees")
    signs=[]
    for label in pair78:
        v=Cyc.wire(table78[label]["values"][c2])
        if v==78:signs.append(1)
        elif v==-78:signs.append(-1)
        else:raise ValueError("selected 78 central C2 not scalar")
    for label in pair12:
        if Cyc.wire(table12[label]["values"][c2])!=-12:
            raise ValueError("selected 12 central C2 sign incorrect")
    if signs[0]!=signs[1]:
        raise ValueError("selected conjugate 78 pair inconsistent at central C2")
    trace=-12+78*signs[0]
    if trace!=sel["source_trace"]:
        raise ValueError("selected 90 centre C2 trace disagrees with actual class rows")
    if sel["selected_faithful"] and (signs[0]!=-1 or sorted(p78)!=[1,2]):
        raise ValueError("faithful 78 requires nontrivial central C2 and C3")
    matches=[x for x in report["matches"]
             if x["12"] in pair12 and x["78"] in pair78]
    direct=sum(x["mode"]=="Sym2" for x in matches)
    dual=sum(x["mode"]=="dualSym2" for x in matches)
    if direct!=sel["full_direct"] or dual!=sel["full_dual"]:
        raise ValueError("full character Sym2/dual counts contradict source selection")
    if (direct==2 and dual==2)!=sel["full_nebe"]:
        raise ValueError("selected full Sym2 family flag contradicts classwise audit")
    if sel["full_nebe"] and (trace!=66 or sel["selected_faithful"]):
        raise ValueError("actual full Sym2 cannot have selected faithful78 centre")
    return dict(status="SOURCE_RELATIVE_CHARACTER_JOIN_PASS",
        selected_atlas_12=list(pair12),selected_atlas_78=list(pair78),
        selected_irr_positions12=list(sel["positions12"]),
        selected_irr_positions78=list(sel["positions78"]),
        bound_suzuki_table_group_order=sel["source_order"],
        bound_suzuki_table_class_count=sel["source_classes"],
        selected_78_c3_exponents=list(p78),central_C2_trace=trace,
        matching_C3_phase_pairs=matching,
        selected_full_class_direct_sym2_count=direct,
        selected_full_class_dual_sym2_count=dual,
        selected_Nebe_family_full_class_equal=(direct==2 and dual==2),
        source_orthogonality_recomputed=True,
        complete_source_class_signature_matched=True,
        source_class_signature_sha256=signature_hash,
        original_source_authenticated=False,
        GAP_executed_by_this_check=False,
        same_object_Monster_intertwiner_proved=False)

def main():
    from monster_3b_suzuki_all_conductors_character_audit import audit
    from render_monster_3b_suzuki_main_quotient_match import validate
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("all_6suz_rows",type=Path)
    p.add_argument("monster_selected_receipt",type=Path)
    p.add_argument("--out",type=Path)
    a=p.parse_args()
    rows=a.all_6suz_rows.read_bytes()
    selected=a.monster_selected_receipt.read_bytes()
    result=check(json.loads(rows),json.loads(selected),
                 audit_fn=audit,selected_validate_fn=validate)
    result["provided_6suz_sha256"]=hashlib.sha256(rows).hexdigest()
    result["provided_monster_selected_sha256"]=hashlib.sha256(selected).hexdigest()
    rendered=json.dumps(result,indent=2)+"\n"
    if a.out:a.out.write_text(rendered)
    print(rendered,end="")

if __name__=="__main__":
    main()

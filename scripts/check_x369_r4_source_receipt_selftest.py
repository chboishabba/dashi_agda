#!/usr/bin/env python3
"""Synthetic fail-closed source-receipt regression. NOT trained evidence."""
from fractions import Fraction as Q
import copy
import check_x369_r4_source_receipt as receipt

eps=["1/256"]*6
base={
 "schema":"x369_r4_source_relative_v1",
 "arm":"coherent",
 "checkpoint_sha256":"0"*64,
 "checkpoint_hash_externally_verified":True,
 "source_export_verified":True,
 "source_float_evaluation_error_receipt_verified":True,
 "x":["2","0","0","0","0","0"],
 "histories":[[str(x) for x in h] for h in
   ((0,1,0,0,0,0),(1,0,1,0,0,0),
    (0,1,1,0,0,0),(1,1,0,0,0,0))],
 "history_weight":["0","1","1","0","0","0"],
 "directed_weight":["2","-1","1","1","0","2"],
 "expert_bias":["0","1","5","10"],
 "base_mask":[True,False],
 "top_k":2,
 "source_selected_ids":[2,3],
 "orientation_weight":["1"]+["0"]*11,
 "errors":{
   "x":eps,"histories":[eps]*4,
   "history_weight":eps,"directed_weight":eps,
   "expert_bias":["1/256"]*4,
   "differential_floating_eval":[["0"]*4 for _ in range(4)],
   "q_energy_eval":["0","0"],
   "orientation_weight":["1/256"]*12,
   "orientation_float_eval":["0"]*4}}

checks=0
for arm,ids in (("coherent",[2,3]),("mixed",[3,2])):
    d=copy.deepcopy(base)
    d["arm"]=arm
    d["source_selected_ids"]=ids
    r=receipt.certify(d)
    assert r["ordered_ids"]==ids
    assert Q(r["selected_softmax_L1_bound"])==Q(594441,8388608)
    assert r["source_checkpoint_authenticated_by_this_script"] is False
    assert r["full_recurrent_state_certified"] is False
    checks+=1
    for claim in ("source_export_verified",
                  "checkpoint_hash_externally_verified",
                  "source_float_evaluation_error_receipt_verified"):
        bad=copy.deepcopy(d)
        bad[claim]=False
        try:receipt.certify(bad)
        except ValueError:pass
        else:raise AssertionError("accepted missing "+claim)
        checks+=1
    bad=copy.deepcopy(d)
    bad["source_selected_ids"]=list(reversed(ids))
    try:receipt.certify(bad)
    except ValueError:pass
    else:raise AssertionError("wrong ordered source IDs accepted")
    checks+=1
    bad=copy.deepcopy(d)
    bad["orientation_weight"]=["0"]*12
    try:receipt.certify(bad)
    except ValueError:pass
    else:raise AssertionError("zero orientation score accepted")
    checks+=1

tie=copy.deepcopy(base)
tie["arm"]="mixed"
tie["x"]=["1","0","0","0","1","0"]
try:receipt.certify(tie)
except ValueError:pass
else:raise AssertionError("ambiguous original q gate accepted")
checks+=1
print("X369_SOURCE_RECEIPT_SYNTHETIC_SELFTEST_PASS",checks)

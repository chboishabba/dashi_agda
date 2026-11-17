#!/usr/bin/env python3
"""Synthetic four-stage ResponseKink source-adapter adversarial regression."""
import copy
from check_x369_r4_kink_source_receipt import certify

head="0"*64
values=["1","4","6","4"]
names=["insufficient","recruited","selected","overloaded"]
base={
 "schema":"x369_r4_original_kink_v1",
 "original_source_export_verified":True,
 "interval_error_receipt_verified":True,
 "checkpoint_sha256":head,
 "history_revision":"synthetic-fixture-rev",
 "response_observable":"synthetic-order-preserving-Nat-activity",
 "response_codomain":"Nat",
 "nat_observation_source_verified":True,
 "stages":[{
  "stage":name,"load":str(i),"response_nat":int(value),
  "response_lower":str(__import__("fractions").Fraction(value)-__import__("fractions").Fraction(1,20)),
  "response_upper":str(__import__("fractions").Fraction(value)+__import__("fractions").Fraction(1,20)),
  "checkpoint_sha256":head,"history_revision":"synthetic-fixture-rev",
  "response_observable":"synthetic-order-preserving-Nat-activity",
  "source_state_verified":True} for i,(name,value) in enumerate(zip(names,values))]}
count=0
assert certify(base)["source_shape_deduced"]
count+=1
def reject(label,mutator):
 global count
 case=copy.deepcopy(base)
 mutator(case)
 try:certify(case)
 except ValueError:count+=1
 else:raise AssertionError("accepted "+label)
reject("missing export",lambda d:d.update(original_source_export_verified=False))
reject("missing interval",lambda d:d.update(interval_error_receipt_verified=False))
reject("missing Nat projection",lambda d:d.update(nat_observation_source_verified=False))
reject("wrong source codomain",lambda d:d.update(response_codomain="Real"))
reject("tampered checkpoint",lambda d:d["stages"][2].update(checkpoint_sha256="f"*64))
reject("stale history",lambda d:d["stages"][3].update(history_revision="other-revision"))
reject("mixed observable",lambda d:d["stages"][1].update(response_observable="unrelated-score"))
reject("non-Nat response",lambda d:d["stages"][1].update(response_nat="4"))
reject("Nat response outside interval",lambda d:d["stages"][1].update(response_nat=5))
reject("unverified state",lambda d:d["stages"][2].update(source_state_verified=False))
reject("repeated load",lambda d:d["stages"][2].update(load="1"))
reject("reversed load",lambda d:d["stages"][1].update(load="3"))
reject("overlap rise",lambda d:d["stages"][1].update(response_lower="1"))
reject("overload not attenuated",lambda d:d["stages"][3].update(response_lower="7",response_upper="8"))
reject("inverted interval",lambda d:d["stages"][0].update(response_lower="3",response_upper="2"))
reject("swapped stage",lambda d:d["stages"][2].update(stage="overloaded"))
reject("source snapshot not a verified state",lambda d:d["stages"][0].pop("source_state_verified"))
print("X369_R4_EARLY_KINK_RECEIPT_SELFTEST_PASS",count)

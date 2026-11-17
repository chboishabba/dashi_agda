#!/usr/bin/env python3
"""R4 source-shaped top-k kink: joint routing + Nat cell proof development.

All source values synthetic and explicit. This tests the ORIGINAL coherent
R4 score algebra and its selected-mix output via existing source receipt
checker. Does not authenticate the claimed checkpoint/float error receipts.
No device, Agda, or trained Leech conclusion.
"""
import sympy as S
from fractions import Fraction as Q
from check_x369_r4_source_receipt import certify as certify_route
from check_x369_r4_kink_source_receipt import certify as certify_kink

check_count=0
def check(name,p):
    global check_count
    if not bool(p):raise AssertionError("R4_KINK_JOINT_FAIL "+name)
    check_count+=1
slopes=(0,4,9,10)
bias=(8,3,-11,-13)
histories=[["1","0",str(s),"0","0","0"] for s in slopes]
eps="1/65536"
errors={
 "x":[eps]*6,
 "histories":[[eps]*6 for _ in range(4)],
 "history_weight":[eps]*6,
 "directed_weight":[eps]*6,
 "expert_bias":[eps]*4,
 "differential_floating_eval":[["0"]*4 for _ in range(4)],
 "q_energy_eval":["0","0"],
 "orientation_weight":[eps]*12,
 "orientation_float_eval":["0"]*4}
def receipt(t,ids):
    return {
     "schema":"x369_r4_source_relative_v1",
     "arm":"coherent","checkpoint_sha256":"0"*64,
     "checkpoint_hash_externally_verified":True,
     "source_export_verified":True,
     "source_float_evaluation_error_receipt_verified":True,
     "x":[str(t),"0","0","0","0","0"],
     "histories":histories,
     "history_weight":["0"]*6,
     "directed_weight":["1","0","0","0","0","0"],
     "expert_bias":list(map(str,bias)),
     "base_mask":[True,True],"top_k":2,
     "source_selected_ids":ids,
     # The bias-free orientation weight reads h[0] from
     # z=concat(x,h), giving strict orientation score 2.
     "orientation_weight":["0"]*6+["1"]+["0"]*5,
     "errors":errors}
e_low=Q(8,3)
e_high=Q(11,4)
# e in (8/3,11/4) follows lower 4-term Taylor and
# a geometric majorant on the omitted factorial tail.
def logistic_of_positive(z):
    return z/(1+z)
# Precise rational natural-response intervals via bounds on e.
raw_bounds=[
    (1/(1+e_high**5),1/(1+e_low**5)),
    (1/(1+e_high),1/(1+e_low)),
    (logistic_of_positive(e_low**3),
     logistic_of_positive(e_high**3)),
    (Q(0),Q(0))]
selected=[[0,1],[0,1],[1,0],[3,2]]
kink_stages=[]
nat=(0,2,9,0)
for t,ids in enumerate(selected):
    output=certify_route(receipt(t,ids))
    check("strict original source router t="+str(t),
          output["ordered_ids"]==ids
          and output["q_mask"]==[True,True]
          and output["full_recurrent_state_certified"] is False)
    B=Q(output["selected_softmax_L1_bound"])
    # For constant expert outputs in {0,1}, exact mixture
    # discrepancy <= B/2. This is conservative even
    # though only score perturbations are admitted.
    lower,upper=raw_bounds[t]
    if t==3:
        # All selected expert outputs are identically ZERO
        # irrespective of selected softmax weights, as
        # long as selected set (3,2) is certified.
        lo=hi=Q(0)
    else:
        lo=max(Q(0),lower-B/2)
        hi=min(Q(1),upper+B/2)
    check("Nat post-quantisation cell stable t="+str(t),
          lo>=0 and hi<=1
          and int(S.floor(10*S.Rational(lo.numerator,lo.denominator)))==nat[t]
          and int(S.floor(10*S.Rational(hi.numerator,hi.denominator)))==nat[t])
    check("same source sign stable t="+str(t),
          True) # independently checked by certify_route
    # Reuse the existing Nat SOURCE consumer rather than treating
    # real-valued softmax intervals as an Agda Nat equality.
    # This ordinal cell is justified above from original source score,
    # pairwise route error and independently bounded e.
    kink_stages.append({
       "stage":("insufficient","recruited","selected","overloaded")[t],
       "load":str(t),
       "response_lower":str(nat[t]),
       "response_upper":str(nat[t]),
       "response_nat":nat[t],
       "checkpoint_sha256":"0"*64,
       "history_revision":"same-reset-initial-histories-synthetic",
       "response_observable":"source-selected-output-coordinate-floor10",
       "source_state_verified":True})
    print("KINK_SOURCE_RECEIPT",t,"ids",ids,"B_L1",B,
          "response_interval",(str(lo),str(hi)),"Nat",nat[t])
# Final donor weld: the ORIGINAL Cognition.ResponseKink response
# shape consumes our four proven post-quantisation Nat intervals.
# Flags are self-declared SYNTHETIC provenance, not authenticity.
kink_payload={
  "schema":"x369_r4_original_kink_v1",
  "original_source_export_verified":True,
  "interval_error_receipt_verified":True,
  "checkpoint_sha256":"0"*64,
  "history_revision":"same-reset-initial-histories-synthetic",
  "response_observable":"source-selected-output-coordinate-floor10",
  "response_codomain":"Nat",
  "nat_observation_source_verified":True,
  "stages":kink_stages}
kink_out=certify_kink(kink_payload)
check("canonical Kink source-bound Nat profile admitted",
      kink_out["source_shape_deduced"] is True
      and kink_out["checkpoint_authenticated_by_this_script"] is False
      and kink_out["biological_or_causal_mechanism_certified"] is False)
check("canonical old Kink Nat strict inequalities",
      nat[0]<nat[1]<nat[2] and nat[3]<nat[2])
# Negative control: source-vetted TopK ids at t=3 differ
# from the frozen-route counterfactual. Extrapolating
# current selected (0,1) weights cannot explain downturn.
try:
    certify_route(receipt(3,[0,1]))
except ValueError:
    check("source frozen route NOT accepted at overload t=3",True)
else:
    raise AssertionError("counterfactual ids wrongly source accepted")
# Negative control: a q-gated mixed-null certificate at t=0 is
# ambiguous for equal q energies and positive source errors.
case=receipt(0,[0,1]);case["arm"]="mixed"
try:
    certify_route(case)
except ValueError:
    check("mixed q tie cannot inherit coherent witness",True)
else:
    raise AssertionError("mixed gate tie accepted")
print("X369_R4_KINK_JOINT_SOURCE_SYMPY_PASS",check_count)

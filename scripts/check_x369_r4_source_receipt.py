#!/usr/bin/env python3
"""Read-only original R4 relative-decision receipt gate, using exact Fractions.

This does not load a checkpoint, authenticate its claimed SHA, run Torch,
infer quantizer guarantees or substitute for a native router execution.
External source/export/float-error provenance must be independently checked
and explicitly admitted. All source numeric inputs use exact rational
strings (not Python binary floats); no default error budgets are invented.
"""
import json
import re
import sys
from fractions import Fraction as Q

def fail(s):
    raise ValueError("X369_RECEIPT_FAIL "+s)
def require(ok,s):
    if not ok:fail(s)
def number(v):
    require(type(v) is str and re.fullmatch(r"-?\d+(?:/\d+|\.\d+)?",v)
            is not None,"numeric value must be rational string")
    return Q(v)
def vec(v,n=None):
    require(isinstance(v,list) and (n is None or len(v)==n),"vector shape")
    return tuple(map(number,v))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def K(w,x):
    return (w[0]*x[0]+w[1]*x[2]+w[2]*x[1],
            w[0]*x[1]+w[1]*x[0]+w[2]*x[2],
            w[0]*x[2]+w[1]*x[1]+w[2]*x[0])
def q(x):
    return sum((x[i]-x[(i+1)%3])**2 for i in range(3))/2
def qerr(x,eps):
    return sum(abs(x[i]-x[(i+1)%3])*(eps[i]+eps[(i+1)%3])
       +(eps[i]+eps[(i+1)%3])**2/2 for i in range(3))
def rotate(t,positive):
    return (t[1],t[2],t[0]) if positive else (t[2],t[0],t[1])

def certify(data):
    require(data.get("schema")=="x369_r4_source_relative_v1","schema")
    require(data.get("arm") in ("coherent","mixed"),"geometry")
    sha=data.get("checkpoint_sha256")
    require(isinstance(sha,str) and re.fullmatch("[0-9a-f]{64}",sha),
            "checkpoint SHA syntax")
    require(data.get("checkpoint_hash_externally_verified") is True,
            "external checkpoint bytes verification missing")
    require(data.get("source_export_verified") is True,
            "original source-export provenance missing")
    require(data.get("source_float_evaluation_error_receipt_verified") is True,
            "source floating error receipt missing")
    x=vec(data["x"]);d=len(x)
    require(d>=6 and d%3==0,"need at least two whole triads")
    histories=[vec(t,d) for t in data["histories"]]
    E=len(histories);require(E>=2,"at least two experts")
    v=vec(data["history_weight"],d)
    w=vec(data["directed_weight"],d)
    bias=vec(data["expert_bias"],E)
    er=data["errors"]
    ex=vec(er["x"],d)
    eh=[vec(z,d) for z in er["histories"]]
    ev=vec(er["history_weight"],d)
    ew=vec(er["directed_weight"],d)
    eb=vec(er["expert_bias"],E)
    ef=[vec(z,E) for z in er["differential_floating_eval"]]
    eq=vec(er["q_energy_eval"],d//3)
    require(len(eh)==E and len(ef)==E,"per-expert error shapes")
    require(all(t>=0 for group in (ex,ev,ew,eb,eq) for t in group),
            "negative errors")
    require(all(t>=0 for row in eh+ef for t in row),
            "negative history/float errors")
    require(all(ef[i][j]==ef[j][i] for i in range(E) for j in range(E)),
            "differential floating slack must be symmetric")
    base=data.get("base_mask")
    require(isinstance(base,list) and len(base)==d//3 and
            all(type(t) is bool for t in base),"mixed mask")
    qs=[q(x[j:j+3]) for j in range(0,d,3)]
    qb=[qerr(x[j:j+3],ex[j:j+3])+eq[j//3] for j in range(0,d,3)]
    mean=sum(qs)/len(qs)
    bits=[]
    for i in range(len(qs)):
        radius=((len(qs)-1)*qb[i]
          +sum(qb[j] for j in range(len(qs)) if j!=i))/len(qs)
        z=qs[i]-mean
        if data["arm"]=="mixed":
            if z-radius>0:flip=True
            elif z+radius<=0:flip=False
            else:fail("mixed q gate not certified")
            bits.append(bool(base[i])^flip)
        else:bits.append(True)
    phase=tuple(t for j,p in enumerate(bits)
        for t in rotate(x[3*j:3*j+3],p))
    pe=tuple(t for j,p in enumerate(bits)
        for t in rotate(ex[3*j:3*j+3],p))
    paths=(((0,0),(1,2),(2,1)),
           ((0,1),(1,0),(2,2)),
           ((0,2),(1,1),(2,0)))
    coeff=[];U=[]
    for j in range(0,d,3):
        coeff.extend(K(w[j:j+3],phase[j:j+3]))
        U.extend(sum(abs(w[j+i])*pe[j+k]
          +ew[j+i]*(abs(phase[j+k])+pe[j+k])
          for i,k in path) for path in paths)
    scores=[dot(v,[abs(t) for t in he])+dot(coeff,he)+bias[i]
             for i,he in enumerate(histories)]
    k=data.get("top_k")
    require(type(k) is int and 1<=k<=E,"topk")
    ids=sorted(range(E),key=lambda i:(-scores[i],i))[:k]
    require(data.get("source_selected_ids")==ids,
            "source ids disagree; float ordering or tie unresolved")
    def pair_budget(i,j):
        hi=histories[i];hj=histories[j]
        return (sum(U[l]*abs(hi[l]-hj[l])
          +(abs(coeff[l])+U[l])*(eh[i][l]+eh[j][l])
          for l in range(d))
          +sum(abs(v[l])*(eh[i][l]+eh[j][l])
            +ev[l]*(abs(abs(hi[l])-abs(hj[l]))
                +eh[i][l]+eh[j][l]) for l in range(d))
          +eb[i]+eb[j]+ef[i][j])
    for i in ids:
        for j in range(E):
            if j not in ids:
                require(scores[i]-scores[j]>pair_budget(i,j),
                        "cross-topk pair uncertified "+str((i,j)))
    for i,j in zip(ids,ids[1:]):
        require(scores[i]-scores[j]>pair_budget(i,j),
                "selected slots uncertified")
    ow=vec(data["orientation_weight"],2*d)
    eow=vec(er["orientation_weight"],2*d)
    eo=vec(er["orientation_float_eval"],E)
    require(all(t>=0 for t in eow+eo),"negative orientation error")
    for i in ids:
        z=x+histories[i];ez=ex+eh[i]
        orient=2*dot(z,ow)
        err=2*sum(abs(ow[j])*ez[j]
             +eow[j]*(abs(z[j])+ez[j]) for j in range(2*d))+eo[i]
        require(abs(orient)>err,
                "selected orientation chart uncertified "+str(i))
    selected_B=max((pair_budget(i,j)
        for i in ids for j in ids if i!=j),default=Q(0))
    return {
      "status":"CONDITIONALLY_CERTIFIED_RATIONAL_MODEL",
      "ordered_ids":ids,"q_mask":bits,
      "selected_softmax_L1_bound":str(selected_B/2),
      "source_checkpoint_authenticated_by_this_script":False,
      "float_errors_accepted_from_external_receipt":True,
      "full_recurrent_state_certified":False}

if __name__=="__main__":
    if len(sys.argv)!=2:
        raise SystemExit("usage: check_x369_r4_source_receipt.py receipt.json")
    try:
        with open(sys.argv[1],encoding="utf8") as stream:
            data=json.load(stream)
        print(json.dumps(certify(data),sort_keys=True))
    except (KeyError,ValueError,TypeError,ZeroDivisionError) as exc:
        raise SystemExit("X369_RECEIPT_FAIL "+str(exc))

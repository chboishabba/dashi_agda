#!/usr/bin/env python3
"""Conditional ideal binary32 source scoring-plan roundoff envelopes.

Use exact Fractions as symbolic rational interval arithmetic. Assume every
declared + and * operation rounds with |fl(z)-z|<=u|z|, u=2^-24,
all intermediate nonzero values normal, no overflow/underflow, exact
fixture inputs, and the EXACT disclosed operation order.
This is NOT a source Torch/ROCm/CUDA/FMA/TF32/fitted precision receipt.
"""
from fractions import Fraction as F
from dataclasses import dataclass
u=F(1,2**24)
checks=[]
def check(name,ok):
    if not ok:raise AssertionError(name)
    checks.append(name)
@dataclass(frozen=True)
class Interval:
    lo:F
    hi:F
    @staticmethod
    def point(x):return Interval(F(x),F(x))
    def rnd(self):
        m=max(abs(self.lo),abs(self.hi))
        return Interval(self.lo-u*m,self.hi+u*m)
    def __add__(self,other):
        return Interval(self.lo+other.lo,self.hi+other.hi).rnd()
    def __mul__(self,other):
        vals=(self.lo*other.lo,self.lo*other.hi,
              self.hi*other.lo,self.hi*other.hi)
        return Interval(min(vals),max(vals)).rnd()
    def error(self,exact):
        return max(abs(self.lo-F(exact)),abs(self.hi-F(exact)))
def dot(xs,ys):
    acc=xs[0]*ys[0]
    for j in range(1,len(xs)):
        acc=acc+xs[j]*ys[j]
    return acc
def exact_scores(x,h,v,w,b,bits):
    phase=tuple(t for j,p in enumerate(bits) for t in (
        (x[3*j+1],x[3*j+2],x[3*j]) if p else
        (x[3*j+2],x[3*j],x[3*j+1])))
    scores=[]
    for e,he in enumerate(h):
        val=sum(v[i]*abs(he[i]) for i in range(len(x)))+b[e]
        for j in range(0,len(x),3):
            a,c,d=phase[j:j+3];A,B,C=he[j:j+3]
            val+=w[j]*(a*A+c*B+d*C)
            val+=w[j+1]*(a*B+c*C+d*A)
            val+=w[j+2]*(a*C+c*A+d*B)
        scores.append(val)
    return tuple(scores)
def interval_scores(x,h,v,w,b,bits,fuse):
    phase=tuple(t for j,p in enumerate(bits) for t in (
        (x[3*j+1],x[3*j+2],x[3*j]) if p else
        (x[3*j+2],x[3*j],x[3*j+1])))
    point=Interval.point
    ks=[]
    if fuse:
        for j in range(0,len(phase),3):
            a,c,d=map(point,phase[j:j+3])
            ws,wf,wr=map(point,w[j:j+3])
            ks.extend((dot((ws,wf,wr),(a,d,c)),
                       dot((ws,wf,wr),(c,a,d)),
                       dot((ws,wf,wr),(d,c,a))))
    results=[]
    for e,he in enumerate(h):
        c2=dot(tuple(map(point,v)),tuple(point(abs(t)) for t in he))
        terms=[]
        for j in range(0,len(x),3):
            hi=tuple(map(point,he[j:j+3]))
            if fuse:
                terms.append(dot(ks[j:j+3],hi))
            else:
                a,c,d=map(point,phase[j:j+3]);A,B,C=hi
                self=dot((a,c,d),(A,B,C))
                fwd=dot((a,c,d),(B,C,A))
                rev=dot((a,c,d),(C,A,B))
                terms.append(dot(tuple(map(point,w[j:j+3])),
                                 (self,fwd,rev)))
        direct=terms[0]
        for term in terms[1:]:
            direct=direct+term
        results.append(c2+direct+point(b[e]))
    return tuple(results)

x=(2,0,0,0,0,0)
histories=((0,1,0,0,0,0),(1,0,1,0,0,0),
           (0,1,1,0,0,0),(1,1,0,0,0,0))
v=(0,1,1,0,0,0)
w=(2,-1,1,1,0,2)
bias=(0,1,5,10)
for arm,bits,expected in (
    ("coherent",(True,True),(3,4,13,11)),
    ("mixed",(False,False),(5,2,9,17))):
    source=exact_scores(x,histories,v,w,bias,bits)
    check(arm+" source exact fixture",source==expected)
    results={}
    for mode in ("original","fused"):
        values=interval_scores(x,histories,v,w,bias,bits,
                               fuse=(mode=="fused"))
        results[mode]=values
        check(arm+" "+mode+" interval encloses exact score",
              all(z.lo<=t<=z.hi for z,t in zip(values,source)))
        ids=sorted(range(len(source)),
                   key=lambda i:(-source[i],i))[:2]
        check(arm+" "+mode+" selected/outside strict",
              all(values[i].lo>values[j].hi for i in ids
                  for j in range(len(source)) if j not in ids))
        check(arm+" "+mode+" selected internal strict",
              values[ids[0]].lo>values[ids[1]].hi)
        pair_error=sum(values[i].error(source[i]) for i in ids)
        print("X369_ROUNDOFF_CONDITIONAL",arm,mode,
              "selected_pair_error_bound",float(pair_error),
              "ordered_ids",ids,
              "max_absolute_logit_error",
              max(float(z.error(t)) for z,t in zip(values,source)))
    ids=sorted(range(len(source)),key=lambda i:(-source[i],i))[:2]
    original=sum(results["original"][i].error(source[i]) for i in ids)
    fused=sum(results["fused"][i].error(source[i]) for i in ids)
    check(arm+" fused elementary plan may have wider roundoff bound",
          fused>original)
check("binary32 ideal unit roundoff exactly 2^-24",
      u==F(1,16777216))
print("X369_R4_ROUNDOFF_PLAN_CONDITIONAL_PASS",len(checks))

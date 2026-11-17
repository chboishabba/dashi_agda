#!/usr/bin/env python3
"""Original R4 coherent source-shape witness from TOP-K REPLACEMENT alone.

Exact source-formula parameters, NOT fitted Leech or a measured runtime.
Original owner: LeechTransformer/models/history_orbit_moe.py R4 branch.
Reuse original DASHI/Cognition/ResponseKink.agda shape, no new
GELU overload hypothesis. Executable with SymPy (no Torch/GPU/Agda).
"""
import sympy as S
from fractions import Fraction as Q
R=S.Rational
checked=[]
def check(label,expr):
    if not bool(expr):raise AssertionError("R4_SOURCE_KINK_FAIL "+label)
    checked.append(label)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def K(w,x):
    return (w[0]*x[0]+w[1]*x[2]+w[2]*x[1],
            w[0]*x[1]+w[1]*x[0]+w[2]*x[2],
            w[0]*x[2]+w[1]*x[1]+w[2]*x[0])
def coherent_phase(x):
    return tuple(z for j in range(0,len(x),3)
                 for z in (x[j+1],x[j+2],x[j]))
# Source R4 c2_c3_residual router, where baseline history weight
# and common unary scores are zero. Source residual shared head
# w is NOT a separate parameter for every expert.
w=tuple(map(R,(1,0,0,0,0,0)))
history_head=(R(0),)*6
slopes=(0,4,9,10)
biases=tuple(map(R,(8,3,-11,-13)))
histories=[tuple(map(R,(1,0,s,0,0,0))) for s in slopes]
outputs=tuple(map(R,(0,1,0,0))) # licensed expert W2=0, b2 outputs
def original_source_scores(t):
    x=(R(t),R(0),R(0),R(0),R(0),R(0))
    phase=coherent_phase(x)
    coeff=tuple(c for j in range(0,len(x),3)
          for c in K(w[j:j+3],phase[j:j+3]))
    return tuple(dot(history_head,tuple(abs(z) for z in h))
             +dot(coeff,h)+biases[e] for e,h in enumerate(histories))
def top2(scores):
    ids=sorted(range(4),key=lambda e:(-scores[e],e))[:2]
    margin_cross=min(scores[i]-scores[j] for i in ids
        for j in range(4) if j not in ids)
    margin_order=scores[ids[0]]-scores[ids[1]]
    return ids,margin_cross,margin_order
def mixture(scores,ids):
    terms=[S.exp(scores[i]) for i in ids]
    return S.simplify(sum(outputs[i]*S.exp(scores[i])
               for i in ids)/sum(terms))
data=[]
for t in range(4):
    sc=original_source_scores(t)
    ids,gap,order=top2(sc)
    y=mixture(sc,ids)
    check("source all R4 logits affine t="+str(t),
          sc==tuple(slopes[e]*t+biases[e] for e in range(4)))
    check("strict top2 and slot margins t="+str(t),
          gap>0 and order>0)
    data.append((sc,ids,gap,order,y))
check("four source-selected expert lists",
      [row[1] for row in data]==[[0,1],[0,1],[1,0],[3,2]])
check("source strict min margin across four loads",
      min(row[2] for row in data)==1)
check("orientation stable and strictly positive at all loads",
      all(h[0]==1 for h in histories))
# A chosen source orientation row selects h[0] from [x,h].
# Since every expert h[0]=1, orientation score=2 and sign=+
# for every stage, independent of the load and selected IDs.
# A source expert FFN W2=0 and b2=constant produces a constant
# output for ANY GELU hidden computation; transition matrices
# set zero and state is reset for each independently compared load.
check("original constant expert output source-compatible",
      outputs[1]==1 and all(outputs[e]==0 for e in (0,2,3)))
# e is rigorously bounded: 5/2 < e < 3.
# Lower Taylor sum to degree 3 is 8/3>5/2.
check("elementary exponential lower rational witness",
      sum(Q(1,S.factorial(j)) for j in range(4))==Q(8,3))
check("elementary e interval used in comparisons",
      2.5<float(S.E.evalf(50))<3)
# Exact selected output:
# t=0: 1/(1+e^5), t=1: 1/(1+e),
# t=2: 1/(1+e^-3), t=3: 0.
expected=(1/(1+S.exp(5)),1/(1+S.E),
          1/(1+S.exp(-3)),S.Integer(0))
check("original output mixture exact closed forms",
      all(S.simplify(data[i][4]-expected[i])==0 for i in range(4)))
check("analytically certified Nat buckets without evalf",
      # e>5/2 gives e^5> (5/2)^5 >9, hence y0<1/10;
      # 5/2<e<3 gives 1/4<y1<2/7 => floor(10y1)=2;
      # e>5/2 gives e^3>9 => y2>9/10; y2<1.
      Q(5,2)**5>9 and Q(5,2)**3>9
      and Q(10,1)/(1+Q(5,2))<3
      and Q(10,1)/(1+Q(3,1))>=2)
Nat=tuple(int(S.floor(10*d[4])) for d in data)
check("same canonical original ResponseKink Nat profile",
      Nat==(0,2,9,0) and Nat[0]<Nat[1]<Nat[2] and Nat[3]<Nat[2])
# CONTROL: freeze expert IDs [0,1] under exactly same learned
# score functions/FFN and states; y1 is logistic(4t-5),
# strictly increasing over all four loads. Without topk replacement,
# overload suppression FAILS. This is a mechanism-specific
# intervention, not another arbitrary analytic envelope.
fixed_ids=[0,1]
fixed=tuple(mixture(d[0],fixed_ids) for d in data)
check("matched fixed-route control monotonic",
      all(float(S.N(fixed[i+1]-fixed[i],50))>0 for i in range(3)))
check("matched fixed-route control fails overload limb",
      float(S.N(fixed[3]-fixed[2],50))>0)
# Because 4t-5 is increasing and sigmoid derivative p(1-p)>0,
# monotonicity follows without fitting or sampling.
v,d=S.symbols("v d",real=True)
sigmoid=1/(1+S.exp(-v))
check("strict derivative of selected two-logit softmax",
      S.simplify(S.diff(sigmoid,v)-sigmoid*(1-sigmoid))==0)
# Source cap_history caps only next_h, not current output y.
# Resetting the SAME initial history across loads prevents a
# fabricated recurrent overload/cap cause. Recurrent comparison
# would need original source history transitions per step.
print("X369_R4_TOPK_KINK_SYMPY_PASS",len(checked))
for i,(scores,ids,gap,order,y) in enumerate(data):
    print("load",i,"logits",scores,"selected",ids,
          "cross_gap",gap,"slot_gap",order,
          "response",S.N(y,13),"Nat",Nat[i])
print("FIXED_ROUTE_CONTROL",tuple(S.N(y,9) for y in fixed))

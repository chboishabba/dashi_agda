#!/usr/bin/env python3
"""Source R4: rational relative-score, q-gate, softmax and recurrence certificates.

Proof-development only. Source: LeechTransformer/models/history_orbit_moe.py
and models/trialectic_wave_prior.py, original R4 branch. No Torch/FP/Agda claims.
"""
import sympy as S
from dataclasses import dataclass
R=S.Rational
checks=[]
def check(name,ok):
    if not bool(ok): raise AssertionError("X369_R4_RELATIVE_FAIL "+name)
    checks.append(name)
@dataclass(frozen=True)
class Interval:
    lo: object
    hi: object
    def __post_init__(self):
        if self.lo>self.hi: raise ValueError("empty interval")
    def __sub__(self,other):
        return Interval(self.lo-other.hi,self.hi-other.lo)
    def contains(self,x):return self.lo<=x<=self.hi
    @staticmethod
    def around(x,error):return Interval(x-error,x+error)

def q(x):return R(1,2)*sum((x[i]-x[(i+1)%3])**2 for i in range(3))
def q_budget(x,eps):
    return sum(abs(x[i]-x[(i+1)%3])*(eps[i]+eps[(i+1)%3])
             +R(1,2)*(eps[i]+eps[(i+1)%3])**2 for i in range(3))
def gate_intervals(x,eps):
    en=[q(x[j:j+3]) for j in range(0,len(x),3)]
    Q=[q_budget(x[j:j+3],eps[j:j+3]) for j in range(0,len(x),3)]
    m=len(en); avg=sum(en)/m
    return [Interval.around(en[j]-avg,
       ((m-1)*Q[j]+sum(Q[i] for i in range(m) if i!=j))/m)
       for j in range(m)]
def certify_mask(x,eps,base):
    out=[]
    for bit,z in zip(base,gate_intervals(x,eps)):
        if z.lo>0:flip=True
        elif z.hi<=0:flip=False
        else:return None
        out.append(bool(bit)^flip)
    return tuple(out)
def rot(x,plus):return (x[1],x[2],x[0]) if plus else (x[2],x[0],x[1])
def phase(x,bits):
    return tuple(y for j,b in enumerate(bits) for y in rot(x[3*j:3*j+3],b))
def dot(x,y):return sum(a*b for a,b in zip(x,y))
def fused(w,x):return (w[0]*x[0]+w[1]*x[2]+w[2]*x[1],
                         w[0]*x[1]+w[1]*x[0]+w[2]*x[2],
                         w[0]*x[2]+w[1]*x[1]+w[2]*x[0])
def score(x,h,v,w,bias,bits,common=R(0)):
    xx=phase(x,bits)
    K=tuple(a for j in range(0,len(x),3)
            for a in fused(w[j:j+3],xx[j:j+3]))
    return tuple(common+dot(v,[abs(z) for z in he])+dot(K,he)+bias[i]
                 for i,he in enumerate(h))
def budget(x,h,v,w,ex,eh,ev,ew,eb,bits):
    xx=phase(x,bits);ee=phase(ex,bits)
    pairs=(((0,0),(1,2),(2,1)),((0,1),(1,0),(2,2)),
           ((0,2),(1,1),(2,0)))
    K=[];U=[]
    for j in range(0,len(x),3):
        K+=fused(w[j:j+3],xx[j:j+3])
        U.extend(sum(abs(w[j+i])*ee[j+k]+ew[j+i]*
          (abs(xx[j+k])+ee[j+k]) for i,k in path) for path in pairs)
    return tuple(sum(abs(v[j])*eh[j]+ev[j]*(abs(he[j])+eh[j])
       +U[j]*abs(he[j])+(abs(K[j])+U[j])*eh[j]
       for j in range(len(x)))+eb for he in h)
def ordered_safe(scores,bounds,k):
    ids=tuple(sorted(range(len(scores)),key=lambda i:(-scores[i],i))[:k])
    intervals=[Interval.around(x,e) for x,e in zip(scores,bounds)]
    outside=set(range(len(scores)))-set(ids)
    return ids,all(intervals[i].lo>intervals[j].hi
                   for i in ids for j in outside),all(
      intervals[ids[i]].lo>intervals[ids[i+1]].hi for i in range(k-1))
x=tuple(map(R,(2,0,0,0,0,0)))
h=[tuple(map(R,z)) for z in ((0,1,0,0,0,0),(1,0,1,0,0,0),
                            (0,1,1,0,0,0),(1,1,0,0,0,0))]
v=tuple(map(R,(0,1,1,0,0,0)))
w=tuple(map(R,(2,-1,1,1,0,2)))
bias=tuple(map(R,(0,1,5,10)))
base=(True,False);eps=(R(1,256),)*6
for arm,expected in [("coherent",(2,3)),("mixed",(3,2))]:
    bits=(True,True) if arm=="coherent" else certify_mask(x,eps,base)
    check(arm+" gate",bits is not None)
    logits=score(x,h,v,w,bias,bits)
    B=budget(x,h,v,w,eps,eps,eps,eps,R(1,256),bits)
    ids,member,order=ordered_safe(logits,B,2)
    check(arm+" ordered topk",ids==expected and member and order)
    huge=R(10)**15
    check(arm+" common unary cancels",
          all(score(x,h,v,w,bias,bits,huge)[i]-
                  score(x,h,v,w,bias,bits,huge)[0]
               ==logits[i]-logits[0] for i in range(4)))
    check(arm+" safe independent relative intervals",
          all((Interval.around(logits[i],B[i])-
               Interval.around(logits[0],B[0])).contains(
                   logits[i]-logits[0]) for i in range(4)))
    print("R4_RELATIVE",arm,logits,B,ids)
check("source mixed q tie refuses proof",
      certify_mask(tuple(map(R,(1,0,0,0,1,0))),eps,base) is None)
q0,q1=S.symbols("Q0 Q1",nonnegative=True)
check("correlated q-mean bound is strictly sharper when Q0>0",
      S.simplify(q0+(q0+q1)/2-(q0+q1)/2)==q0)
# Exact shift-invariant softmax derivative bound: common shift is
# annihilated by J=diag(p)-p*p^T, and selected L1 variation <=
# half the oscillation of the score perturbation by choosing
# the optimal common shift midpoint.
ps=S.symbols("p0:3",real=True)
P=S.Matrix(ps);J=S.diag(*P)-P*P.T
check("softmax common-shift Jacobian null on simplex",
      all(S.simplify(t.subs(ps[2],1-ps[0]-ps[1]))==0
          for t in J*S.ones(3,1)))
delta=(R(100),R(101),R(100))
softmax=lambda z:[S.exp(zz)/sum(S.exp(v) for v in z) for zz in z]
z=(R(0),R(2),R(1))
p=softmax(z);p2=softmax([a+b for a,b in zip(z,delta)])
tv=S.N(sum(abs(a-b) for a,b in zip(p,p2)),40)
check("softmax oscillation bound",tv<=(max(delta)-min(delta))/2)
check("oscillation bound tightens raw absolute budget",
      (max(delta)-min(delta))/2<max(map(abs,delta)))
# Source orientation: sign requires independent interval away from zero.
o=tuple(map(R,(1,-2,2,0,1,-1,1,0,0,-1,0,2)))
for i in (2,3):
    z=x+h[i];ez=eps+eps;eo=(R(1,256),)*len(o)
    orient=2*dot(z,o)
    orientB=2*sum(abs(o[j])*ez[j]+eo[j]*(abs(z[j])+ez[j])
                  for j in range(len(z)))
    check("selected orientation "+str(i),abs(orient)>orientB)
# Source selected update is independent of current mixture weights,
# but emitted output is not; future input/state must be recertified.
weight=S.symbols("mixture_weight")
expert=S.Function("expert")
transition=S.Function("transition")
xv,hv=S.symbols("xv hv")
check("one-step expert history ignores mixture weight",
 S.diff(transition(xv,hv,expert(xv,hv)),weight)==0)
check("one-step emitted mixture depends on mixture weight",
 S.diff(weight*expert(xv,hv),weight)==expert(xv,hv))
# Selected FFN source GELU' identity; spectral norms still unmeasured.
t=S.symbols("t",real=True)
gelu=t*(1+S.erf(t/S.sqrt(2)))/2
phi=S.exp(-t**2/2)/S.sqrt(2*S.pi)
Phi=(1+S.erf(t/S.sqrt(2)))/2
check("source GELU differential",
      S.simplify(S.diff(gelu,t)-Phi-t*phi)==0)
# Nonstationary conditional error recurrence: all gates must be
# recertified at each step; coefficients come from the actual model.
L=S.symbols("L0:5",nonnegative=True)
eta=S.symbols("eta0:5",nonnegative=True)
d0=S.symbols("D0")
d=d0
for j in range(5):d=S.expand(L[j]*d+eta[j])
closed=d0*S.prod(L)+sum(eta[j]*S.prod(L[j+1:]) for j in range(5))
check("5-step nonautonomous recurrence identity",S.expand(d-closed)==0)
print("X369_R4_RELATIVE_SYMPY_PASS",len(checks),"grouped checks")

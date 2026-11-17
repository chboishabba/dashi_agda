#!/usr/bin/env python3
"""Exact SymPy source theorem: rank of original shared directed router head.

This addresses history sufficiency for ALL possible future activations,
not only one selected packet. Original owner: LeechTransformer
models/trialectic_wave_prior.py directed_trialectic_invariants and
models/history_orbit_moe.py shared learned residual head.
No claimed fitted checkpoint, Agda run, or physical precision result.
"""
import sympy as S
ws,wf,wr=S.symbols("ws wf wr",real=True)
M=S.Matrix([[ws,wr,wf],[wf,ws,wr],[wr,wf,ws]])
DC=ws+wf+wr
q=ws**2+wf**2+wr**2-ws*wf-wf*wr-wr*ws
checks=[]
def check(label,ok):
    if not bool(ok):raise AssertionError("X369_CIRCULANT_FAIL "+label)
    checks.append(label)
check("exact original circulant determinant",S.expand(M.det()-DC*q)==0)
project=S.ones(3,3)/3
check("exact DC/rotating Gram spectral decomposition",
      all(S.expand(t)==0 for t in
          (M.T*M-(q*S.eye(3)+(DC**2-q)*project))))
z=S.symbols("lambda")
check("squared singular-value characteristic polynomial",
      S.expand((M.T*M).charpoly(z).as_expr()
               -(z-DC**2)*(z-q)**2)==0)
x=S.Matrix(S.symbols("x0:3",real=True))
h=S.Matrix(S.symbols("h0:3",real=True))
a,b,c=x
A,B,C=h
source=(ws*(a*A+b*B+c*C)+wf*(a*B+b*C+c*A)
        +wr*(a*C+b*A+c*B))
check("source T linear score equals x^T M^T h",
      S.expand(source-(M*x).dot(h))==0)
check("for all x, observable history is M^T h",
      all(S.expand(t)==0 for t in
          M.T*h-S.Matrix([S.diff(source,t) for t in x])))
check("zero-sum source head DC history null",
      M.subs(wr,-ws-wf).T*S.ones(3,1)==S.zeros(3,1))
check("nonzero zero-sum symbolic head generically rank two",
      M.subs(wr,-ws-wf).rank()==2)
check("equal original directed head weights rank one",
      M.subs({wf:ws,wr:ws}).rank()==1)
check("zero directed head rank zero",
      M.subs({ws:0,wf:0,wr:0}).rank()==0)
check("generic rational source head full rank",
      M.subs({ws:2,wf:-1,wr:1}).rank()==3)
# In the weight-sum-zero case the directed score sees only
# h's rotating-plane projection; the original source C2 abs(h)
# baseline can STILL distinguish histories differing by DC.
Mzero=M.subs({ws:2,wf:-1,wr:-1})
ha=S.Matrix((0,0,0));hb=S.Matrix((1,1,1))
check("directed head cannot observe a DC history shift",
      Mzero.T*(hb-ha)==S.zeros(3,1))
check("original nonzero C2 absolute-history head restores distinction",
      sum(abs(t) for t in hb)!=sum(abs(t) for t in ha))
check("zero-sum source head factors through rotating-plane projection",
      M.subs(wr,-ws-wf).T*(S.eye(3)-project)
      ==M.subs(wr,-ws-wf).T)
# Even where a CURRENT score projection forgets DC, future transition
# may retain it; identity transition is an explicit semantic control.
check("future identity history transition can distinguish dropped DC",
      S.eye(3)*hb!=S.eye(3)*ha)
# Original q-gated mixed arm is a BIJECTION of the full activation
# carrier in exact arithmetic: q is cyclic/sign invariant and the
# sample-mean gate is unchanged by independent per-triad C3 rotations.
# Hence the score observability no-go is not escaped by the q gate.
aa,bb,cc=S.symbols("aa bb cc",real=True)
def q3(t):
    u,v,w=t
    return u*u+v*v+w*w-u*v-v*w-w*u
def plus(t):return (t[1],t[2],t[0])
def minus(t):return (t[2],t[0],t[1])
check("original q invariant under +120",
      S.expand(q3((aa,bb,cc))-q3(plus((aa,bb,cc))))==0)
check("original q invariant under -120",
      S.expand(q3((aa,bb,cc))-q3(minus((aa,bb,cc))))==0)
check("original q invariant under C2 sign",
      S.expand(q3((aa,bb,cc))-q3((-aa,-bb,-cc)))==0)
def gate_fn(triads,base):
    energies=[q3(t) for t in triads]
    avg=sum(energies)/len(energies)
    return tuple(bool(k)^bool(e>avg) for k,e in zip(base,energies))
def F(triads,base):
    bits=gate_fn(triads,base)
    return tuple(plus(t) if bit else minus(t)
                 for t,bit in zip(triads,bits))
def Finverse(triads,base):
    bits=gate_fn(triads,base)
    return tuple(minus(t) if bit else plus(t)
                 for t,bit in zip(triads,bits))
original=((S.Integer(2),S.Integer(0),S.Integer(0)),
          (S.Integer(0),S.Integer(1),S.Integer(0)))
base=(True,False)
check("q gate phase is invariant along its own orbit",
      gate_fn(original,base)==gate_fn(F(original,base),base))
check("exact q-gated phase has explicit inverse on rational fixture",
      Finverse(F(original,base),base)==original)
check("q-gated map commutes with diagonal C3 action on fixture",
      F(tuple(plus(t) for t in original),base)
      ==tuple(plus(t) for t in F(original,base)))
# Stronger ALL-ROUTER counterexample at a rank-two zero-sum head.
# Even joining the C2 abs(history) route with directed T need not
# restore the lost DC sign: h=+t*(1,1,1) vs -t*(1,1,1).
# For EVERY x, directed-score difference is zero and |h| agrees
# coordinatewise. Nevertheless the source expert FFN or orientation
# transition can still inspect signed h, so future-sufficiency fails.
tp=S.symbols("t",positive=True)
Hp=tp*S.ones(3,1);Hm=-tp*S.ones(3,1)
v0,v1,v2=S.symbols("v0 v1 v2",real=True)
vv=S.Matrix((v0,v1,v2))
R2=M.subs(wr,-ws-wf)
check("full C2 plus rank2 directed score cannot recover DC sign",
      R2.T*(Hp-Hm)==S.zeros(3,1)
      and all(S.Abs(Hp[i])==S.Abs(Hm[i]) for i in range(3)))
check("original signed expert history still distinguishes routing fibre",
      Hp!=Hm)
print("X369_CIRCULANT_SUFFICIENCY_SYMPY_PASS",len(checks),"checks")

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
print("X369_CIRCULANT_SUFFICIENCY_SYMPY_PASS",len(checks),"checks")

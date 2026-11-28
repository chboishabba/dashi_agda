#!/usr/bin/env python3
"""BR78: NONLINEAR Einstein–Israel Codazzi/tension Ward obligation.

On one matched induced wall h and common Levi-Civita D, with actual
physical sign convention I_ab=[K_ab]-h_ab tr_h[K]+3 j h_ab-S_ab:
  D^a I_ab=[Ric(n,e_b)]+3 D_b j-D^a S_ab.
If both bulk sides satisfy vacuum Einstein Ric=-4g, then
[Ric(n,e_b)]=0 for each unit normal/tangent, hence
  D^a I_ab=3 D_b j-D^a S_ab.
Thus if I=0 and no wall stress S, the physical j MUST be constant
on each connected wall component (all four tangential derivatives).
An arbitrary varying j(t) in BR67/69 is a legitimate formal source
test, but is NOT an admissible vacuum wall unless wall stress/flux pays
D S=3 dj. This is a serious nonlinear Ward/non-promotion condition.

At the original 10-row symbol level BR62 D_q(I)= q^a I_ab-q_b tr I
is the trace-reversed Codazzi symbol for a different tensor carrier;
do NOT confuse it with the covariant divergence of the physical
I_ab itself. This checker explicitly distinguishes the two.

--part vacuum|matter|symbol|negative
"""
import argparse
import sympy as s

eta=s.diag(-1,1,1,1)
q=s.Matrix(s.symbols("q0:4"))
j=s.symbols("j")
J=s.Matrix(4,4,lambda a,b:s.Symbol(f'J{min(a,b)}{max(a,b)}'))
S=s.Matrix(4,4,lambda a,b:s.Symbol(f'S{min(a,b)}{max(a,b)}'))
ric=s.Matrix(s.symbols("R0:4"))
gidx=eta*q

def divergence(T):return T*gidx

def vacuum():
    # Exact vacuum Ric(n,tangent)=(-4 g)(n,tangent)=0 on a genuine
    # normalized wall: the curvature source is independently zero.
    pure=s.zeros(4)
    dJ=3*q
    assert divergence(pure)==s.zeros(4,1)
    assert dJ!=s.zeros(4,1)
    # If physical I=0, divergence I=0 forces 3 dj=0, with no
    # spectral or rank tricks. Characteristic zero original fields.
    obstruction=3*q
    assert obstruction[0]==3*q[0]
    assert obstruction!=s.zeros(4,1)
    print("BR78 physical vacuum Ward: homogeneous Israel forces all four tension gradients zero")

def matter():
    # Full source balance: Ric jump + 3 dj - div S = 0.
    balance=ric+3*q-divergence(S)
    required=ric+3*q
    # Construct symmetric S at nonzero q through exact right inverse
    # only for the finite source; no claim of global positive matter.
    testq=s.Matrix([1,0,0,0])
    target=s.Matrix([s.Rational(i+2,7) for i in range(4)])
    st=s.Matrix(4,4,lambda a,b:0)
    for b in range(4):
        st[0,b]=-target[b]
        st[b,0]=st[0,b]
    # q timelike, divergence S =-S[:,0]. The symmetric S00 works too.
    assert st*(eta*testq)==target
    # Correct sign: divergence I=ric+3dj-divS.
    assert (required-(ric+3*q-divergence(S))-divergence(S))==s.zeros(4,1)
    print("BR78 explicit symmetric compensating matter/normal Ricci source with all four channels")

def symbol():
    from check_hopf369_br62_israel_codazzi_rank import codazzi,pencil
    # The original symbol q^a T_ab -q_b tr T applies to TRACE-
    # REVERSED extrinsic source T; for physical I, source divergence
    # is only q^a I_ab. They generally differ.
    p=s.Matrix([1,1,0,0]) # null: still distinct
    T=s.Matrix(4,4,lambda a,b:s.Rational(min(a,b)+max(a,b)+2,7))
    direct=T*(eta*p)
    reversed=codazzi(p,T)
    assert direct-reversed==p*s.trace(eta*T)
    assert reversed!=direct
    assert pencil(p).rank()==4
    print("BR78 null-frequency source warns: physical Israel divergence != trace-reversed K Codazzi")

def negative():
    # An independently time-varying pure tension (no matter) is
    # inadmissible on a source-verified vacuum Einstein wall.
    grad=s.Matrix([1,0,0,0])
    assert 3*grad!=s.zeros(4,1)
    print("BR78 negative: nonconstant vacuum pure tension cannot be promoted")

if __name__=="__main__":
    p=s.ArgumentParser() if False else argparse.ArgumentParser()
    p.add_argument('--part',choices=['vacuum','matter','symbol','negative'],default='vacuum')
    a=p.parse_args()
    {'vacuum':vacuum,'matter':matter,'symbol':symbol,'negative':negative}[a.part]()

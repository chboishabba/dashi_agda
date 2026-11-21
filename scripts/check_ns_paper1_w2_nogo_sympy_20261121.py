#!/usr/bin/env python3
"""Paper 1 original B-lane arithmetic / status regression (SymPy 1.14).

Verifies exact R850/R853 3-4-5 rate, R820/R823/R824/R825 same-packet
algebra, the R854 original strict-short-time rational bound, and the
falsification logic. This DOES NOT build a complete real Galerkin flow,
prove an original Agda source identity, execute CI, or prove NS regularity.
Those producers remain the original C1/C2/B1 owners.
"""
import sys
from pathlib import Path
import sympy as S

def run(paper=None):
    q = S.Rational
    C, P, d = -q(557627,125), S.Integer(0), S.Integer(15834)
    r0=S.expand(6*(12*C-P+d))
    assert r0 == -q(28273644,125)
    N, Q, D, H, Lw, diss = S.symbols("N Q D H Lw diss",real=True)
    r820=2*(9*N-Q)+D+6*diss
    r823=D+6*diss-2*(Q-9*N)
    r825=6*diss+(H+18*N)-(Lw+2*Q)
    assert S.expand(r820-r823)==0
    assert S.expand(r825-r820.subs(D,H-Lw))==0
    # Independent negative controls for the exact original sign ledger.
    assert S.expand(r820-(D+6*diss)) == 2*(9*N-Q)
    assert S.expand(r820.subs({N:0,Q:1,D:0,diss:0}))<0
    assert S.expand(r820.subs({N:0,Q:0,D:0,diss:1}))>0

    T=q(226189,3938540454339300631433585885184)
    K=S.Integer(5032512)
    Lambda=S.Integer(618365778064115445891072)
    L=S.Integer(391309593930357307785216)
    # Physical real-ODE C1/C2 owner supplies K,Lambda and continuation;
    # the following is only its EXACT rational envelope arithmetic.
    assert K*T < 6
    upper=r0+Lambda*K*T
    assert upper < -q(19,125)
    assert r0+L*T == -q(284574877153831,1258128000)
    assert (r0*T+Lambda*K*T*T/2) < -q(19,125)*T
    # Continuity/derivative hypothesis is essential: a value at t=0
    # alone says nothing about the integral. This is a countercontrol.
    assert r0<0 and S.integrate(S.Integer(1),(S.Symbol("t"),0,T))>0
    # The no-go is for ORIGINAL R734/R735 and R820/R823/R825 payment.
    # R751/R752 selected G is NOT identified with that rate by this script.
    if paper is not None:
        s=Path(paper).read_text(encoding="utf-8")
        assert s.count("## Abstract")==1
        for needle in (
            "unrestricted universal positive W2 auxiliary premise is",
            "R734/R735", "R820/R823/R825", "R751/R752",
            "identity of the two signed observables",
            "not a viable universal premise",
            "Lane A", "Lanes C/D",
        ):
            assert needle.lower() in s.lower(), needle
    print("PASS R850/R853 exact selected r0 = -28273644/125")
    print("PASS R820=R823=R824/825 graded same-packet source algebra")
    print("PASS original R854 rational short-time negativity envelope")
    print("PASS opposite-sign and continuity negative controls")
    print("BOUNDARY: original source owner supplies physical ODE and rate transport")
    print("BOUNDARY: no R751/R752 source identity, no global NS regularity claim")
if __name__=="__main__":
    run(sys.argv[1] if len(sys.argv)>1 else None)

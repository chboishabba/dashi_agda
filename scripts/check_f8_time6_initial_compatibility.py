"""F8 initial characteristic high-time compatibility from flat original pulse.

On original zero initial data all derivatives of compact bump vanish at t=1.
Smooth first-order characteristic Y'=M(t)Y+f(t) then has zero initial
time jets Y1..Y7. This is conditional on smooth IBVP admissibility and
does not establish global source/energy estimates.
"""
from math import comb
import sympy as s


def initial_jets(Y0,M,F,order=7):
    if len(M)<order or len(F)<order:
        raise ValueError('operator/source differentiated jets required')
    jets=[Y0]
    for r in range(order):
        jets.append(sum(comb(r,j)*M[j]*jets[r-j] for j in range(r+1))+F[r])
    return jets


def exact():
    M=list(s.symbols('M0:7',real=True))
    F=[s.S.Zero]*7
    assert initial_jets(s.S.Zero,M,F)==[s.S.Zero]*8
    for k in range(7):
        pert=F[:];pert[k]=s.Integer(1)
        out=initial_jets(s.S.Zero,M,pert)
        assert all(out[j]==0 for j in range(k+1))
        assert out[k+1]==1
    X=s.symbols('X',positive=True)
    for p in range(8):
        assert s.limit(X**p*s.exp(1-X),X,s.oo)==0
    print('PASS original homogeneous characteristic initial time jets 0..7, flat pulse and nonflat negative controls')

if __name__=='__main__':exact()

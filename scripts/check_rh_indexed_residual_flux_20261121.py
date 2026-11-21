#!/usr/bin/env python3
"""Exact finite residual-flux accounting test; not Lean/Agda kernel or RH."""
from itertools import product
from dataclasses import dataclass

@dataclass(frozen=True)
class Frame:
    k: int
    mode: str
    sign: int
    residual: int
    zero: bool

INVERSE = {'zero':'zero','one':'one','zeta':'zeta2','zeta2':'zeta'}

def reflect(x):
    return Frame(x.k,INVERSE[x.mode],x.sign,x.residual,x.zero)

def flux(d,x):
    return Frame(x.k+1,x.mode,x.sign,x.residual+d,x.zero)

def run():
    n=0
    for k,mode,sgn,r,z,a,b in product(
        range(4),INVERSE,(-1,1),(0,3,9),(False,True),(0,2,5),(0,1,4)):
        x=Frame(k,mode,sgn,r,z)
        assert flux(a,reflect(x))==reflect(flux(a,x))
        assert flux(b,flux(a,reflect(x)))==reflect(flux(b,flux(a,x)))
        assert flux(b,flux(a,x)).residual==(r+a)+b
        assert flux(a,x).mode==x.mode
        assert flux(a,x).sign==sgn
        assert flux(a,x).zero==z
        assert flux(a,x).k==k+1
        n+=1
    assert flux(4,Frame(3,'zeta',1,9,True)).residual==13
    # An unchanged-residual step cannot satisfy a nonzero source-flux ledger.
    assert flux(4,Frame(3,'zeta',1,9,True)).residual != 9
    print(f'PASS {n}/{n} indexed flux-reflection, order and residual checks')
    print('PASS nonzero residual contribution retained; no cancelled source')
    print('NOT TESTED: original automorphic IsLift, analytic zeta, Agda kernel')

if __name__=='__main__':
    run()

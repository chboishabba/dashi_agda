"""Smoothing-first history return certificate.
Bounds are conditional on independently verified coefficient and integration
enclosures. Uses the max norm on current state and continuous ratio history.
"""
import sympy as S
from solar_steelman_history_enclosure import rat,interpolation

def bounds(a,b,c,r,rprime,T,delay):
    a,b,c,r,rprime,T,delay=map(rat,(a,b,c,r,rprime,T,delay))
    if delay==0 or T<=2*delay:raise ValueError("return must exceed history window")
    # x' = A x + B h(t-tau) + C h(t-2tau), h=R x after zero.
    # For unit initial section, sup ||x|| <= exp(kT) via Gronwall.
    k=a+(b+c)*max(1,r)
    G=S.exp(k*T)
    H=max(1,r)*G
    D=a*G+(b+c)*H
    L=rprime*G+r*D
    return dict(amplification=G,ratio_amplification=H,derivative=D,returned_lipschitz=L)

def contraction(section_power,section_norm,return_norm,output_error,step_error,p):
    """Bound T^(p+1), without approximating arbitrary initial histories.
    P=piecewise linear interpolation (norm <=1 including compatible endpoint
    in the augmented norm), A=P T restricted to ran P.
    Initial first return T maps into smooth histories; ||(I-P)T||<=e.
    For later iterations error recurrence E_{j+1}<=g E_j+e a^j g.
    Numerical section error supplied separately as uniform operator bound.
    """
    q,a,g,e,u=map(rat,(section_power,section_norm,return_norm,output_error,step_error))
    if not isinstance(p,int) or p<1:raise ValueError("positive integer power")
    # Compare T^(p+1) with A^p P T, using true T on initial histories.
    # E0 <= e. For approximate section A, ||T v-A v|| <= e+u.
    err=g**p*e+(e+u)*g*sum(g**(p-1-j)*a**j for j in range(p))
    cap=q*g+err
    return dict(bound=cap,contracting=bool(cap<1),margin=1-cap)

def fixture():
    z=bounds(0,0,0,1,0,3,1)
    assert z['amplification']==1 and z['returned_lipschitz']==0
    q=S.Rational(1,10)
    assert contraction(q,1,1,0,0,2)['bound']==q
    assert contraction(q,1,1,q,q,2)['bound']==S.Rational(3,5)
    assert not contraction(1,1,1,0,0,1)['contracting']
    print("PASS smoothing-first contraction arithmetic; actual bounds not supplied")

if __name__=="__main__":fixture()

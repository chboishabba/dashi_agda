#!/usr/bin/env python3
"""BR69: all orders zero-eight PHYSICAL gauge/mean source on existing towers.

Original BR68 physical (nonzero mean) corrections:
  ΔCodazzi_a=-2 M_a^b(c+_b-c-_b)-(j/2)(c+_a+c-_a)
  ΔMean = -4 m(ell+ +ell-).
Use independent symmetric M_ab(t), j(t), m(t), c±(t) and ell±(t)
as divided Taylor jets. No freeze of M_t, j_t, m_t or their cross terms.
The source is compared to independently differentiated SymPy
polynomials, through all 9 coefficients in each 4+1 physical suffix.
The D/E original prefixes remain DISTINCT and are not altered.

This concerns reference coordinate Codazzi and nonzero-mean force;
BR19/31 nonlinear material shape variation/induced geometry and
BR37 variable-boundary estimate still remain separate.
"""
import argparse
from fractions import Fraction as F
import sympy as s
from check_hopf369_br52_all_order_material_flux import ORDER,trim,mul,add,sub,scale
from check_hopf369_br_warped_physical_attachment import E4

def jet(seed):
    return trim([F(((seed+2)*(i+3)+i*i)%47-23,13+seed+i) for i in range(ORDER+1)])
def conv(*arr):
    out=arr[0]
    for v in arr[1:]:out=mul(out,v)
    return out
def sym2(a,b):
    return jet(1+min(a,b)*4+max(a,b))
def to_pol(a,t):
    return sum(s.Rational(x.numerator,x.denominator)*t**i for i,x in enumerate(a))
def exact(a,b):
    return all(x==y for x,y in zip(a,b))

def physical():
    j=jet(17);mean=jet(18)
    plus=[jet(20+i) for i in range(4)]
    minus=[jet(30+i) for i in range(4)]
    M=[[sym2(a,b) for b in range(4)] for a in range(4)]
    ellp,ellm=jet(39),jet(40)
    result=[]
    for a in range(4):
        p=trim([])
        for b in range(4):
            term=scale(-2*E4[b,b],conv(M[a][b],sub(plus[b],minus[b])))
            p=add(p,term)
        p=sub(p,scale(F(1,2),conv(j,add(plus[a],minus[a]))))
        result.append(p)
    meanresult=scale(-4,conv(mean,add(ellp,ellm)))
    t=s.symbols('t')
    jm=to_pol(j,t); mm=to_pol(mean,t)
    P=[to_pol(v,t) for v in plus];N=[to_pol(v,t) for v in minus]
    MM=s.Matrix(4,4,lambda a,b:to_pol(M[a][b],t))
    reference=s.Matrix([0]*4)
    independent=-2*MM*E4*(s.Matrix(P)-s.Matrix(N))-jm*(s.Matrix(P)+s.Matrix(N))/2
    independentMean=-4*mm*(to_pol(ellp,t)+to_pol(ellm,t))
    for n in range(ORDER+1):
        assert all(s.expand(independent[a]).coeff(t,n)==s.Rational(
            result[a][n].numerator,result[a][n].denominator)
            for a in range(4))
        assert s.expand(independentMean).coeff(t,n)==s.Rational(
            meanresult[n].numerator,meanresult[n].denominator)
    # Negative controls for ignoring source background derivatives:
    frozen=-2*s.Matrix([[MM[a,b].subs(t,0) for b in range(4)] for a in range(4)])*E4*(
        s.Matrix(P)-s.Matrix(N))-jm.subs(t,0)*(s.Matrix(P)+s.Matrix(N))/2
    assert any(s.expand(independent[a]-frozen[a])!=0 for a in range(4))
    assert meanresult[8]!=0 and any(result[a][8]!=0 for a in range(4))
    print("BR69 constructed all nine orders of physical four-Codazzi plus mean source")
    print("BR69 preserves independent M,j,m,c+,c-,ell+,ell- divided jets")

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['all'],default='all');p.parse_args()
    physical()

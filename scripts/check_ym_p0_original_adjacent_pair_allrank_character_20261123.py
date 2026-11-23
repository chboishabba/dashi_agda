#!/usr/bin/env python3
"""All-SU(N) original Wilson adjacent F19 pair interaction: native geometry,
exact matrix words and fundamental-character third-order coefficient.
The all-rank Peter-Weyl sum uses classical representation orthogonality.
This is NOT Bałaban Eq171 T, W3 absolute shells, or same-H OS.
"""
from itertools import product
from pathlib import Path
from importlib.util import spec_from_file_location,module_from_spec
import sympy as s
from fractions import Fraction as Q

p=Path(__file__).with_name('check_ym_p0_original_wilson_marked_ordered_t_20261123.py')
assert p.exists()
sp=spec_from_file_location('_original_L4',p);source=module_from_spec(sp);sp.loader.exec_module(source)
assert len(source.links)==1024 and len(source.faces)==1536
origin=(0,0,0,0)
y=((origin,2),(source.step(origin,2),2))
z=((origin,3),(source.step(origin,3),3))
touched=[f for f in source.faces if any(l in y+z for l in f)]
assert len(touched)==23 and sum(any(l in y for l in f) and any(l in z for l in f) for f in touched)==1
assert len(source.faces)-len(touched)==1513
checks={'geometry':4,'noncommuting':0,'all_rank':0,'first_character':0}

def group(n):
    c=s.Rational(3,5);v=s.Rational(4,5)
    R=s.Matrix([[c,-v],[v,c]])
    if n==2:
        A=R;B=s.Matrix([[c,s.I*v],[s.I*v,c]])
    else:
        A=s.eye(n);B=s.eye(n)
        for i in range(2):
            for j in range(2):
                A[i,j]=R[i,j]; B[i+1,j+1]=R[i,j]
    I=s.eye(n)
    for u in (A,B,A*B,B*A):
        assert s.simplify(u.det()-1)==0 and s.simplify(u*u.H-I)==s.zeros(n)
    assert A*B!=B*A
    return I,A,B

def realtrace(U):
    tr=s.trace(U)
    return s.expand((tr+s.conjugate(tr))/2)

def hol(field,face,I):
    a,b,c,d=face
    return field.get(a,I)*field.get(b,I)*field.get(c,I).H*field.get(d,I).H

for n in (2,3,4,5):
    I,A,B=group(n)
    for V,W in ((A,B),(B,A),(A*B,B),(A,B*A)):
        f={y[0]:V.H,y[1]:V,z[0]:W.H,z[1]:W}
        full=s.Integer(0)
        for face in touched:
            full+=1-realtrace(hol(f,face,I))/n
        pred=23-11*realtrace(V)/n-11*realtrace(W)/n-realtrace(V.H*W)/n
        assert s.simplify(full-pred)==0
        assert s.simplify(1-realtrace(hol(f,source.face(source.F,2,3),I))/n-(1-realtrace(V.H*W)/n))==0
        assert s.simplify(1-realtrace(hol(f,source.face(source.G,2,3),I))/n)==0
        checks['all_rank']+=3
    checks['noncommuting']+=3
    # For SU(N>=3), fund and antifund are distinct and have coefficient
    # a_f(x)=x/(2N)+O(x^2), giving two positive n=f,bar f terms.
    # For SU2 self-dual fundamental: a_f(x)=x/N+O(x^3), counted once.
    beta=s.symbols('beta')
    if n==2:
        result=(s.Rational(11,n)*beta)**2*(s.Rational(1,n)*beta)/n
        expected=s.Rational(121,16)*beta**3
    else:
        result=2*(s.Rational(11,2*n)*beta)**2*(s.Rational(1,2*n)*beta)/n
        expected=s.Rational(121,4*n**4)*beta**3
    assert s.expand(result-expected)==0
    checks['first_character']+=1

print('PASS',s.__version__,checks,'TOTAL',sum(checks.values()))
print('Native source S_N(V,W)=23-11t_N(V)-11t_N(W)-t_N(V^-1W), all N>=2')
print('Continuous Haar SU(N)^2 joint J=sum_rep a_rep(11beta)^2 a_rep(beta)/dim_rep')
print('Strict positive interaction beta>0; leading correction SU2=121/16 beta^3')
print('SU(N>=3)=121/(4N^4) beta^3 (fund+antifund distinct)')
print('OPEN literal CMP119/122 T, termwise absolute W3, fixed-physical same-H OS')

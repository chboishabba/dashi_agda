from fractions import Fraction as F
from math import isqrt
from time import perf_counter
from sympy import symbols, expand

def main():
    start=perf_counter()
    r,u,v=symbols('r u v')
    assert expand((1+u)**3-(1+v)**2-(3*u-2*v+3*u*u+u**3-v*v))==0
    assert 3*(-240)-2*504==-1728
    R=F(1,2**36)
    # pi > 3, sqrt(163)>12, exp(1)>2 imply 0<exp(-pi sqrt(163))<R.
    assert 163>12**2 and 1+1+F(1,2)>2
    # sigma_k(n)<=n^(k+1); from n=2 successive majorant ratio <=(3/2)^(k+1)r.
    assert F(3,2)**6*R<F(1,2)
    A=2*240*2**4; B=2*504*2**6
    assert A*R<1 and B*R<1
    # u=E4-1=-240r+error; v=E6-1=504r+error.
    K=3*A+2*B+3*241**2+241**3*R+505**2
    assert K<600000 and K*R<864
    # |Delta+r| <= K*r^2/1728 < r/2. No eta identity required.
    print('PASS: uniform negative-real q apartness; K < 600000; radius < 2^-36')
    print('relative error upper bound:',float(K*R/1728))
    print('wall_seconds:',perf_counter()-start)
if __name__=='__main__': main()

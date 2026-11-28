#!/usr/bin/env python3
"""BR202 actual frozen physical/subsidiary spectral projector.
No curved boundary or nonlinear promotion."""
import sympy as s
from check_hopf369_br_curvature_energy import carrier
from check_hopf369_br143_145_parallel import trace
Q=s.Rational

def main():
    _,_,X,G,_,_,_,A,_,_,_,_=carrier()
    P,X2,_,_,D,*_=trace()
    assert X==X2
    for i in range(4):
        B=A[i]; R=D[i]*X; I=s.eye(35)
        N=s.Matrix.hstack(*R.nullspace())
        assert N.cols==10 and R*B*N==s.zeros(R.rows,10)
        F=N*(N.T*G*N).inv()*N.T*G; Z=I-F
        assert F*F==F and F*B==B*F and F.T*G==G*F
        assert B*B*F==F
        assert (B**3-B/4)*Z==s.zeros(35)
        assert F==Q(4,3)*B**2*(B**2-I/4)
        print('BR202 axis',i,'physical rank 10, subsidiary rank 25',flush=True)
    print('PASS BR202 frozen physical projector polynomial on all four axes')
if __name__=='__main__':main()

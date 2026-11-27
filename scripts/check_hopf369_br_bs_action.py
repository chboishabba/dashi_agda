#!/usr/bin/env python3
"""Material Israel momentum Hessian and separated AK gauge-vector AdS endpoint."""
import sympy as S


def seam_hessian():
    # At any common wall point reduce by congruence to a Lorentz frame.
    # Covariant perturbations U,V are arbitrary symmetric matrices.
    h=S.diag(-1,1,1,1); j=S.symbols('j',real=True)
    def sym(prefix):
        a=S.symbols(prefix+'0:10'); M=S.zeros(4); n=0
        for i in range(4):
            for k in range(i,4):
                M[i,k]=M[k,i]=a[n]; n+=1
        return M
    U,V=sym('u'),sym('v')
    # Israel momentum jump divided by common sqrt(abs(det h)) = -3j h^-1.
    # Vary the density before taking the second variation.
    def dPi(M):
        return -3*j*(S.trace(h*M)*h/2-h*M*h)
    def pair(A,B):
        return S.trace(A*B)
    assert S.expand(pair(dPi(U),V)-pair(dPi(V),U))==0
    # Actual tangent Hessian has indefinite sign: do NOT infer positivity.
    tr=h; sh=S.diag(0,1,-1,0)
    assert S.simplify(pair(dPi(tr),tr))==-12*j
    assert S.simplify(pair(dPi(sh),sh))==6*j
    # Cross terms retain both trace and shear; no division by signed j.
    print('PASS material Israel momentum Hessian reciprocity, opposite trace/shear signs')


def vector_indicial():
    r,p,h2,m=S.symbols('r p h0sq m2',positive=True)
    # AdS4 metric F=1+h0^2 r^2. Static transverse time component
    # of Proca: (r^2 A_t')'=m^2 r^2/F A_t.
    F=1+h2*r*r; A=r**(-p)
    leading=S.simplify((S.diff(r*r*S.diff(A,r),r)*r**p-m/h2))
    assert S.expand(leading-(p*(p-1)-m/h2))==0
    # m^2>=6*h0^2: p_+>=3, Delta=p+1>=4.
    assert S.simplify((1+S.sqrt(1+4*6))/2)==3
    # Transverse boundary components have radial work proportional to r^2 A A'.
    flux=S.simplify(r*r*A*S.diff(A,r))
    assert S.simplify(flux/(-p*r**(1-2*p)))==1
    # Exact reference gauge wave gap via b^2 ground state: not physical radion.
    print('PASS transverse gauge Proca indicial polynomial, decaying branch and flux scaling')


if __name__=='__main__':
    seam_hessian(); vector_indicial()

"""G3 centre-patch analytic budget with separate principal/source caps.
Conditional classical analytic majorant, not a validated finite-time PDE.
"""
from fractions import Fraction as F
import sympy as s

def main():
    eps=F(1,4); k=F(32,729); Q=F(1,18)
    pmin=(1-2*k)/(1-k); pmax=1/((1-Q)*(1-k))
    r=F(1,4); D=1-3*r*r
    a=2*eps*max(2*r*r+2*r,1+3*r*r)/D**2
    assert 3*r*r<F(1,4)
    assert pmax**2*(1+a*a)<3
    assert (1+3*a+3*a*a)/pmin**2<8
    rho=F(1,16); eta=F(1,128); n=80
    # Cauchy on nested radii 1/4,1/8,1/16.
    P0=24; dP0=384
    assert 8*4*eta==F(1,4)
    I=11; P=25; K=1
    assert F(8)/(1-8*4*eta)<I
    # Inverse row norm, not four times its entrywise bound.
    G=F(3,2)*I*P
    dI=I*I*4*P
    dG=F(3,2)*(dI*P+I*dP0)
    Ric=8*dG+32*G*G
    cF=10**7; cA=200
    assert max(2*K,Ric+48*I*K*K)<cF
    assert max(2,8*F(3,2)*I)<cA
    # V_t=A_i(x,V) d_i V+F(x,V), distinct holomorphic caps.
    # Scalar comparison w_t=(cF+3*n*cA*w_z)/(1-z/rho-n*w/eta).
    A=n*(F(3)*cA/(rho*cF)+1/eta)
    T=F(3,32)/(A*cF); W=1/(4*A)
    assert W<eta and F(1,2)*W-A*W*W/2==cF*T
    z,w,t,rh,et,N,f,b=s.symbols('z w t rh et N f b',positive=True)
    aa=N*(3*b/(rh*f)+1/et)
    P=(1-z/rh)*w-aa*w*w/2-f*t
    wt=-s.diff(P,t)/s.diff(P,w); wz=-s.diff(P,z)/s.diff(P,w)
    assert s.simplify(wt*(1-z/rh-N*w/et)-f-3*N*b*wz)==0
    old=F(3,15564800000000000000)
    print('source cap',cF,'principal cap',cA,'Ricci cap',Ric)
    print('T',T,float(T),'improvement',float(T/old),'W',W,float(W))
    print('PASS split-majorant arithmetic and implicit PDE identity')
if __name__=='__main__':main()

"""Conservative original G3 analytic centre patch via BR189/188.
Classical CK; rational coefficient budget, not an interval PDE simulation.
"""
from fractions import Fraction as F


def main():
    # BR189 radial Volterra contraction; real P0T normalization.
    e=F(1,4); R=F(1,2); Q=8*e*e/9
    k=8*e*e*R*R/(9*(1-R*R)**4)
    assert k==F(32,729)
    pmax=1/((1-Q)*(1-k)); pmin=(1-2*k)/(1-k)
    assert pmax*pmax<2 and 1/(pmin*pmin)<2
    # complex Cartesian polydisc |x_i|<=1/8. Even radial solution
    # is holomorphic in x.x since |x.x|<=3/64<1/4.
    r=F(1,8); Dmin=1-3*r*r
    Amax=2*e*max(2*r*r+2*r,1+3*r*r)/Dmin**2
    assert Amax<1
    # h0=q[[I+AA^T,A],[A^T,1]], inverse=q^-1[[I,-A],[-A^T,1+A.A]].
    # entry bound 4 and inverse infinity norm <= 14 (use 32).
    assert pmax*pmax*(1+Amax*Amax)<4
    assert (1+3*Amax+3*Amax*Amax)/pmin**2<32
    rho=F(1,32); eta=F(1,512); n=80
    # On |x|<=1/16, first derivatives P0<=4/(1/16)=64;
    # on |x|<=1/32, derivatives P0<=64/(1/32)=2048.
    P0=64; dP0=2048
    assert 32*4*eta<=F(1,2)
    I=64; P=65; K=1; dP=dP0+1
    # Gaussian ADM first-order system, full ordered entries:
    # h_t=-2K, P_i,t=-2 partial_i K,
    # K_t=Ric(h,P,partial P)+tr(h^-1 K)K-2 K h^-1 K.
    # Fourth spatial (circle) derivative identically zero.
    # Evaluate affine spatial-derivative RHS at zero and each unit
    # derivative of perturbation. All entries of dP bounded by 2049.
    Gamma=F(3*4*I*P,2)
    dInv=16*I*I*P
    dGamma=F(3*4,2)*(dInv*P+I*dP)
    Ric=8*dGamma+32*Gamma*Gamma
    rhs=max(2*K,2,Ric+16*I*K*K+32*I*K*K)
    c=10**13
    assert 2*rhs<c
    # BR188/P0V positive coefficient majorant, evaluated on sum of
    # three formal spatial increments <=rho/2.
    A=n*(3/rho+1/eta)
    T=F(3,32)/(A*c)
    W=1/(4*A)
    assert W<eta and F(1,2)-A*W==F(1,4)
    assert F(1,2)*W-A*W*W/2==c*T
    # Cauchy temporal remainder after quartic for even metric, at T/2.
    # |h-h0|<=W on disk T, hence tail sum <=W/48 at T/2.
    tail=W*F(1,2)**6/(1-F(1,2)**2)
    assert tail==W/48
    print('radial contraction',k,'psi bounds',pmin,pmax)
    print('Gamma',Gamma,'dGamma',dGamma,'Ric',Ric,'RHS',rhs,'c',c)
    print('n',n,'rho',rho,'eta',eta,'A',A,'T',T,'float',float(T))
    print('W',W,'quartic tail at T/2',tail,'float',float(tail))
    print('PASS rational coefficient budget and conditional analytic majorant arithmetic')


if __name__=='__main__':main()

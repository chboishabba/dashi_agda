"""Polar ADM kinetic form and conformal Hamiltonian inverse for repaired TOV.
Linear constraints only; no full polar evolution or spatial coercivity claim.
"""
import sympy as s

def main():
    e,k,m,z,L,f,r,N=s.symbols('e k m z L f r N',real=True)
    # In an orthonormal spatial frame: radial trace e, angular trace 2k.
    # Angular integrated trace-free tensor norm L(L-2)/2.
    H=s.diag(e,k,k)
    assert s.expand(s.trace(H*H)-s.trace(H)**2)==-4*e*k-2*k*k
    # Radial/polar shift has opposite signs in two trace directions.
    assert (-4*e*k-2*k*k).subs({e:1,k:1})==-6
    assert (-4*e*k-2*k*k).subs({e:-1,k:1})==2
    x,l=s.symbols('x l',real=True); p=l/(8*s.pi)
    rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
    F=1-l*(2+l)*(x/3-x*x/5)
    P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*F)
    V=-pt-(rho+pr)/2
    # Conformal spatial metric h_e=(1+e chi)^4 h. At rest,
    # B_e=(1+e chi)^-4 B; correction first derivative vanishes.
    eps,chi,T,R,lap=s.symbols('eps chi T R lap',real=True)
    assert s.diff((1+eps*chi)**-4*T,eps).subs(eps,0)==-4*chi*T
    # R_e=omega^-5(-8 Delta omega+R omega), R=16pi(T+V).
    dR=s.diff((1+eps*chi)**-5*(-8*eps*lap+R*(1+eps*chi)),eps).subs(eps,0)
    assert s.expand((dR+64*s.pi*chi*T).subs(R,16*s.pi*(T+V))+8*lap+64*s.pi*chi*V)==0
    # At lambda=1/10, V/p <= 1+lambda(2+lambda)/(4 fmin) <2.
    # Uses 0<=x<=1, rho+pr>=0, |P|<=1/2, F>=93/100.
    lam=s.Rational(1,10); fmin=s.Rational(93,100)
    assert 1+lam*(2+lam)/(4*fmin)<2
    assert 2-2*lam>s.Rational(3,2)
    # Direct rational Bernstein certificate 2-V/p>0 on [0,1].
    num,den=s.fraction(s.cancel((2-V/p).subs(l,lam)))
    def bern(poly):
        q=s.Poly(poly,x); n=q.degree()
        return [sum(q.nth(j)*s.binomial(i,j)/s.binomial(n,j) for j in range(i+1)) for i in range(n+1)]
    if den.subs(x,0)<0:num,den=-num,-den
    assert min(bern(num))>0 and min(bern(den))>0
    print('PASS polar trace negative control, conformal Hamiltonian variation, rational potential bound')
    print('OPEN polar momentum gauge inverse, spatial Hessian, physical interface and canonical polar flux')
if __name__=='__main__':main()

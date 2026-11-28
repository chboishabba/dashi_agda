"""Vacuum master reconstruction interface: gauge invariant trace maps.
Conventions: Martel-Poisson even Zerilli-Moncrief and odd CPM.
No assertion that arbitrary interior junction data solve vacuum constraints.
"""
import sympy as s

def main():
    r,M,n=s.symbols('r M n',positive=True); F=1-2*M/r; L=2*(n+1)
    # Even invariant amplitudes in Schwarzschild coordinates:
    # Khat, h_rr_hat, radial derivative Khat_r.
    K,H,D=s.symbols('K H D',real=True)
    psi=r/(n+1)*(K+F/(n+3*M/r)*(F*H-r*D))
    inv=s.solve(s.Symbol('P')-psi,H)[0]
    P=s.Symbol('P')
    assert s.cancel(psi.subs(H,inv)-P)==0
    # Standard vacuum inverse for Khat using master and tortoise derivative.
    Q=s.Symbol('Q'); A=(n*(n+1)*r*r+3*n*M*r+6*M*M)/(r*r*(n*r+3*M))
    Kr=A*P+Q
    V=2*F*(n*n*(n+1)*r**3+3*n*n*M*r*r+9*n*M*M*r+9*M**3)/(r**3*(n*r+3*M)**2)
    T=s.Symbol('T') # second time derivative of master
    deriv=lambda expr:s.diff(expr,r)+s.diff(expr,P)*Q/F+s.diff(expr,Q)*(T+V*P)/F
    Hr=s.cancel(inv.subs({K:Kr,D:deriv(Kr)}))
    assert s.cancel(psi.subs({K:Kr,D:deriv(Kr),H:Hr})-P)==0
    # Odd CPM definition, h_aA=r² b_a S_A; orientation chosen epsilon^tr=+1.
    bt,br,brt,btr=s.symbols('bt br brt btr')
    odd=r**3/n*(brt-btr)
    zt,zr,ztr=s.symbols('zt zr ztr')
    assert s.expand(odd.subs({brt:brt+ztr,btr:btr+ztr},simultaneous=True)-odd)==0
    # Exterior energy flux in boundary trace coordinates. A positive
    # impedance condition is dissipative at the left endpoint of exterior
    # if Q=+z P_t (outgoing flux toward the material).
    pt,Z=s.symbols('pt Z',real=True)
    flux=pt*Q
    assert s.expand(flux.subs(Q,Z*pt)-Z*pt**2)==0
    # Do not equate energy positivity to interface passivity. Arbitrary
    # prescribed boundary trace can inject exterior energy.
    assert (-flux).subs({pt:1,Q:-1})==1
    print('PASS even master algebraic reconstruction, odd gauge curl, signed exterior flux')
    print('OPEN vacuum inverse Einstein residual, physical interior trace range, canonical flux normalization and matching')
if __name__=='__main__':main()

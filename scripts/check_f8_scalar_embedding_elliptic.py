"""Constraint-reduced scalar embedding elliptic reconstruction.
Nonzero modes; algebraic estimate, not a closed evolution theorem.
"""
import sympy as s

def exact():
    b,k=s.symbols('b k',positive=True); B=s.sqrt(1+b*b); q=s.I*k*b
    K,w=s.symbols('K w',positive=True)
    F,G,Z,J,Ft,Fn,Zn,f,ft,u,ut,v,V,jx,jy,jm=s.symbols('F G Z J Ft Fn Zn f ft u ut v V jx jy jm')
    r=Z+F/3
    l=-2*B**2*(F-2*r)+2*b*b*(G-2*r)
    X=2*(F-2*r);Y=2*r
    W=2*B*b*(F-G);lam=-2*b*b*(F-2*r)+2*B**2*(G-2*r)
    assert s.simplify(X+2*Y-2*F)==0
    assert s.simplify(B*lam/2+b*W/2-B*(G-2*r))==0
    D=q*v-F+3*B*f; A=ut+l/2+f/B
    rho=w*D+K*A-3*b*K*u
    rho_g=b*b*f-B*lam/2-b*W-Zn-Fn/3-b*ft+jy
    diff=3*Zn-k*k*b*b*f+jx-jy
    mix=q*(W/2+ft-b*f)-3*(w*V+K*q*u)-jm
    # Direct row combination: no division by k until reconstructing f.
    c=k*k*b*b/3+3*w*B+K/B
    rhs=-w*(q*v-F)-K*(ut+l/2)-B*(G-2*r)-Fn/3-b*(3*w*V+jm)/q+(jx+2*jy)/3
    assert s.simplify(q*(rho-rho_g)-q*(c*f-rhs)-q*diff/3-b*mix)==0
    # Substitute exact bulk normal jet (J is the radial constraint datum).
    normal=(2*F+6*Z+b*J-b*Ft)/B
    rhs2=rhs.subs(Fn,normal)
    assert s.simplify(rhs2-rhs+(normal-Fn)/3)==0
    # Positive coefficient, uniform high-frequency elliptic smoothing.
    assert s.simplify(c-k*k*b*b/3-(3*w*B+K/B))==0
    # |k|^3/c² <= 9/(b^4 |k|). Check cross-multiplied positivity.
    m=s.symbols('m',positive=True); c0=k*k*b*b/3+m
    assert s.expand(9*c0*c0-k**4*b**4)==6*b*b*k*k*m+9*m*m
    # Momentum source contribution has an additional inverse k.
    assert s.simplify(b/q+ s.I/k)==0
    # Low-frequency-safe multiplied equation; does not determine f at k=0.
    poly=s.expand(q*(c*f-rhs))
    assert s.simplify(poly.subs(k,0)-(b*(3*w*V+jm)))==0
    # Recover density and mixed constraints in the reverse direction when diff=mix=0.
    assert s.simplify((rho-rho_g).subs({Zn:s.solve(diff,Zn)[0],ft:s.solve(mix,ft)[0]})-(c*f-rhs))==0
    print('9 grouped exact embedding elliptic reconstruction checks PASS')
    return c,rhs2

if __name__=='__main__':exact()

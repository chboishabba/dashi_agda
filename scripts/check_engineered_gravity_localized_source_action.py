"""Localized conserved source: static scaling, charged wall, and receiver bounds.
Classical Derrick/virial, scalar/Maxwell stress and linear GR identities.
Conditional flat-background EFT fixtures; no physical material or 5D solution.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def main():
    # Positive scalar gradients and potential in 3 spatial dimensions.
    R,A,B,C=s.symbols('R A B C',positive=True)
    E=A*R+B*R**3
    assert s.diff(E,R).is_positive
    # Additional inverse-radius energy can stabilize a scale, not prove
    # full field stability. Reverse-solve it at a prescribed radius.
    F=E+C/R
    cs=A*R**2+3*B*R**4
    eq(s.diff(F,R).subs(C,cs))
    eq(s.diff(F,R,2).subs(C,cs),2*A/R+12*B*R)
    # Thin wall plus positive interior vacuum energy and fixed conserved
    # charge on a conducting sphere: electrostatic energy C/R (SI).
    T,U,Q,eps=s.symbols('T U Q eps',positive=True)
    Cq=Q**2/(8*s.pi*eps)
    F=4*s.pi*T*R**2+4*s.pi*U*R**3/3+Cq/R
    q2=8*s.pi*eps*(8*s.pi*T*R**3+4*s.pi*U*R**4)
    eq(s.diff(F,R).subs(Q**2,q2))
    eq(s.diff(F,R,2).subs(Q**2,q2),24*s.pi*T+16*s.pi*U*R)
    # Radial virial: vacuum pressure -U and wall tension pull inward,
    # exterior Maxwell pressure pushes outward. Positive total energy.
    empressure=Q**2/(32*s.pi**2*eps*R**4)
    eq(empressure.subs(Q**2,q2),U+2*T/R)
    # Complete apparatus stress: integrated trace = -3 U V -2 T Area + Eem.
    # For electromagnetic field trace spatial = energy, including exterior.
    Ev=4*s.pi*U*R**3/3; Ew=4*s.pi*T*R**2; Em=Cq/R
    trace=-3*Ev-2*Ew+Em
    eq(trace.subs(Q**2,q2))
    total=Ev+Ew+Em
    eq((total+trace).subs(Q**2,q2),4*Ev+3*Ew)
    # This is a flat-background charged thin-wall fixture; no quantum
    # stability, GR junction, charge leakage or physical vacuum amplitude.
    # Local source divergence for canonical scalar and gauge kinetic term.
    x=s.symbols('x',real=True)
    phi=s.Function('phi')(x); V=s.Function('V'); Z=s.Function('Z')
    F2=s.Function('F2')(x)
    p=s.diff(phi,x)**2/2-V(phi)
    residual=s.diff(phi,x,2)-s.diff(V(phi),phi)-s.diff(Z(phi),phi)*F2/4
    eq(s.diff(p,x)-s.diff(phi,x)*residual,s.diff(Z(phi),x)*F2/4)
    # On shell, EM exchange must pay opposite gradient force; neither
    # sector may independently be treated as a closed conserved source.
    # Common scalar receiver at fixed boundary acceleration: independent
    # clock, gradient and tidal readout, not amplitude-to-force alias.
    m,b,q,r=s.symbols('m b q r',positive=True)
    psi=b*q*R*s.exp(-m*(r-R))/r
    a=-s.diff(psi,r)
    eq(a.subs(r,R),b*q*(m+1/R))
    eq(-s.diff(a,r)/a,2/r+m*m*r/(1+m*r))
    # EM/GW receiver: source-free tensor wave curvature oscillates;
    # its linear period mean vanishes, not a static cancellation.
    t,w,H=s.symbols('t w H',positive=True)
    tide=-s.diff(H*s.cos(w*t),t,2)/2
    eq(s.integrate(tide,(t,0,2*s.pi/w)))
    # F8 signed ledger: retain source, initial, interface, handoff.
    I,J,K,L,N=s.symbols('initial source interface handoff native',real=True)
    eq(N-(I+J+K+L),N-I-J-K-L)
    print('PASS localized scaling, charged wall radial balance, full stress virial, exchange and receiver controls')
    print('OPEN physical vacuum/material parameters, GR charged junction, tensor shielding, original F8 convergence')

if __name__=='__main__':main()

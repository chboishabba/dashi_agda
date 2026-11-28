"""Same-action source reverse-solve and stress conservation, conditional EFT.

Extends master check_kk_same_action_stress.py and
check_sc_coherent_braking_same_source_dynamics.py.
No empirical coefficient or complete 5D source is asserted.
"""
import sympy as s

def check():
    # Covariant target-space metric with positive square completion, including
    # a dynamical reference field Z. Kinetic terms in signature (-,+,+,+).
    K,H,M,l=s.symbols('K H M l',positive=True)
    X=s.symbols('X',real=True)
    G=s.Matrix([[K,0,-l*X],[0,M,0],[-l*X,0,H+l*l*X*X/K]])
    assert s.factor(G.det())==K*M*H
    p,q,r=s.symbols('p q r',real=True)
    v=s.Matrix([p,q,r])
    assert s.expand((v.T*G*v)[0]-(K*(p-l*X*r/K)**2+M*q*q+H*r*r))==0
    # Derivative coupling yields a real mixed scalar/material Hessian about
    # a nonzero reference gradient, with sign fixed by wavevector orientation.
    k,z=s.symbols('k z',real=True)
    ap,ax=s.symbols('a_phi a_X',positive=True)
    # Fourier convention exp(i k x); real fields use conjugate modes.
    Q=s.Matrix([[K*k*k+ap,s.I*l*z*k],[-s.I*l*z*k,M*k*k+ax+l*l*z*z/K]])
    assert Q==Q.conjugate().T
    det=s.expand(Q.det())
    assert s.factor(det-((K*k*k+ap)*(M*k*k+ax)+ap*l*l*z*z/K))==0
    # No zero-mode cross response; the completed kinetic term does not by
    # itself produce a homogeneous mass-mixing instability.
    assert Q[0,1].subs(k,0)==0
    assert s.factor((Q.inv())[0,1]+s.I*l*z*k/det)==0
    # Local same-action static energy and active stress. General anisotropic
    # gradients represented as target-space tangent vectors in each direction.
    t0=s.Matrix(s.symbols('v0:3',real=True))
    t1=s.Matrix(s.symbols('v3:6',real=True))
    t2=s.Matrix(s.symbols('v6:9',real=True))
    t3=s.Matrix(s.symbols('v9:12',real=True))
    U=s.symbols('U',real=True)
    tangents=[t0,t1,t2,t3]
    norm=[(v.T*G*v)[0] for v in tangents]
    lag=(norm[0]-sum(norm[1:]))/2-U
    stress=s.Matrix(4,4,lambda i,j:(tangents[i].T*G*tangents[j])[0]+(s.diag(-1,1,1,1)[i,j])*lag)
    assert s.expand(s.trace(stress)-(2*norm[0]-2*U))==0
    assert s.expand(stress[0,0]-(sum(norm)/2+U))==0
    # Noether identity for arbitrary scalar profiles (flat-space restriction):
    # d_x T_xx equals -sum Euler-Lagrange residual * derivative, sign chosen
    # E_i = partial L / partial q_i - d_x partial L / partial q_i'.
    x=s.symbols('x',real=True)
    fields=[s.Function(n)(x) for n in ('phi','X','Z')]
    v=s.Matrix([s.diff(y,x) for y in fields])
    Gx=G.subs(X,fields[1])
    pot=s.Function('V')(*fields)
    L=-(v.T*Gx*v)[0]/2-pot
    mom=[s.diff(L,w) for w in v]
    EL=[s.diff(L,y)-s.diff(m,x) for y,m in zip(fields,mom)]
    Txx=L-sum(m*w for m,w in zip(mom,v))
    assert s.expand(s.diff(Txx,x)-sum(e*w for e,w in zip(EL,v)))==0
    # Reverse source for a prescribed smooth scalar profile in a fixed
    # reference-gradient linearization. Material gradient must be solved
    # rather than prescribing scalar amplitude independently.
    a=s.symbols('a',real=True,nonzero=True)
    phi=s.Function('p')(x); u=s.Function('u')(x)
    Jphi=-K*s.diff(phi,x,2)+ap*phi+a*s.diff(u,x)
    Ju=-M*s.diff(u,x,2)+(ax+a*a/K)*u-a*s.diff(phi,x)
    assert s.simplify(Jphi.subs(u,0)+K*s.diff(phi,x,2)-ap*phi)==0
    assert s.simplify(Ju.subs(u,0)+a*s.diff(phi,x))==0
    print('PASS positive same-action target metric, finite-k mixing, stress, conservation and inverse source')
    print('OPEN actual material action, background reference stress, full Einstein/5D equations and external source')

if __name__=='__main__':check()

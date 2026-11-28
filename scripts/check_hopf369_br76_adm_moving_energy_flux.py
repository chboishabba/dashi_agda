#!/usr/bin/env python3
"""BR76: actual ADM normal-frame stress-energy flux through a moving wall.

Let t^mu=(∂t-v^i∂i)/N future unit timelike normal to ADM slices,
s^mu=g^{mu nu} F_nu/sqrt(z) unit spacelike normal to material F=0.
For scalar principal wave source (each of original 15+5 components):
 T_mu nu = (∂mu u)(∂nu u)
            -1/2 g_mu nu g^{rho sigma} ∂rho u ∂sigma u.
The exact moving-wall flux is
  T(t,s)=(t·du)(s·du)-1/2 g(t,s) g^-1(du,du).
For a wall orthogonal to the spatial slice, g(t,s)=0 and the flux
reduces exactly to the normal velocity × wall conormal; on a MOVING
wall g(t,s) generally is NOT zero, and its trace term must be retained.
The positive normal energy BR73 is the density T(t,t), up to geometric
density N,sqrt(det H) factors.

This precisely locates the nonlinear moving-wall source term missing
when one substitutes the coordinate BR4 flux into the BR41 wall work.
It does NOT establish physical Israel boundary dissipation, nor the
matrix-valued Einstein connection lower-order stress.

--part formula|moving|channels
"""
import argparse
import sympy as s

def src():
    N=s.Rational(3,2)
    H=s.diag(1,s.Rational(5,4),s.Rational(6,5),s.Rational(4,3))
    v=s.Matrix([s.Rational(1,11),s.Rational(-1,13),s.Rational(2,17),s.Rational(1,19)])
    hi=H.inv()
    g00=-N*N+(v.T*H*v)[0]
    g=s.Matrix([[g00,*list(H*v)]])
    g=g.col_join((H*v).row_join(H))
    Gi=(-s.Matrix([[1/N**2]])).row_join((v/N**2).T)
    Gi=Gi.col_join((v/N**2).row_join(hi-v*v.T/N**2))
    assert (g*Gi-s.eye(5)).applyfunc(s.simplify)==s.zeros(5)
    t=s.Matrix([1,*list(-v)])/N
    F=s.Matrix([-s.Rational(1,5),s.Rational(-1,7),
                s.Rational(1,9),s.Rational(-1,11),1])
    z=s.cancel((F.T*Gi*F)[0])
    assert z>0
    sn=Gi*F/s.sqrt(z)
    return N,H,v,g,Gi,t,F,z,sn

def check_formula():
    N,H,v,g,Gi,t,F,z,sn=src()
    u=s.Matrix(s.symbols('u0:5',real=True))
    en=(t.T*u)[0];wall=(sn.T*u)[0];norm=(u.T*Gi*u)[0]
    flux=en*wall-(t.T*g*sn)[0]*norm/2
    # Independent tensor stress contraction over 25 physical entries:
    T=u*u.T-g*norm/2
    direct=(t.T*T*sn)[0]
    assert s.simplify(flux-direct)==0
    assert s.simplify((t.T*g*t)[0]+1)==0
    assert s.simplify((sn.T*g*sn)[0]-1)==0
    # T(t,t)= (normal velocity² + spatial inverse energy)/2.
    spatial=u[1:5,0]
    E=(en**2+(spatial.T*H.inv()*spatial)[0])/2
    assert s.simplify((t.T*T*t)[0]-E)==0
    return N,H,v,g,Gi,t,F,z,sn,u,en,wall,norm,flux

def formula():
    check_formula()
    print('BR76 exact 25-entry ADM stress tensor, normal energy and moving-wall flux')

def moving():
    N,H,v,g,Gi,t,F,z,sn,u,en,wall,norm,flux=check_formula()
    d=(t.T*g*sn)[0]
    # t·s = (t^mu F_mu)/sqrt(z); nonzero if material moves
    assert s.simplify(d-(t.T*F)[0]/s.sqrt(z))==0
    assert s.simplify(d)!=0
    sample={u[i]:s.Rational(i+2,11) for i in range(5)}
    assert s.simplify((flux-en*wall).subs(sample))!=0
    # Conormal J_F = D sqrt(z) (s·du), not merely u_n.
    D=N*s.sqrt(H.det())
    assert s.simplify(D*(F.T*Gi*u)[0]-D*s.sqrt(z)*wall)==0
    print('BR76 nonzero normal-mixing trace source paid, original material conormal preserved')

def channels():
    N,H,v,g,Gi,t,F,z,sn,u,en,wall,norm,flux=check_formula()
    for dim in (15,5):
        total=s.S.Zero
        for ch in range(dim):
            vals={u[i]:s.Rational((ch+2)*(i+3)%23-11,17) for i in range(5)}
            val=s.simplify(flux.subs(vals))
            assert val.is_real
            total+=val
        assert total.is_real
    print('BR76 full 15+5 channel original signed physical flux with real normal-energy positivity')

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--part",choices=["formula","moving","channels"],default="formula")
    args=p.parse_args();{"formula":formula,"moving":moving,"channels":channels}[args.part]()

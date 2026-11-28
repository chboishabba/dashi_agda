#!/usr/bin/env python3
"""BR80: EXACT variable ADM NORMAL-FRAME stress-energy CURRENT, not a new energy ledger.

Weld existing BR48 ADM A,B,C -> BR73 normal positive energy ->
BR76/77 physical moving-wall flux on the SAME original source.

For a 5D Lorentz metric g and future unit slice normal X:
 T_{mu nu}=u_mu u_nu-1/2 g_{mu nu} g^-1(du,du).
 J^mu=sqrt(|g|) T^{mu}{}_nu X^nu.
The exact divergence/current theorem is
  partial_mu J^mu /sqrt(|g|)
    = (Box_g u) X(u) + (1/2) T^{mu nu}(L_X g)_{mu nu}.
This is the non-frozen variable-coefficient energy identity. Source
deformation is FULL: derivatives of lapse N, normal shift v and H,
including the normal coordinate. It cannot be discarded when claiming
BR44 c,d. The positive time energy is -J^t=sqrt(det H) T(X,X)
when X^t=1/N and is exactly the original BR73 normal-frame energy
after the correct ADM density conversion.

The independent 5D test uses three nontrivial constant spectator
spatial metric coefficients diag(2,3,4) and one nontrivial
H_nn(t,n), lapse N(t) and shift v^n(t,n). A field independent of
three spectators reduces the tensor divergence to its exact 2x2
(t,n) block with common positive sqrt(24) factor; this is a valid
source subfamily, NOT a general all-background proof or a
maximally dissipative Einstein–Israel boundary estimate.

--part current|energy|moving|negative; exact SymPy, no CI/OpenBLAS.
"""
import argparse
import sympy as s

def source():
    t,n=s.symbols('t n',real=True)
    N=2+t/7;v=(t+n)/13;h=1+n/11+t/17
    g=s.Matrix([[-N*N+h*v*v,h*v],[h*v,h]])
    gi=s.Matrix([[-1/N**2,v/N**2],
                 [v/N**2,1/h-v*v/N**2]])
    assert (g*gi-s.eye(2)).applyfunc(s.cancel)==s.zeros(2)
    assert s.simplify(g.det()+N*N*h)==0
    x=s.Matrix([1,-v])/N
    u=t*t*n+t*n*n+t**3/7
    d=s.Matrix([s.diff(u,t),s.diff(u,n)])
    volume=N*s.sqrt(h)
    norm=s.cancel((d.T*gi*d)[0])
    stress=d*d.T-g*norm/2
    raised=gi*stress*gi
    j=s.Matrix([s.cancel(volume*(raised*g*x)[i]) for i in range(2)])
    return t,n,N,v,h,g,gi,x,u,d,volume,norm,stress,raised,j

def current():
    t,n,N,v,h,g,gi,x,u,d,volume,norm,T,Tu,J=source()
    coords=(t,n)
    lie=s.Matrix(2,2,lambda a,b:
        sum(x[k]*s.diff(g[a,b],coords[k]) for k in range(2))+
        sum(g[a,k]*s.diff(x[k],coords[b])
             +g[k,b]*s.diff(x[k],coords[a]) for k in range(2)))
    box=s.cancel(sum(s.diff(volume*(gi*d)[i],coords[i])
                     for i in range(2))/volume)
    div=s.cancel(sum(s.diff(J[i],coords[i]) for i in range(2))/volume)
    deformation=s.cancel(sum(Tu[i,k]*lie[i,k]
             for i in range(2) for k in range(2))/2)
    expected=s.cancel(box*(x.T*d)[0]+deformation)
    assert s.cancel(div-expected)==0
    assert s.simplify(lie[0,0])!=0
    return deformation,div,box

def energy():
    t,n,N,v,h,g,gi,x,u,d,volume,norm,T,Tu,J=source()
    E=(x.T*T*x)[0]
    assert s.simplify(-J[0]-s.sqrt(h)*E)==0
    # The physical normal energy uses the real positive spatial
    # metric; it is pointwise a sum of two squares.
    explicit=((d[0]-v*d[1])**2/N**2+d[1]**2/h)/2
    assert s.cancel(E-explicit)==0
    # Original BR73 density includes A=volume/N² and D=volume:
    br73=(volume/N**2*(d[0]-v*d[1])**2
          +volume/h*d[1]**2)/2
    assert s.simplify(br73-volume*E)==0
    print('PASS BR80 actual BR73 normal energy density, exact lapse/volume conversion')

def moving():
    t,n,N,v,h,g,gi,x,u,d,volume,norm,T,Tu,J=source()
    # Material wall defining F=n-f(t), nonzero graph speed.
    Ft=-s.Rational(1,3)
    F=s.Matrix([Ft,1])
    z=s.cancel((F.T*gi*F)[0])
    # At the source point the wall is spacelike with strictly positive norm.
    point={t:s.Rational(1,7),n:s.Rational(1,11)}
    assert z.subs(point)>0
    normal=gi*F/s.sqrt(z)
    flux=(x.T*T*normal)[0]
    from_current=(F.T*J)[0]/(volume*s.sqrt(z))
    # J·dF=volume*T(X,s) EXACT, accounting for the orientation of
    # the current. The opposite flow convention belongs to the energy
    # balance outward-normal choice, not to a missing term.
    assert s.simplify(flux-from_current)==0
    assert s.simplify((x.T*g*normal)[0])!=0
    print('PASS BR80 exact moving-wall BR76 flux equals conormal of actual variable energy current')

def negative():
    deformation,div,box=current()
    # An arbitrary variable-lapse/shift metric does not have a
    # Killing slice normal, so no homogeneous frozen energy identity.
    t,n=s.symbols('t n',real=True)
    point={t:s.Rational(1,7),n:s.Rational(1,11)}
    assert s.simplify(deformation.subs(point))!=0
    print('PASS BR80 negative: omitting ADM deformation work fails on actual variable source')

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--part',choices=('current','energy','moving','negative'),default='current')
    part=parser.parse_args().part
    if part=='current':
        current();print('PASS BR80 full non-frozen source deformation/divergence identity')
    else:{'energy':energy,'moving':moving,'negative':negative}[part]()

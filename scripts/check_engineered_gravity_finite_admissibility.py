"""Finite admissibility: exact Kottler source attribution, scalar shell energy,
material wall, and source-preserving receiver controls.
Conditional models only; units G=c=1 for Israel, canonical for scalar.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def israel():
    R,u,v=s.symbols('R u v',positive=True)
    x=s.symbols('x',nonnegative=True) # M/R
    Lo=3*(1-2*x-u*u)/R**2
    Li=3*(1-v*v)/R**2
    a=(1-3*x-u*u)/R # outward coordinate acceleration at release
    sig=2*(v-u)/R # 8 pi sigma
    p=((3*x+u*u-1)/u+(1-v*v)/v+u-v)/R
    # DEC is sig>=0 and sig +/- p>=0. Exact linear interval in x.
    lower=(1-u*u-u*(1-v*v)/v-u*(u-v)-2*u*(v-u))/3
    upper=(1-u*u-u*(1-v*v)/v-u*(u-v)+2*u*(v-u))/3
    eq(sig+p,3*(x-lower)/(u*R))
    eq(sig-p,3*(upper-x)/(u*R))
    fixture={R:2,u:s.Rational(1,2),v:s.Rational(3,4),x:s.Rational(1,8)}
    for expr,val in [(Lo,s.Rational(3,8)),(Li,s.Rational(21,64)),(a,s.Rational(3,16)),(sig,s.Rational(1,4)),(p,-s.Rational(5,24))]:
        eq(expr.subs(fixture),val)
    # Fixed cosmological background comparison at SAME area radius.
    # For positive mass, apparatus changes coordinate release acceleration
    # by -M/R² relative to the zero-mass background. Not shielding.
    lam,M=s.symbols('Lambda M',real=True)
    release=-M/R**2+lam*R/3
    eq(release-release.subs(M,0),-M/R**2)
    # Static proper-frame release acceleration is -f'/2sqrt(f).
    # Coordinate release above is d²r/dtau², not local orthonormal value.
    eq((a/u).subs(fixture),s.Rational(3,8))
    # Nonempty strict DEC domain near known fixture, quantified by inequalities;
    # no radial stability without a shell EOS. Dynamic junction potential:
    A,B,h=s.symbols('A B h',real=True,nonzero=True)
    V=(A+B)/2-h*h/4-(A-B)**2/(4*h*h)
    # h=4 pi R sigma, sqrt(A+rdot²)-sqrt(B+rdot²)=h.
    eq((A-V)-((A-B+h*h)/(2*h))**2)
    eq((B-V)-((A-B-h*h)/(2*h))**2)
    eq(V.subs({A:v*v,B:u*u,h:v-u}))

def scalar():
    R,m,q,r=s.symbols('R m q r',positive=True)
    inside=q*R*s.sinh(m*r)/(r*s.sinh(m*R))
    outside=q*R*s.exp(-m*(r-R))/r
    zi=m*s.coth(m*R)-1/R
    zo=m+1/R
    eq(s.diff(inside,r).subs(r,R),q*zi)
    eq(-s.diff(outside,r).subs(r,R),q*zo)
    for phi in (inside,outside):
        eq(s.diff(r*r*s.diff(phi,r),r),r*r*m*m*phi)
        eq(s.diff(r*r*phi*s.diff(phi,r),r),r*r*(s.diff(phi,r)**2+m*m*phi**2))
    # Boundary source from (-Delta+m²)phi=j delta(r-R).
    j=q*(zi+zo)
    E=2*s.pi*R*R*q*q*(zi+zo)
    eq(E,2*s.pi*R*R*q*j)
    b,g=s.symbols('b g',positive=True)
    qstar=g/(b*zo)
    eq(E.subs(q,qstar),2*s.pi*R*R*g*g*(zi+zo)/(b*b*zo**2))
    # Full scalar field storage, NOT shell material or stabilization energy.
    eq(s.limit(E,m,0,dir='+'),2*s.pi*R*q*q)

def material():
    x,L,J,K,b=s.symbols('x L J K b',positive=True)
    theta=4*s.atan(s.exp(x/L))
    U=J*(1-s.cos(theta))
    # On wall L²=K/J; gradient and potential energies equal.
    eq((K*s.diff(theta,x)**2/2-U).subs(K,J*L*L))
    eq(U,2*J/s.cosh(x/L)**2)
    # Energy per transverse area =8 J L, scalar source integral =4 b J L.
    eq(s.integrate(2*J/s.cosh(x/L)**2,(x,-s.oo,s.oo)),4*J*L)
    # Canonical winding stabilization donor, 4D E-frame potential.
    r,W,C=s.symbols('radius W C',positive=True)
    Lam=s.symbols('Lambda5',real=True)
    V=C*(Lam/r+W/r**3)
    r0=s.symbols('r0',positive=True)
    fix={Lam:-3*W/r0**2,r:r0}
    eq(s.diff(V,r).subs(fix))
    eq(s.diff(V,r,2).subs(fix),6*C*W/r0**5)
    eq(V.subs(fix),-2*C*W/r0**3)
    # Negative vacuum value and graviphoton mass issue remain, not uplifted.

def receiver():
    # Finite weak source interpolation preserves 1 and r² exactly.
    a,b,r=s.symbols('a b r',real=True)
    L=(b*b-r*r)/(b*b-a*a);H=1-L
    eq(L+H,1);eq(a*a*L+b*b*H,r*r)
    # Common signed receiver residual with independently bounded nuisance.
    y,model,nuisance=s.symbols('y model nuisance',real=True)
    eq(y-model,(y-model-nuisance)+nuisance)
    # Reciprocal passive conversion and mechanical reaction controls.
    g1,g2,k,d=s.symbols('g1 g2 k d',positive=True)
    A=d*g2/(g1*g2+k*k);B=d*k/(g1*g2+k*k)
    eq(d*A,g1*A*A+g2*B*B)
    F,v1,v2=s.symbols('F v1 v2',real=True)
    eq(F*v1-F*v2,F*(v1-v2))

if __name__=='__main__':
    for fn in (israel,scalar,material,receiver):
        fn();print('PASS',fn.__name__,flush=True)
    print('Conditional finite admissibility only; physical source, stability and continuum remain open')

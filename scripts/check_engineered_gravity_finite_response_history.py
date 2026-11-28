"""Finite inhomogeneous response and retarded DC: conditional exact models.
No actual material coefficients, self-consistent metric or native F8 claim.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def layer():
    # Static scalar perturbation about a stipulated piecewise background.
    # E=1/2 int K q'^2+M² q² dx; flux p=K q'.
    K,m,d,Z=s.symbols('K m d Z',positive=True)
    a,b=s.symbols('a b',real=True)
    C=s.cosh(m*d); S=s.sinh(m*d)
    P=s.Matrix([[C,S/(K*m)],[K*m*S,C]])
    eq(P.det(),1)
    p0=-(P[1,0]+Z*P[0,0])*a/(P[1,1]+Z*P[0,1])
    out=P*s.Matrix([a,p0])
    eq(out[1]+Z*out[0])
    eq(out[0],a/(C+Z*S/(K*m)))
    # A boundary amplitude is not an independently generated Earth source.
    # For fixed positive exterior impedance the far receiver gradient
    # scales with output; material supports and background not included.
    eq(s.limit(out[0],m,0,dir='+'),a/(1+Z*d/K))
    # Static massless tensor-like flux remains constant across the layer.
    eq(s.limit(P[1,0],m,0,dir='+'))
    eq(s.limit(P[0,1],m,0,dir='+'),d/K)

def controller():
    # Actual P024 two-field quadratic potential structure; positive
    # Schur complement after relaxation, not physical PtMn3 coefficients.
    a,b,l,k=s.symbols('a b l k',positive=True)
    O,C,J=s.symbols('O C J',real=True)
    V=(a*O**2+b*C**2)/2-l*O*C-J*C
    eq(s.diff(V,C).subs(C,(l*O+J)/b))
    eq(V.subs(C,(l*O+J)/b),a*O**2/2-(l*O+J)**2/(2*b))
    H=s.Matrix([[a+k*k,-l],[-l,b+k*k]])
    eq(H.det(),(a+k*k)*(b+k*k)-l*l)
    # F(O) even: reversing entire ordered domain does not switch F.
    F0,xi=s.symbols('F0 xi',positive=True)
    F=F0+2*xi*O**2
    eq(F.subs(O,-O),F)
    eq(s.diff(F,O).subs(O,0))
    # Thus unbroken O=0 has no linear scalar-curvature vertex.

def retarded():
    # Exact finite pulse quadratic source into a single retarded mode:
    # q''+Omega² q = J0(1-cos(2 omega t))/2. Zero initial data.
    t,w,W,J=s.symbols('t w W J',positive=True)
    q=J/2*((1-s.cos(W*t))/W**2-(s.cos(2*w*t)-s.cos(W*t))/(W**2-4*w**2))
    eq(q.subs(t,0));eq(s.diff(q,t).subs(t,0))
    eq(s.diff(q,t,2)+W**2*q,J*s.sin(w*t)**2)
    # DC response is a boundary/history problem, not simply mean/J.
    eq(s.limit(q,W,0),J*t*t/4+J*(s.cos(2*w*t)-1)/(8*w*w))
    # after a pulse, retain both final q and qdot in homogeneous evolution.
    L,z,p=s.symbols('L z p',real=True)
    free=z*s.cos(W*(t-L))+p*s.sin(W*(t-L))/W
    eq(free.subs(t,L),z);eq(s.diff(free,t).subs(t,L),p)
    eq(s.diff(free,t,2)+W**2*free)

if __name__=='__main__':
    for fn in (layer,controller,retarded):
        fn();print('PASS',fn.__name__,flush=True)
    print('Conditional finite response; original F8, physical source and full metric OPEN')

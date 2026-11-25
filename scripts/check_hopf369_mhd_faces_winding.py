#!/usr/bin/env python3
"""Exact classical Hopf, MHD, cubical cochain and AFZ chart reference.
No kernel certification, KN soliton or general stability claim.
"""
import sympy as s
from itertools import product, permutations, combinations
x,y,z,t=s.symbols('x y z t',real=True); X=(x,y,z); D=1+x*x+y*y+z*z
f=lambda w:s.factor(s.cancel(w)); clean=lambda w:w.applyfunc(f)
grad=lambda w:s.Matrix([s.diff(w,i) for i in X])
def curl(w):
    return clean(s.Matrix([s.diff(w[2],y)-s.diff(w[1],z),s.diff(w[0],z)-s.diff(w[2],x),s.diff(w[1],x)-s.diff(w[0],y)]))
def div(w): return f(sum(s.diff(w[i],X[i]) for i in range(3)))
def adv(u,v): return clean(v.jacobian(X)*u)
counts={}
def eq(tag,l,r):
    d=l-r
    ok=clean(d)==s.zeros(*d.shape) if isinstance(d,s.MatrixBase) else s.simplify(d)==0
    assert ok,(tag,l,r)
    counts[tag]=counts.get(tag,0)+1
q=s.Matrix([2*x,2*y,2*z,D-2])/D
a,b,c,d=q
A=clean(a*grad(b)-b*grad(a)+c*grad(d)-d*grad(c)); B=curl(A); J=curl(B)
eq('source',B,4*A/D);eq('source',div(B),0);eq('source',div(A),4*z/D**2)
eq('source',A.dot(B),16/D**3);eq('source',B.dot(J),256/D**5)
eq('source',curl(B.cross(J)).subs(dict(zip(X,(1,0,0)))),s.Matrix([-4,0,0]))
# Alfvén units, rho=mu=1; constant total pressure, either alignment.
pressure=33-B.dot(B)/2
for sign in (-1,1):
    u=sign*B; zp=u+B; zm=u-B
    eq('MHD',div(u),0);eq('MHD',adv(u,u)+grad(pressure)-J.cross(B),s.zeros(3,1))
    eq('MHD',curl(u.cross(B)),s.zeros(3,1))
    eq('MHD',adv(zm,zp),s.zeros(3,1));eq('MHD',adv(zp,zm),s.zeros(3,1))
r=s.symbols('r',positive=True)
def radial(p,c): return s.integrate(4*s.pi*r*r*c/(1+r*r)**p,(r,0,s.oo))
eq('MHD_integrals',radial(3,16),4*s.pi**2);eq('MHD_integrals',radial(4,64),8*s.pi**2);eq('MHD_integrals',radial(5,256),20*s.pi**2)
eq('MHD_integrals',J.dot(J),256*(x*x+y*y+4)/D**6)
diss=radial(6,256*(s.Rational(2,3)*r*r+4));eq('MHD_integrals',diss,60*s.pi**2);print('curl energy integral:',diss)
# Spatial faces: actual circulation cochain on 12 positive oriented edges.
edge={}
for i in range(3):
    other=[j for j in range(3) if j!=i]
    for signs in product((-1,1),repeat=2):
        p=list(signs); fixed={X[j]:v for j,v in zip(other,p)}
        edge[(i,*signs)]=s.integrate(A[i].subs(fixed),(X[i],-1,1))
def e(i,fix):return edge[(i,*(fix[j] for j in range(3) if j!=i))]
flux={}
for i in range(3):
    j,k=(i+1)%3,(i+2)%3
    for h in (-1,1):
        flux[i,h]=s.simplify(h*(e(j,{i:h,k:-1})+e(k,{i:h,j:1})-e(j,{i:h,k:1})-e(k,{i:h,j:-1})))
        eq('physical_face_Stokes_integrand',B[i].subs(X[i],h),s.diff(A[k],X[j]).subs(X[i],h)-s.diff(A[j],X[k]).subs(X[i],h))
eq('physical_boundary',sum(flux.values()),0)
assert flux[2,1]!=0 and flux[2,-1]!=0
print('oriented face flux',flux)
# Distinct diagrammatic cube: 3 commuting coordinate reflections, axial curl.
def tr(w,bits,axial=False):
    signs=[(-1)**b for b in bits]; S=s.diag(*signs)
    return clean((s.prod(signs) if axial else 1)*S*w.subs(dict(zip(X,[v*i for v,i in zip(signs,X)])),simultaneous=True))
verts={bits:(tr(A,bits),tr(B,bits,True)) for bits in product((0,1),repeat=3)}
for bits,(av,bv) in verts.items():
    eq('cube_vertex',curl(av),bv);eq('cube_vertex',av.dot(bv),(-1)**sum(bits)*16/D**3)
for bits,(av,bv) in verts.items():
    for i in range(3):
        if bits[i]:continue
        step=tuple(int(j==i) for j in range(3)); dest=tuple(a+b for a,b in zip(bits,step))
        eq('cube_edge',tr(av,step),verts[dest][0]);eq('cube_edge',tr(bv,step,True),verts[dest][1])
for i,j in combinations(range(3),2):
    ei=tuple(int(k==i) for k in range(3));ej=tuple(int(k==j) for k in range(3))
    for h in (0,1):
        start=tuple(h if k not in (i,j) else 0 for k in range(3)); av,bv=verts[start]
        eq('cube_face',tr(tr(av,ei),ej),tr(tr(av,ej),ei));eq('cube_face',tr(tr(bv,ei,True),ej,True),tr(tr(bv,ej,True),ei,True))
for perm in permutations(range(3)):
    av,bv=A,B
    for i in perm:
        step=tuple(int(j==i) for j in range(3));av,bv=tr(av,step),tr(bv,step,True)
    eq('cube_path',av,verts[1,1,1][0]);eq('cube_path',bv,verts[1,1,1][1])
# Signed winding: t=|z1|^2; normalized powers; orientation chosen to match Q(1,1)=1.
# A = P f(t) dxi1 + Q (1-f(t)) dxi2, A wedge dA = PQ f'(t) dt dxi1 dxi2.
for P,Q in product((-3,-2,-1,1,2,3),repeat=2):
    p,q=abs(P),abs(Q); F=t**p/(t**p+(1-t)**q)
    eq('winding_endpoints',F.subs(t,0),0);eq('winding_endpoints',F.subs(t,1),1)
    # coefficient via exterior multiplication (orientation t,xi1,xi2)
    eq('winding_density',P*F*Q*s.diff(F,t)+Q*(1-F)*P*s.diff(F,t),P*Q*s.diff(F,t))
    eq('winding_charge',P*Q*(F.subs(t,1)-F.subs(t,0)),P*Q)
    K=p*p*(1-t)+q*q*t; C=s.Rational(p*q*(p+q),2)
    G=t if p==q else s.Rational(q,q-p)*(1-p/s.sqrt(K))
    eq('AFZ_profile',G.subs(t,0),0);eq('AFZ_profile',G.subs(t,1),1)
    eq('AFZ_profile',s.diff(G,t),C/K**s.Rational(3,2))
    # conserved squared canonical momentum, omitting positive constant factor.
    eq('AFZ_momentum',s.diff(K**s.Rational(3,2)*s.diff(G,t),t),0)
    eq('AFZ_charge',P*Q*(G.subs(t,1)-G.subs(t,0)),P*Q)
# Zero winding is separately constructed, not use nonzero AFZ formula at p*q=0.
for P,Q in [(0,0),(0,1),(1,0),(0,-2),(-2,0)]:
    F=t**abs(P)/(t**abs(P)+(1-t)**abs(Q))
    U,V=P*F,Q*(1-F)
    eq('zero_winding',V*s.diff(U,t)-U*s.diff(V,t),0)
# Distinguish smooth normalized polynomial map from AFZ stationary chart profile.
p,q=2,1; F=t**p/(t**p+(1-t)**q);K=p*p*(1-t)+q*q*t
assert s.simplify(s.diff(K**s.Rational(3,2)*s.diff(F,t),t).subs(t,s.Rational(1,2)))!=0
print('checks:',counts,'total',sum(counts.values()),'SymPy',s.__version__)

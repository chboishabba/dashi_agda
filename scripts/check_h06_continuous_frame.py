#!/usr/bin/env python3
"""H06 affine two-plane in R4 x independent SO3; actual AN metric consumer.
Exact rational/symbolic chart tests, numerical tensor pullback only.
"""
import os
os.environ.setdefault('JAX_ENABLE_X64','true')
os.environ.setdefault('XLA_FLAGS','--xla_cpu_multi_thread_eigen=false intra_op_parallelism_threads=1')
from itertools import combinations, product
import sympy as s
import numpy as np

def require(ok,label):
    if not bool(ok): raise RuntimeError(label)

def rotation(q):
    w,x,y,z=q; N=sum(v*v for v in q)
    if N==0: raise ValueError('zero quaternion')
    return s.Matrix([[N-2*(y*y+z*z),2*(x*y-w*z),2*(x*z+w*y)],
        [2*(x*y+w*z),N-2*(x*x+z*z),2*(y*z-w*x)],
        [2*(x*z-w*y),2*(y*z+w*x),N-2*(x*x+y*y)]])/N

def zero(M): return all(s.cancel(v)==0 for v in M)

def atlas(B,o,p):
    E=s.eye(4)[list(p),:]; A=E*B
    if A.det()==0:return None
    D=B*A.inv(); return D,o-D*E*o

def plane_projector(B,o):
    P=B*(B.T*B).inv()*B.T
    return P,(s.eye(4)-P)*o

x,y,z=s.symbols('x y z',real=True); q=s.Matrix([1,x,y,z]); R=rotation(q)
require(zero(R.T*R-s.eye(3)) and s.cancel(R.det()-1)==0,'SO3 symbolic')
# Recover projective quaternion chart from actual rotation (not a gauge choice).
# Q = q q^T / norm², reconstructed from R by trace and antisymmetric/symmetric entries.
def quaternion_projector(R):
    a=(1+s.trace(R))/4
    v=s.Matrix([R[2,1]-R[1,2],R[0,2]-R[2,0],R[1,0]-R[0,1]])/4
    D=(R+R.T)/4+(s.Rational(1,2)-a)*s.eye(3)
    return a.row_join(v.T).col_join(v.row_join(D)) if hasattr(a,'row_join') else s.Matrix([[a]]).row_join(v.T).col_join(v.row_join(D))
Q=quaternion_projector(R)
require(zero(Q-q*q.T/(q.dot(q))),'projective quaternion reverse')
require(rotation(s.Matrix([1,0,0,1]))==s.Matrix([[0,-1,0],[1,0,0],[0,0,1]]),'original quarter turn')
require(rotation(s.Matrix([1,-1,-1,-1]))==s.Matrix([[0,1,0],[0,0,1],[1,0,0]]),'literal H05 cycle')
# 4 chart domains in RP3; nonzero component, normalize by it, keep its sign separately for Spin lift.
qc=0
for q0 in product((-1,0,1),repeat=4):
    if not any(q0):continue
    q=s.Matrix(q0); R=rotation(q); Q=quaternion_projector(R)
    require(rotation(-q)==R,'central sign')
    for i in range(4):
        if not q[i]:continue
        u=q/q[i]; require(Q[:,i]/Q[i,i]==u,'chart inverse')
        for j in range(4):
            if not q[j]:continue
            require(u/u[j]==q/q[j] and rotation(u/u[j])==R,'chart transition');qc+=1
# Actual six-dimensional affine plane coordinates: four slope and two offset.
a,b,c,d,e,f=s.symbols('a b c d e f',real=True)
B=s.Matrix([[1,0],[0,1],[a,b],[c,d]]); o=s.Matrix([0,0,e,f]); P=s.eye(4)-B*s.eye(4)[:2,:]
require(zero(P*B) and zero(P*P-P),'affine symbolic split')
# Exact independence: normalized plane columns and offsets are recovered from the plane,
# rotation chart coordinates from Q. Product chart has explicit 9-coordinate inverse.
marks=tuple(combinations(range(4),2)); pc=tc=0
for p in marks:
    rest=[i for i in range(4) if i not in p]
    for vals in product((-1,0,1),repeat=4):
        B=s.zeros(4,2); B[p[0],0]=1; B[p[1],1]=1
        for k,i in enumerate(rest):B[i,0],B[i,1]=vals[2*k:2*k+2]
        o=s.zeros(4,1); o[rest[0]]=1;o[rest[1]]=-1
        charts={r:C for r in marks if (C:=atlas(B,o,r)) is not None}
        for r,(D,h) in charts.items():
            require(atlas(D,h,p)==(B,o),'affine reverse')
            require(zero(plane_projector(D,h)[0]-plane_projector(B,o)[0]) and zero(plane_projector(D,h)[1]-plane_projector(B,o)[1]),'same affine plane');pc+=1
            for t,C in charts.items():
                require(atlas(D,h,t)==C,'affine cocycle');tc+=1
print('PASS exact affine pairs/triples',pc,tc,'quaternion chart overlaps',qc,flush=True)
# Original AN metric formula, transcribed from check_hopf369_p0an_metric.py
# (blob ffdd57a98eea54be991801468e9e20816b56ab0d). Not an Einstein solve.
import jax
import jax.numpy as j
L=2*np.log(2); h0=.8

def metric(X,eps):
    x=X[:3]; y=X[3]; r2=x@x; fac=2*(1+r2)/(h0*(1-r2)**2)
    df=2/h0*((1-r2)**-2+2*(1+r2)*(1-r2)**-3)
    pull=fac*j.eye(3)+2*df*j.outer(x,x)
    X0=fac*x; X1,X2,X3=X0; D=1+X0@X0
    A=2*j.array([2*X1*X3-2*X2,2*X1+2*X2*X3,1-X1**2-X2**2+X3**2])/D**2
    a=eps*pull@A; gamma=4/(h0**2*(1-r2)**2)*j.eye(3)
    S=1+(a@a)/gamma[0,0]; H=gamma+j.outer(a,a)
    b=j.cosh(y-L/2)/1.25
    Q=gamma+(b*b-1)*H/j.sqrt(S)
    return j.block([[Q+j.outer(a,a),a[:,None]],[a[None,:],j.ones((1,1))]])

def rot(t):
    c=(1-t*t)/(1+t*t); z=2*t/(1+t*t)
    return j.array([[c,-z,0.],[z,c,0.],[0.,0.,1.]])
def phi(U):return j.concatenate((U[:1],rot(U[0])@U[1:4],U[4:]))
def source(U,eps):
    g=j.zeros((5,5)); return g.at[0,0].set(-1.).at[1:,1:].set(metric(U[1:],eps))
def pullback(U,eps):
    J=jax.jacfwd(phi)(U); return J.T@source(phi(U),eps)@J

def christ(g,U,eps):
    h=g(U,eps); d=jax.jacfwd(g,0)(U,eps)
    return .5*j.einsum('al,lij->aij',j.linalg.inv(h),d.transpose(0,2,1)+d-d.transpose(2,0,1))

# Test affine coordinate map with independent t, including Hessian term of connection.
maxerr=0.; maxmixed=0.; frozenerr=0.; signederr=0.; checks=0
for eps in (.025,-.025,0.):
    for U in (j.array([.2,.1,-.15,.07,.3]),j.array([-.35,-.12,.08,.16,.7])):
        J=jax.jacfwd(phi)(U); Hess=jax.jacfwd(jax.jacfwd(phi))(U)
        g=pullback(U,eps); G=christ(pullback,U,eps)
        expected=j.einsum('ka,aij->kij',j.linalg.inv(J),j.einsum('abc,bi,cj->aij',christ(source,phi(U),eps),J,J)+Hess)
        err=float(j.max(j.abs(G-expected))); maxerr=max(maxerr,err)
        require(err<1e-10,'connection naturality')
        require(np.linalg.eigvalsh(np.array(g))[0]<0 and np.all(np.linalg.eigvalsh(np.array(g))[1:]>0),'signature')
        frozen=J.at[1:4,0].set(0.); frozenerr=max(frozenerr,float(j.max(j.abs(g-frozen.T@source(phi(U),eps)@frozen))))
        maxmixed=max(maxmixed,float(j.max(j.abs(g[0,1:]))))
        # original signed circle reflection, independent of time-dependent frame
        V=U.at[4].set(L-U[4]); T=j.diag(j.array([1.,1.,1.,1.,-1.]))
        se=float(j.max(j.abs(g-T@pullback(V,-eps)@T)));signederr=max(signederr,se);require(se<1e-10,'signed circle reflection')
        checks+=1
require(frozenerr>1e-3 and maxmixed>1e-3,'frozen frame negative control')
print('PASS AN tensor cases',checks,'connection max',maxerr,'signed reflection max',signederr,'mixed max',maxmixed,'frozen-frame error',frozenerr,flush=True)

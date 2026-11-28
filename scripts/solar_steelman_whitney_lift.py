"""Exact rational Whitney shell lift of the occupied unity trajectory.
Normalized piecewise-flat shell and selected loop ports, not atmospheric SI data.
"""
import hashlib
from pathlib import Path
from itertools import combinations
import numpy as np
import sympy as S
from sympy.polys.matrices import DomainMatrix
from solar_spherical_whitney import shell_mesh, whitney
from solar_steelman_unity import rhs, zero


def masses(xyz,s,m):
    # Exact barycentric second moments V(1+delta_ij)/20.
    M=S.zeros(len(s[1])); N=S.zeros(len(s[2])); volume=0
    ee=list(combinations(range(4),2)); ff=list(combinations(range(4),3))
    for t in s[3]:
        p=S.Matrix([[S.Rational(float(v)) for v in xyz[j]] for j in t]);
        V=abs((p[1:,:]-S.ones(3,1)*p[0,:]).det())/6;volume+=V
        g=S.ones(4,1).row_join(p).inv()[1:,:]
        W=[]; Q=[]
        for i,j in ee:
            w=S.zeros(3,4);w[:,i]=g[:,j];w[:,j]=-g[:,i];W.append(w)
        for i,j,k in ff:
            q=S.zeros(3,4);q[:,i]=2*g[:,j].cross(g[:,k]);q[:,j]=2*g[:,k].cross(g[:,i]);q[:,k]=2*g[:,i].cross(g[:,j]);Q.append(q)
        moments=V*(S.ones(4)+S.eye(4))/20
        for forms,indices,mat in [(W,ee,M),(Q,ff,N)]:
            ids=[m[len(indices[0])-1][tuple(t[j] for j in e)] for e in indices]
            for i,a in enumerate(forms):
                for j,b in enumerate(forms):mat[ids[i],ids[j]]+=S.trace(a*moments*b.T)
    return M,N,volume


def solve(A,B):
    a,b=DomainMatrix.from_Matrix(A).unify(DomainMatrix.from_Matrix(B));num,den=a.solve_den(b)
    return num.to_Matrix()/num.domain.to_sympy(den)


def geometry():
    raw=Path(__file__).with_name('solar_spherical_whitney.py').read_bytes()
    assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='3faf4f27b043936085465693f9d2a2d36b675a2d'
    xyz,s,m,d=shell_mesh([1,1.5,2]);G,C,D=map(S.Matrix,d)
    M,N,V=masses(xyz,s,m);Mf,Nf,Vf=whitney(xyz,s,m,epsilon=1,mu=1)
    assert np.max(abs(np.array(M,float)-Mf))<1e-12 and np.max(abs(np.array(N,float)-Nf))<1e-12
    assert abs(float(V)-Vf)<1e-12
    # Three original mesh face-boundary cycles, one per radial layer.
    T=S.Matrix.vstack(*[C[m[2][(j,j+2,j+4)],:] for j in (12,6,0)])
    assert T.rank()==3 and T*G==S.zeros(3,G.cols)
    assert C*G==S.zeros(C.rows,G.cols) and D*C==S.zeros(D.rows,C.cols)
    return M,N,G,C,D,T


def inverse(M,N,G,C,D,T,w,source,receiver):
    K=C.T*N*C-w*w*M
    A=solve(K,T.T); assert K*A==T.T
    X=w*T*A;assert X==X.T
    x=X[source,receiver];assert x!=0
    # Fixed source current 1, receiver draw p=i/x. Exact source reference
    # match after compensating its series reactance; receiver R=x²>0.
    p=S.I/x; i=S.zeros(3,1);i[source]=1;i[receiver]=-p
    # Forward solve from fixed incident wave 1 and reverse-synthesized load.
    # Source relation v_s-i Xss i_s+i_s=2; receiver v_r=(x²-i Xrr)p.
    forward=S.Matrix([[1,-S.I*x],[S.I*x,-x*x]]).inv()*S.Matrix([2,0])
    assert zero(forward-S.Matrix([1,p]))
    e=S.I*w*A*i;b=-C*e/(S.I*w);v=T*e
    assert zero(S.I*w*M*e-C.T*N*b-T.T*i) and zero(S.I*w*b+C*e)
    assert zero(G.T*M*e) and zero(D*b)
    assert S.simplify(v[source]-S.I*X[source,source])==1
    assert S.simplify(v[receiver]/p-x*x+S.I*X[receiver,receiver])==0
    assert S.simplify(S.re(S.conjugate(p)*v[receiver]))==1
    assert S.simplify(S.re(v[source]))==1
    assert S.simplify(S.re((i.H*v)[0]))==0
    inactive=3-source-receiver;assert i[inactive]==0
    print('frequency',w,'source',source,'receiver',receiver,'cross reactance',float(x),'inactive voltage',complex(v[inactive]),flush=True)
    return X,i,e,b,v


def foster(w,v,target):
    # Target series reactance, with a pole at the other band.
    y=target-w/(v*v-w*w);L=1+abs(y)/w;K=w*(w*L-y)
    assert L>0 and K>0
    assert S.cancel(w*L-K/w+w/(v*v-w*w)-target)==0
    return L,K


def causal_branch(w,v,target,current,blocked_effort):
    L,K=foster(w,v,target)
    # RMS complex phasors for actual qdot=i, xdot=i-v²z, zdot=x.
    q=current/(S.I*w);x=S.I*w*current/(v*v-w*w);z=x/(S.I*w)
    assert zero(S.I*w*q-current) and zero(S.I*w*x-current+v*v*z) and zero(S.I*w*z-x)
    assert zero(S.I*w*L*current+K*q+x-S.I*target*current)
    # Other carrier: no current or capacitor charge, finite resonator state.
    xb=blocked_effort;zb=xb/(S.I*v)
    assert zero(S.I*v*xb+v*v*zb) and zero(S.I*v*zb-xb)
    # Exact arbitrary-state storage identity; no intermediate dissipation.
    i,di,q,x,z,l,k,n=S.symbols('i di q x z l k n',real=True)
    assert S.expand(l*i*di+k*q*i+x*(i-n*n*z)+n*n*z*x-i*(l*di+k*q+x))==0
    return L,K


def converter_port_ledger():
    rr=S.symbols('r:12',real=True);a,c,b,d,e,v=[rr[2*j]+S.I*rr[2*j+1] for j in range(6)]
    f=rhs(S.Matrix([a,c,b,d]),0);bright=(b+d)/S.sqrt(2);dark=(b-d)/S.sqrt(2)
    # Replace source term and input radiation by actual effort, and bright
    # damping by the actual distributed load voltage; dark termination stays.
    f[0]+=a+e/S.sqrt(2);f[2]+=(bright-v)/S.sqrt(2);f[3]+=(bright-v)/S.sqrt(2)
    work=2*S.re(S.conjugate(a)*f[0]+S.conjugate(c)*f[1])+S.re(S.conjugate(b)*f[2]+S.conjugate(d)*f[3])
    assert zero(work-S.re(S.conjugate(e)*S.sqrt(2)*a)+S.re(S.conjugate(v)*bright)+dark*S.conjugate(dark))


def run():
    M,N,G,C,D,T=geometry();print('mesh',M.rows,N.rows,'exact full Hodge',flush=True)
    hi=inverse(M,N,G,C,D,T,S.Integer(2),0,1)
    lo=inverse(M,N,G,C,D,T,S.Integer(1),1,2)
    # Existing modal endpoint with the full-frequency input phase i and
    # half-frequency phase exp(i*pi/4). Real transformer x maps receiver
    # draw i/x to normalized converter input i, preserving signed power.
    h=(1+S.I)/S.sqrt(2);x=S.Matrix([S.I/S.sqrt(2),S.I/S.sqrt(2),h/S.sqrt(2),h/S.sqrt(2)])
    assert zero(rhs(x,S.I))
    bright=(x[2]+x[3])/S.sqrt(2);dark=(x[2]-x[3])/S.sqrt(2)
    assert zero(bright-h) and zero(dark)
    assert zero(hi[0][0,1]*(-hi[1][1])-S.I)
    assert zero(h*lo[1][1]-bright)
    converter_port_ledger()
    # Four shared-shell causal compensator branches. Current orientation is
    # into each branch; source-side compensation uses -shell self-reactance
    # with current injected toward shell. Inactive branch sees full voltage.
    # Outer high source branch; middle high converter draw; middle low
    # converter injection; inner low final load draw. Blocked efforts retain
    # the actual other-band shell voltage (scaled by h for the low band).
    cases=[(2,1,-hi[0][0,0],hi[1][0],h*lo[4][0]),
           (2,1,-hi[0][1,1],-hi[1][1],h*lo[4][1]),
           (1,2,-lo[0][1,1],h*lo[1][1],hi[4][1]),
           (1,2,-lo[0][2,2],-h*lo[1][2],hi[4][2])]
    for w,v,target,current,blocked in cases:
        causal_branch(S.Integer(w),S.Integer(v),target,current,blocked)
    # Exact matched nominal converter input/output efforts: source-side
    # transformer real x, so v_conv=v_shell_adjusted/x and i_conv=x*p.
    cross=hi[0][0,1];p=-hi[1][1]
    assert zero((hi[4][1]+S.I*hi[0][1,1]*p)/cross-S.I)
    assert zero(h*(lo[4][1]-S.I*lo[0][1,1])-bright)
    # Reconstruct a SINGLE real distributed field containing both bands;
    # linear cochain equations are exact coefficientwise. RMS convention
    # sqrt(2) Re phasors. Distinct harmonics are work-orthogonal over 2pi.
    t=S.symbols('t',real=True)
    assert S.integrate(S.cos(t)*S.cos(2*t),(t,0,2*S.pi))==0
    assert S.integrate(S.sin(t)*S.sin(2*t),(t,0,2*S.pi))==0
    assert S.integrate(S.sin(t)*S.cos(2*t),(t,0,2*S.pi))==0
    assert S.integrate(S.cos(t)*S.sin(2*t),(t,0,2*S.pi))==0
    print('PASS exact occupied Whitney coefficient lift: incident=1 output=1 reflection=0, Gauss and inactive traces retained')
    print('PASS four causal Foster branch harmonic states, zero blocked currents, exact reciprocal converter effort-flow ledger')
    print('Conditional harmonic trajectory; physical nonlinear material and joint off-harmonic stability not certified')
if __name__=='__main__':run()

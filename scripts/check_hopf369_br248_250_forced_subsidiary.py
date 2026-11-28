"""BR248-250: exact scalar principal energy; sampled actual G3 constraints."""
import argparse
import numpy as np
import sympy as s
from scipy.ndimage import spline_filter, map_coordinates
from check_hopf369_br240_metric_history import initial, acceleration
from check_hopf369_br242_244_constraint_history import curvature

def energy():
    t,x,y=s.symbols('t x y'); X=(x,y)
    u,A=[s.Function(k)(t,x,y) for k in ('u','A')]
    B=s.Matrix([s.Function('B%d'%i)(t,x,y) for i in range(2)])
    D=s.Matrix(2,2,lambda i,j:s.Function('D%d%d'%tuple(sorted((i,j))))(t,x,y))
    v=u.diff(t); w=s.Matrix([u.diff(i) for i in X])
    P=-(A*v).diff(t)+B.dot(w).diff(t)+sum((B[i]*v+(D*w)[i]).diff(X[i]) for i in range(2))
    E=(A*v*v+w.dot(D*w)+u*u)/2
    flux=sum((v*(B[i]*v+(D*w)[i])).diff(X[i]) for i in range(2))
    work=-A.diff(t)*v*v/2+v*B.diff(t).dot(w)+w.dot(D.diff(t)*w)/2+u*v
    assert s.expand(E.diff(t)-flux-work+v*P)==0
    print('BR248 PASS variable-coefficient energy identity')

def history(n):
    g,v,dx=initial(n); dt=.06/{11:4,17:6,23:8}[n]; steps=round(.12/dt); states=[g.copy()]
    def rhs(g,v):
        a=acceleration(g,v,dx); vv=v.copy()
        for i in range(3):
            for j in (0,-1):
                p=[slice(None)]*3;p[i]=j;a[tuple(p)]=0;vv[tuple(p)]=0
        return vv,a
    for _ in range(steps):
        u,a=rhs(g,v);w,b=rhs(g+dt*u/2,v+dt*a/2);g+=dt*w;v+=dt*b;states.append(g.copy())
    G=np.array(states); coeff=[spline_filter(G[...,i,j],order=3) for i in range(5) for j in range(5)]
    def read(p):
        q=((p-np.array([0,-1.5,-1.5,-1.5]))/np.array([dt,dx,dx,dx]))[:,None]
        return np.array([map_coordinates(c,q,order=3,prefilter=False)[0] for c in coeff]).reshape(5,5)
    return read

def sample(read,p,h):
    g=read(p); f=np.zeros((5,5,5)); J=np.zeros((5,5,5,5)); eye=np.eye(4)*h
    for i in range(4):
        a=read(p+eye[i]);b=read(p-eye[i]);f[i]=(a-b)/(2*h);J[i,i]=(a+b-2*g)/h**2
        for j in range(i):
            J[i,j]=J[j,i]=sum(a*b*read(p+a*eye[i]+b*eye[j]) for a in (-1,1) for b in (-1,1))/(4*h*h)
    I=np.linalg.inv(g);R,C,U=curvature(g,f,J);L=(f.swapaxes(0,1)+np.moveaxis(f,0,-1)-f)/2
    G=np.einsum('ae,ebc->abc',I,L);E=R-(U+U.T)/2
    return g,I,G,R,C,U,E

def probe(read,p,h):
    g,I,G,R,C,U,E=sample(read,p,h);dU=np.zeros((5,5,5));dE=np.zeros_like(dU)
    for k in range(4):
        z=np.eye(4)[k]*h;a=sample(read,p+z,h);b=sample(read,p-z,h);dU[k]=(a[5]-b[5])/(2*h);dE[k]=(a[6]-b[6])/(2*h)
    def cov(T,dT):return dT-np.einsum('aki,aj->kij',G,T)-np.einsum('akj,ia->kij',G,T)
    CU=cov(U,dU);CE=cov(E,dE);wave=np.einsum('ki,kij->j',I,CU)+R@I@C
    force=-2*np.einsum('ki,kij->j',I,CE)+np.einsum('ij,kij->k',I,CE)
    den=np.sqrt(-np.linalg.det(g));A=-den*I[0,0];D=den*I[1:,1:];margin=min(A,np.linalg.eigvalsh(D).min());assert margin>0
    partial=U+np.einsum('aij,a->ij',G,C);en=(A*(partial[0]@partial[0])+np.einsum('ij,ia,ja',D,partial[1:],partial[1:])+C@C)/2
    ein=R-g*np.sum(I*R)/2;normal=-I[:,0]/np.sqrt(-I[0,0])
    return np.array([np.max(abs(wave-force)),np.max(abs(force)),np.max(abs(E)),abs(2*normal@ein@normal),np.max(abs(normal@ein[:,1:])),np.max(abs(C)),en,margin])

def refine(n):
    read=history(n);pts=np.array([[.06,0,0,0],[.06,.3,0,0],[.06,.3,-.3,.3]])
    for h in (.002,.001):
        v=np.array([probe(read,p,h) for p in pts]);assert np.isfinite(v).all()
        print('BR249/250',n,'h',h,'max [forced defect,force,reduced,H,M,C,energy]',v[:,:7].max(axis=0).tolist(),'min margin',v[:,7].min(),flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['energy','refine'],required=True);p.add_argument('--n',type=int,choices=[11,17,23],default=11);a=p.parse_args();energy() if a.part=='energy' else refine(a.n)

"""Original F8 radial FV obstruction and common-prepotential spectral reference.
Uses #1530 angular/Ricci jet owners; different outer boundary closure, not production parity.
"""
import numpy as np
import sympy as s
from scipy.special import spherical_jn
from scipy.optimize import brentq
from numpy.polynomial.legendre import leggauss
from math import asinh,sqrt,ceil
from check_f8_tensor_backreaction import angular,radial,ricci_jet
from check_f8_ym_ns_weld import source


def obstruction():
    x=s.Symbol('x'); h=s.Rational(1,2)
    def R(d,n):
        W=[((j+h)**d-max(j-h,0)**d)/d for j in range(n)]
        F=[(j+h)**(d-1) for j in range(n)]
        return s.Matrix(n,n,lambda j,k: (-(F[j]+(F[j-1] if j else 0)) if k==j else F[j] if k==j+1 else F[k] if k==j-1 else 0)/W[j])
    for n in (2,3,5,8):
        for d in (3,5,7,9):
            p=R(d,n).charpoly(x).as_expr();q=R(d+2,n).charpoly(x).as_expr()
            assert s.degree(s.gcd(p,q),x)==0
    print('16 exact native FV disjoint-spectrum controls PASS; intertwiners zero on these grids',flush=True)


def evolve(n,ny,dt,common):
    R=3.2;eps=.04;dr=R/n;dy=2.1/(ny-1);r=np.arange(n)*dr;Y=np.arange(ny)*dy
    F=lambda t:asinh(t)-sqrt(1+t*t)/t
    T0=F(1);Tend=F(12);nt=ceil((Tend-T0)/dt);dt=(Tend-T0)/nt
    it=round((F(11.8)-T0)/dt);iy=round(.06/dy);ir=round(2.52/dr)
    ti=np.arange(it-2,it+3);yi=np.arange(iy-2,iy+3);ri=np.arange(ir-2,ir+3)
    if common:
        k=np.arange(1,n+1)*np.pi/R;a,b=leggauss(160);rr=(a+1)*eps/2
        src=(2/R)*k*(np.sin(k[:,None]*rr)@(b*rr*eps**4*np.exp(1-1/(1-(rr/eps)**2))*eps/2))
        sources=src[None,:];dims=(3,)
    else:sources=source(r,dr,eps);dims=(3,7,11)
    geom=[]
    for j in range(2*(it+3)+1):
        ds=j*dt/2;t=brentq(lambda t:F(t)-T0-ds,.5,14);v=-1/sqrt(1+t*t);b=1/t
        amp=-6*sqrt(1-v*v)/b*np.exp(1-1/(1-(2*ds/.065-1)**2)) if 0<ds<.065 else 0.
        geom.append((1+v,1-v,1.5/(b+Y)[:,None],amp))
    def D(a):
        b=np.empty_like(a);b[0]=(a[1]-a[0])/dy;b[-1]=(a[-1]-a[-2])/dy;b[1:-1]=(a[2:]-a[:-2])/(2*dy);return b
    hist=[]
    for q,d in enumerate(dims):
        diag,p,m=radial(d,n,dr);state=np.zeros((3,ny,n));snap=[]
        def B(state,j):
            U,P,M=state;a,c,Z,amp=geom[j]
            if common:force=-k*k*U
            else:
                force=diag*U;force[:,:-1]+=p*U[:,1:];force[:,1:]+=m*U[:,:-1]
            force-=Z*(P-M);dp=a*D(P)+force;dm=-c*D(M)+force
            dp[-1]-=2*a*P[-1]/dy;dm[0]+=2*(a*P[0]-c*M[0]-2*amp*sources[q])/dy
            return state+dt*np.array([(a*P+c*M)/2,dp,dm])
        for j in range(it+3):
            if j in ti:snap.append(state[0,yi,:].copy() if common else state[0][np.ix_(yi,ri)].copy())
            if j==it+2:break
            a=B(state,2*j);b=.75*state+.25*B(a,2*j+2);state=state/3+2*B(b,2*j+1)/3
        hist.append(snap)
    return np.array(hist), (k if common else r[ri],T0+ti*dt,Y[yi],eps)


def make_evaluator(hist,meta,common,xyz,polys):
    nodes,Tn,Yn,eps=meta
    def basis(nodes,x):
        h=nodes[1]-nodes[0];a=(nodes-nodes[2])/h;t=(x-nodes[2])/h
        return np.linalg.solve(np.array([a**j for j in range(5)]),np.array([t**j for j in range(5)]))
    fun=[s.lambdify(xyz,P,'numpy') for P in polys]
    F=lambda t:asinh(t)-sqrt(1+t*t)/t
    def value(X):
        T,*v,z=X;t=brentq(lambda t:F(t)-T,.5,14);Y=z-1/t;r=np.linalg.norm(v)
        wt=basis(Tn,T);wy=basis(Yn,Y);H=np.zeros((5,5))
        if common:
            A=np.einsum('a,b,abk->k',wt,wy,hist[0]);k=nodes
            U=[np.dot(A,k**4*c*spherical_jn(l,k*r)/r**l) for l,c in zip((0,2,4),(.4,-4/7,1/35))]
        else:U=np.einsum('a,b,c,qabc->q',wt,wy,basis(nodes,r),hist)/eps**np.arange(0,6,2)
        H[1:4,1:4]=sum(f(*v)*a for f,a in zip(fun,U));return H/z**2
    return value


def diagnostics(value,X,h=1e-5):
    eye=np.eye(5)*h;H=value(X);d=np.array([(value(X+e)-value(X-e))/(2*h) for e in eye]);dd=np.empty((5,5,5,5))
    for i,e in enumerate(eye):
        dd[i,i]=(value(X+e)-2*H+value(X-e))/h**2
        for j,f in enumerate(eye[:i]):dd[i,j]=dd[j,i]=(value(X+e+f)-value(X+e-f)-value(X-e+f)+value(X-e-f))/(4*h*h)
    Q,L,div=ricci_jet(H,d,dd,X[-1]);return np.array([np.linalg.norm(a) for a in (H,Q,L,div)]),Q


def run():
    obstruction();xyz,polys=angular();F=lambda t:asinh(t)-sqrt(1+t*t)/t
    X=np.r_[F(11.8),2.52*np.array([2.,3.,6.])/7,1/11.8+.06]
    for n,ny,dt in [(270,71,.0025),(540,71,.00125),(270,141,.0025),(270,71,.00125)]:
        for common in (False,True):
            H,meta=evolve(n,ny,dt,common);v=make_evaluator(H,meta,common,xyz,polys);a,Q=diagnostics(v,X);b,_=diagnostics(v,X,2e-5)
            assert np.isfinite(a).all() and np.allclose(Q,Q.T,atol=1e-12)
            print(n,ny,dt,'common' if common else 'native','h Q linear div',a,'jet step difference',np.abs(a-b),flush=True)
if __name__=='__main__':run()

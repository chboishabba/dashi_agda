"""P0AF independent controls: bounded discontinuous current, zero mode,
retarded support and ADM Hamiltonian. Not original curved dependency replay."""
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.special import exprel


def hybrid(N):
    # Orthonormal real Fourier basis on [-pi,pi], even electric / odd magnetic.
    # Unit box current on [-a,a], including its nonzero constant mode.
    a=.7; k=np.arange(1,N+1); J=np.r_[2*a/np.sqrt(2*np.pi),2*np.sin(k*a)/(k*np.sqrt(np.pi))]
    def rhs(t,y):
        e=y[:N+1]; b=y[N+1:2*N+1]; n=y[-3:-1]; v=J@e
        m=.4*(n[0]/exprel(-v)-n[1]/exprel(v))
        diss=m*(np.log(n[0]/n[1])+v)
        return np.r_[np.r_[0.,k*b]-J*m,-k*e[1:],-m,m,diss]
    y0=np.r_[np.zeros(2*N+1),1.8,.2,0.]
    sol=solve_ivp(rhs,(0,2),y0,method='DOP853',rtol=2e-10,atol=2e-12,t_eval=np.linspace(0,2,41))
    assert sol.success
    y=sol.y; n=y[-3:-1]; assert n.min()>0
    U=.5*np.sum(y[:2*N+1]**2,axis=0)+np.sum(n*(np.log(n)-1),axis=0)
    err=np.max(abs(U-U[0]+y[-1])); assert err<1e-8 and np.max(abs(n.sum(axis=0)-2))<1e-10
    assert np.min(np.diff(y[-1]))>=-1e-10 and abs(y[0,-1])>1e-4
    print('hybrid',N,'min amount',n.min(),'energy closure',err,'zero mode',y[0,-1])
    return y[:N+1,-1],y[N+1:2*N+1,-1],n[:,-1]


def retarded():
    # Exact d'Alembert characteristic integration for unit box [-1,1]
    # source switched on at t=0, initially zero, on the noncompact line.
    R=s.Rational
    def overlap(l,r):return max(0,min(r,1)-max(l,-1))
    def field(x,t):
        p=overlap(x,x+t); m=overlap(x-t,x)
        return -(p+m)/2,(m-p)/2
    for t in map(R,[0,1,2,3]):
        for x in (R(-9,2),R(-3),R(-2),R(0),R(2),R(3),R(9,2)):
            if abs(x)>=1+t: assert field(x,t)==(0,0)
    assert field(R(2),R(1,2))==(0,0)
    assert field(R(2),R(2))==(R(-1,2),R(1,2))
    print('retarded compact-source support PASS (exact rational, 1D flat control)')


def adm():
    a=s.symbols('alpha',positive=True); d=s.Matrix(s.symbols('d:3')); b=s.Matrix(s.symbols('b:3')); beta=s.Matrix(s.symbols('beta:3'))
    H=a*(d.dot(d)+b.dot(b))/2-beta.dot(d.cross(b))
    assert s.Matrix([s.diff(H,x) for x in d])==a*d+beta.cross(b)
    assert s.Matrix([s.diff(H,x) for x in b])==a*b-beta.cross(d)
    u=s.Matrix(s.symbols('u:6')); v=s.Matrix(s.symbols('v:6')); K=s.hessian(H,list(d)+list(b))
    assert K==K.T
    assert s.expand((v.T*K*v-u.T*K*u)[0]/2-((v+u).T*K*(v-u))[0]/2)==0
    # Nonzero shift cross term can destroy coordinate energy coercivity.
    assert H.subs(dict(zip(list(d)+list(b)+list(beta)+[a],[1,0,0,0,1,0,0,0,2,1])))==-1
    print('ADM Hamiltonian adjoints, midpoint chain rule and superluminal-shift counterexample PASS')


if __name__=='__main__':
    ref=hybrid(128); errors=[]
    for N in (8,16,32,64):
        e,b,n=hybrid(N); er,br,nr=ref
        err=np.sqrt(np.linalg.norm(e-er[:N+1])**2+np.linalg.norm(b-br[:N])**2+np.linalg.norm(er[N+1:])**2+np.linalg.norm(br[N:])**2+np.linalg.norm(n-nr)**2)
        errors.append(err); print('embedded endpoint error',N,err)
    assert all(x>y for x,y in zip(errors,errors[1:]))
    retarded(); adm()

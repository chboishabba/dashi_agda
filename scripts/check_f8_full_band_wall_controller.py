"""Full finite-band controller and wall-source consumer, original F8 coefficient action.
K input, 2K charge, 3K stress. No continuum acceptance.
"""
import numpy as np
from scipy.interpolate import CubicSpline
from scipy.integrate import solve_ivp
from scipy.special import roots_legendre
from check_f8_characteristic_history import evolve, coefficient, bump
from check_f8_nonzero_convolution import project, tri
from check_f8_wall_fourier_gauss import ordered

Q=np.diag([0.,1.,-1.])
REPS=[np.diag([-1.,-1.,2.])/np.sqrt(6),
      np.array([[0.,0.,1.],[0.,0.,0.],[1.,0.,0.]])/np.sqrt(2),
      np.diag([1.,-1.,0.])/np.sqrt(2)]

def sectors(n,Q):
    z=n@Q@n
    a=1.5*z*z; b=2*((Q@n)@(Q@n)-z*z)
    return np.array([a,b,np.sum(Q*Q)-a-b])

def triangles(k,P,C,nodes):
    a,w=roots_legendre(nodes)
    if k==0:
        for p,wp in zip(min(P,C)*(a+1)/2,w*min(P,C)/2):
            for c,wc in zip(a,w):
                for phi in 2*np.pi*np.arange(16)/16:
                    v=p*np.array([np.sqrt(1-c*c)*np.cos(phi),np.sqrt(1-c*c)*np.sin(phi),c])
                    yield v,-v,wp*wc*p*p/(4*np.pi**2*16)
        return
    edges=sorted(set([0.,P]+[v for v in (k,abs(k-C),k+C) if 0<v<P]))
    for l,r in zip(edges,edges[1:]):
        for p,wp in zip(l+(r-l)*(a+1)/2,(r-l)*w/2):
            lo=abs(k-p);hi=min(k+p,C)
            if hi<=lo:continue
            for q,wq in zip(lo+(hi-lo)*(a+1)/2,(hi-lo)*w/2):
                pp,qq=tri(k,p,q)
                for v,u in zip(pp,qq):yield v,u,wp*wq*p*q/(4*np.pi**2*k*len(pp))

class History:
    def __init__(self,K=40,cells=128,nh=16,nodes=4,end=1.05):
        self.K=K;self.nodes=nodes
        self.kh=K*(1-np.cos(np.linspace(0,np.pi,nh)))/2
        t,_,_,h,ht,_=evolve(self.kh,np.ones(nh),cells,end)
        self.h=CubicSpline(t,h,axis=0);self.ht=CubicSpline(t,ht,axis=0)
        self.kr=2*K*(1-np.cos(np.linspace(0,np.pi,2*nh-1)))/2
        a,w=roots_legendre(nodes);r=K*(a+1)/2;rw=K*w/2
        self.r=r;self.w0=rw*r*r*coefficient(r)**2/(5*np.pi**2)
        self.tables=[]
        for k in self.kr[1:]:
            qq=[];ww=[]
            for p,q,weight in triangles(k,K,K,nodes):
                rp,rq=np.linalg.norm(p),np.linalg.norm(q)
                c=coefficient(np.array([rp,rq])).prod()
                qq.append(rq)
                ww.append(weight*c*np.array([np.sum(project(S,p)*project(S,q)) for S in REPS]))
            self.tables.append((np.array(qq),np.array(ww).reshape(-1,3)))
        scale=1e8; N=len(self.kr)
        def rhs(t,y):
            ip=CubicSpline(self.kh,self.h(t))
            Z=np.zeros((N,3));Z[0]=self.w0@ip(self.r)
            for j,(q,W) in enumerate(self.tables,1):Z[j]=W.T@ip(q)
            B,V=y.reshape(2,N,3)
            return np.stack([V,2*scale*bump(t)*Z-3*V/t-self.kr[:,None]**2*B/t**2]).ravel()
        sol=solve_ivp(rhs,(1,end),np.zeros(6*N),rtol=1e-9,atol=1e-12,dense_output=True,method='DOP853')
        assert sol.success
        self.ctrl=lambda t:sol.sol(t).reshape(2,N,3)/scale
    def known_ward(self,t,k,Qrot=None,muS=0.):
        """Complete source-owned T, effective Israel C and all four Ward rows.
        Use this rather than legacy wall() when coupling scalar/vector sectors.
        muS is the actual shear coefficient times controller S; supply it explicitly.
        """
        from check_f8_full_band_ward_attachment import assemble
        return assemble(self,t,k,muS=muS,Qrot=Qrot)

    def wall(self,t,k,Q=Q):
        """Legacy projected diagnostic; not a complete four-component Ward source."""
        """Actual coefficient-level known stress/Ward and elastic/charge split."""
        K=self.K;b=1/t;w=b**4/12;clock=b*b/(3*np.sqrt(1+b*b))-w
        h=CubicSpline(self.kh,self.h(t)); ht=CubicSpline(self.kh,self.ht(t))
        htt=CubicSpline(self.kh,self.ht(t,1))
        def mode(p):
            r=np.linalg.norm(p); E=project(Q,p)
            c=coefficient(np.array([r]))[0]
            return c*h(r)*E,c*ht(r)*E,c*htt(r)*E,c*bump(t)*E
        T=np.zeros((4,4),complex); C=T.copy(); R=np.zeros(4,complex)
        curvature=0j; ctrl=np.zeros((3,3))
        for p,q,wt in triangles(k,K,K,self.nodes):
            H,Ht,Htt,P=mode(p);G,Gt,Gtt,Pq=mode(q)
            df=w*np.trace(H@G)/4;d=np.trace(H@Pq)/2
            T[0,0]+=wt*(-df+d);T[1:,1:]+=wt*((df/3+d)*np.eye(3)-H@Pq)
            C[0,0]+=wt*(3*df-d);C[1:,1:]-=wt*(df+d)*np.eye(3)
            R[0]+=wt*(clock*np.trace(H@Gt)/2+np.trace(H@Pq)*(2*b)/2)
            # Pq time derivative uses original source profile, not finite difference of H.
            from check_f8_wall_fourier_gauss import spatial
            curvature+=wt*(spatial(p,H,q,G)*b*b-np.trace(H@Gtt)-.75*np.trace(Ht@Gt)-4*b*np.trace(H@Gt))
        # Complete clock forcing: add P_t term with independent source-clock derivative.
        # Differentiate analytic bump on its open support.
        F=lambda a:np.arcsinh(a)-np.sqrt(1+a*a)/a
        x=2*(F(t)-F(1))/.065-1
        ratio=-2*x/(1-x*x)**2*2*np.sqrt(1+t*t)/(t*t)/.065 if abs(x)<1 else 0.
        R[0]+=ratio*sum(wt*np.trace(mode(p)[0]@mode(q)[3])/2 for p,q,wt in triangles(k,K,K,self.nodes))
        # Spatial Ward is divergence of known stress minus the TT connection term.
        for p,q,wt in triangles(k,K,K,self.nodes):
            H,_,_,_=mode(p);Pq=mode(q)[3]
            R[1:]-=wt*1j*p*np.trace(Pq@H)/2
        B=CubicSpline(self.kr,self.ctrl(t)[0],axis=0)
        for p,q,wt in triangles(k,K,2*K,self.nodes):
            r=np.linalg.norm(q); v=np.linalg.norm(p)
            charge=B(r)@sectors(q/r,Q) if r else B(0)[0]*np.sum(Q*Q)
            ctrl+=wt*charge*coefficient(np.array([v]))[0]*bump(t)*project(Q,p)
        T[1:,1:]+=ctrl;C[1:,1:]-=3*ctrl
        R[1:]+=1j*k*T[3,1:]
        # Elastic term per mu*S (kept separate to preserve original amplitude ceiling).
        elastic=-mode(np.array([0.,0.,k]))[0] if 0<k<=K else np.zeros((3,3))
        return T,C,R,curvature,ctrl,elastic

def run():
    H=History()
    assert np.max(abs(H.ctrl(1)))==0
    assert np.max(abs(H.ctrl(1.035)[0][-1]))<1e-20
    rows=[]
    for k in (0.,30.,60.,90.,120.):
        T,C,R,G,A,E=H.wall(1.035,k)
        assert np.isfinite(np.r_[T.ravel(),C.ravel(),R,G,A.ravel(),E.ravel()]).all()
        if k>2*H.K:
            assert G==0 and np.linalg.norm(T[1:,1:]-A)<1e-14
        if k==3*H.K:assert np.linalg.norm(A)<1e-20
        rows.append((k,float(np.linalg.norm(T)),float(np.linalg.norm(A)),float(abs(G)),float(np.linalg.norm(R))))
    assert rows[3][2]>0
    print('k,stress,controller,curvature,Ward',rows,flush=True)
if __name__=='__main__':run()

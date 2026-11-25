"""Distributed radial-shell port and goal dual. Normalized source fixtures only.
Transcribed XCIII/XCIV/XCV and layered-shell donors; no physical calibration.
"""
import numpy as np
import sympy as sp
from itertools import product
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
import json
R=6371000.;ht=110000.;mu=4*np.pi*1e-7;eps=8.8541878128e-12;ya=1/(mu*1e6);yg=.1
edges=[(1,4),(2,5),(0,1),(1,2),(3,4),(4,5),(0,3)]
D=np.array([[1,0,1,0,-1,0,-1],[-1,1,0,1,0,-1,0]])
G=np.zeros((7,6));
for i,(a,b) in enumerate(edges):G[i,a]=-1;G[i,b]=1
assert not np.any(D@G)
Q=[np.diag([1,-1,0])/np.sqrt(2),np.diag([1,1,-2])/np.sqrt(6)]
for i,j in ((0,1),(0,2),(1,2)):
    q=np.zeros((3,3));q[i,j]=q[j,i]=1/np.sqrt(2);Q.append(q)
Q=np.array(Q);axis=np.ones(3)/np.sqrt(3)
def angular(n):
    X=np.cross(n,np.eye(3)).T;P=np.eye(3)-np.outer(n,n);q=np.einsum('kij,j->ik',Q,n)
    return np.column_stack((np.sqrt(1.5)*X,np.sqrt(1.5)*P,np.sqrt(5)*X@q,np.sqrt(5)*P@q))
Gram=np.zeros((16,16));K=Gram.copy();J=Gram.copy()
for p in product((-1,0,1),repeat=3):
    nn=sum(x!=0 for x in p)
    if not nn:continue
    n=np.array(p)/np.sqrt(nn);w={1:1/21,2:4/105,3:9/280}[nn];B=angular(n);X=np.cross(n,np.eye(3)).T
    Gram+=w*B.T@B;K+=w*(axis@n)*B.T@B;J+=w*B.T@X@B
assert np.max(abs(Gram-np.eye(16)))<1e-14
# Preserve source edge ordering and exact degree-one/two line integrals.
def trace(v):
    rows=[]
    for a,b in edges:
        n,t=v[a],v[b];cross=np.cross(n,t);length=np.linalg.norm(cross);u=cross/length;theta=np.arctan2(length,n@t)
        delta=t-n;summ=t+n;delta[2]=-(delta[:2]@summ[:2])/summ[2]
        tor=-np.tan(theta/2)*np.einsum('i,kij,j->k',u,Q,summ);pol=np.einsum('i,kij,j->k',delta,Q,summ)/2
        rows.append(np.r_[np.sqrt(1.5)*np.r_[-theta*u,delta],np.sqrt(5)*np.r_[tor,pol]])
    T=np.array(rows);assert np.max(abs(D@T[:,[3,4,5,11,12,13,14,15]]))<1e-14
    return T
def geometry(area,spread):
    target=area/R**2;solid=lambda y:4*np.arctan(y*y/np.sqrt(1+2*y*y));y=brentq(lambda y:solid(y)-target,0,2*np.sqrt(target),xtol=1e-25)
    v=np.array([[a,b,1.] for b in (-y,y) for a in (-y,0,y)]);v/=np.linalg.norm(v,axis=1)[:,None]
    if spread==0:return [R],[trace(v)]
    def rot(a,b):
        ca,sa,cb,sb=np.cos(a),np.sin(a),np.cos(b),np.sin(b)
        return np.array([[cb,0,sb],[0,1,0],[-sb,0,cb]])@np.array([[1,0,0],[0,ca,-sa],[0,sa,ca]])
    T=sum(trace(v@rot(a*y*spread,b*y*spread).T) for a,b in product((-1,0,1),repeat=2))/27
    return [R,R+spread*np.sqrt(area),R+2*spread*np.sqrt(area)],[T]*3
# Original XCV off-guard circuit and seven-edge finite return.
q=sp.Rational;Mi=sp.Matrix([[2,q(3,5)],[q(3,5),q(3,2)]]);Mc=sp.Matrix([[q(7,5),-1],[-1,q(31,20)]])
z=sp.Matrix(sp.symbols('i j u v b p r ih x'));i,j,u,v,b,p,r,ih,x=z
f=(Mi.inv()*sp.Matrix([-q(35,100)*i,u-v-q(28,100)*j])).col_join(Mc.inv()*sp.Matrix([-j+q(35,100)*p+2*ih,j])).col_join(sp.Matrix([-q(18,1000)*b/q(65,100),q(11,10)*r-q(2,10000)*p-q(35,100)*u/2,-q(11,10)*p-q(2,10000)*r,(-x-q(5,100)*ih-2*u)/q(15,100),(ih-q(52,100)*x)/q(12,100)]))
Ac=f.jacobian(z);Kc=sp.zeros(2,9);Kc[0,5]=Kc[1,6]=1
W=sp.diag(Mi,Mc,q(65,100),2,2,q(15,100),q(12,100));loss=sp.diag(q(35,100),q(28,100),0,0,q(18,1000),q(4,10000),q(4,10000),q(5,100),q(52,100));assert Ac.T*W+W*Ac==-2*loss
Ac,Kc,loss=map(lambda a:np.array(a,float),(Ac,Kc,loss));L=np.eye(7)[:,:2];beta=10*np.sqrt(.03)
def native(f):
    w=f/7.83;E=L.T;h=-D/(1.5j*w);p=1.5*E/(4-w*w+2j*w/3);v=1j*w*p
    c=np.linalg.solve(1j*w*np.eye(9)-Ac,beta*Kc.T@E/2);jc=beta*Kc@c
    mass=np.diag([2,2,.1,.1,1,1,1]);C=np.diag([.2,.2,20/9,20/9,1,1,1]);disp=mass+L@p
    Y=C+L@jc+1j*w*disp-D.T@h
    return Y,np.sqrt(.52)*c[-1],c,v,C,disp

def transfer(f,a,b,n):
    w=2*np.pi*f;mats=[]
    for ell,typ,count in [(1,'TE',3),(1,'TM',3),(2,'TE',5),(2,'TM',5)][:2 if n==6 else 4]:
        LL=ell*(ell+1);M=np.eye(2,dtype=complex)
        for lo,hi,sg in ((max(a,R),min(b,R+ht/2),0),(max(a,R+ht/2),min(b,R+ht),1e-9)):
            if hi<=lo:continue
            aa=sg+1j*w*eps
            def mat(r):
                a,b=(1j*w*mu,aa+LL/(1j*w*mu*r*r)) if typ=='TE' else (1j*w*mu+LL/(aa*r*r),aa)
                return np.array([[0,-a*ya],[-b/ya,0]],complex)
            sol=solve_ivp(lambda r,t:(mat(r)@t.reshape(2,2)).ravel(),(lo,hi),np.eye(2,dtype=complex).ravel(),rtol=2e-11,atol=2e-12);assert sol.success;M=sol.y[:,-1].reshape(2,2)@M
        mats += [M]*count
    A,B,C,D=[np.diag([m[i,j] for m in mats]) for i,j in ((0,0),(0,1),(1,0),(1,1))]
    return np.block([[A,B],[C,D]])

def model(f,area,spread,n):
    radii,ts=geometry(area,spread);ts=[t[:,:n] for t in ts];I=np.eye(n);w=f/7.83;S=2*(I+.5*K[:n,:n])+J[:n,:n]+1j*w*1.5/(4-w*w+1j*2*w/3)*I;U=I+S
    P=[transfer(f,a,b,n) for a,b in zip(radii,radii[1:]+[R+ht])]
    Y,t,c,p,C,disp=native(f)
    assert min(np.linalg.eigvalsh((Y+Y.conj().T)/2))>0
    def walk(a,i):
        e=a.copy();h=-yg*a;v=np.zeros((7,a.shape[1]),complex);rad=np.zeros(a.shape[1]);work=rad.copy()
        for T,F in zip(ts,P):
            v+=T@e;h=h-T.T@i;work+=np.sum((e.conj()*(T.T@i)).real,axis=0)
            before=np.sum((e.conj()*h).real,axis=0);e,h=np.split(F@np.vstack((e,h)),2);rad+=before-np.sum((e.conj()*h).real,axis=0)
        return U@e-h,v,e,h,rad,work
    a=np.eye(n);i=np.zeros((7,n));A,C0,*_=walk(a,i)
    B,H,*_=walk(np.zeros((n,7)),np.eye(7)); # top Ue-h response, v response to load current
    Z=C0@np.linalg.solve(A,B)-H;V=C0@np.linalg.solve(A,2*I)
    assert min(np.linalg.eigvalsh((Z+Z.conj().T)/2))>-1e-13
    if spread==0:
        F0=P[0];aa,bb,cc,dd=F0[:n,:n],F0[:n,n:],F0[n:,:n],F0[n:,n:]
        M0=U@(aa-bb*yg)-(cc-dd*yg);Z0=np.linalg.solve(M0,dd-U@bb);V0=np.linalg.solve(M0,2*I)
        assert np.max(abs(Z-ts[0]@Z0@ts[0].T))<1e-10 and np.max(abs(V-ts[0]@V0))<1e-10
    F=np.block([[A,B@Y],[-C0,np.eye(7)-H@Y]])
    return F,Z,V,walk,S,Y,t,c,p,C,disp
rows=[]
for f in (.005,.05,3.915,7.83):
 for area in (1e6,1e10):
  for spread in (0.,.1):
    n=16;F,Z,V,walk,S,Y,t,c,p,C,disp=model(f,area,spread,n);F6,*_=model(f,area,spread,6)
    source=np.eye(n)[:,[0,4]];rhs=np.vstack((2*source,np.zeros((7,2))));x=np.linalg.solve(F,rhs);a,v=x[:n],x[n:];i=Y@v
    assert np.max(abs(v-np.linalg.solve(np.eye(7)+Z@Y,V@source)))<1e-10
    top,vr,e,h,rad,work=walk(a,i);ref=np.sum(abs(e-source)**2,axis=0);sheet=np.sum((e.conj()*(S@e)).real,axis=0);ground=yg*np.sum(abs(a)**2,axis=0);load=np.sum((v.conj()*i).real,axis=0)
    useful=abs(t@v)**2;heat=np.sum((v.conj()*(C@v)).real,axis=0)+4/9*np.sum(abs(p@v)**2,axis=0)+np.sum(((c@v).conj()*(loss@c@v)).real,axis=0)-useful
    err=max(np.max(abs(1-ref-sheet-ground-rad-load)),np.max(abs(load-useful-heat)),np.max(abs(work-load)))
    assert err<1e-8 and np.min(rad)>-1e-10
    # Goal-oriented dual: coarse solution + signed residual, exact fine adjoint.
    keep=np.r_[np.arange(6),np.arange(n,n+7)];block_defect=np.linalg.norm(F6-F[np.ix_(keep,keep)])
    xc=np.zeros_like(x);xc[keep]=np.linalg.solve(F6,rhs[keep]);r0=rhs-F@xc
    goal=np.r_[np.zeros(n),t];dual=np.linalg.solve(F.conj().T,goal.conj());dual0=np.zeros(n+7,complex);dual0[keep]=np.linalg.solve(F6.conj().T,goal[keep].conj())
    assert np.max(abs(goal@(x-xc)-dual.conj()@r0))<1e-10
    # Eliminated radial state does not generally commute with angular truncation.
    sv=np.linalg.svd(F,compute_uv=False)[-1];bound=np.linalg.norm(goal)*np.linalg.norm(r0,axis=0)/sv;actual=abs(goal@(x-xc));assert np.all(actual<=bound+1e-10)
    correction=dual0.conj()@r0;dr=goal.conj()-F.conj().T@dual0;radius=np.linalg.norm(dr)*np.linalg.norm(r0,axis=0)/sv
    assert np.all(abs(goal@(x-xc)-correction)<=radius+1e-10)
    # Exact signed Schur elimination from the full 16-mode carrier.
    omit=np.arange(6,n);E=F[np.ix_(keep,keep)];B1=F[np.ix_(keep,omit)];C1=F[np.ix_(omit,keep)];D1=F[np.ix_(omit,omit)]
    S1=E-B1@np.linalg.solve(D1,C1);rhs1=rhs[keep]-B1@np.linalg.solve(D1,rhs[omit]);xr=np.linalg.solve(S1,rhs1)
    assert np.max(abs(xr-x[keep]))<1e-10
    assert np.max(abs(np.linalg.solve(D1,rhs[omit]-C1@xr)-x[omit]))<1e-10
    w=f/7.83;assert np.max(abs(G.T@(1j*w*disp@v+C@v+L@(beta*Kc@c@v)-i)))<1e-10
    # Source-off no initial field: homogeneous system only.
    assert not np.any(np.linalg.solve(F,np.zeros(n+7)))
    rows.append(dict(f=f,area=area,spread=spread,useful=useful.tolist(),min_port_hermitian=float(np.linalg.eigvalsh((Z+Z.conj().T)/2)[0]),ledger=float(err),dual_error=float(np.max(abs(goal@(x-xc)-dual.conj()@r0))),goal_actual=actual.tolist(),global_bound=bound.tolist(),dual_corrected_bound=(abs(correction)+radius).tolist(),block_defect=float(block_defect),schur_defect=float(np.linalg.norm(S1-F6))))
print(json.dumps(dict(status='CONDITIONAL_DISTRIBUTED_LAYERED_SHELL',rows=rows,physical_admission=False),indent=2))

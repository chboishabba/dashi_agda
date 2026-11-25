"""S2/S4 finite aperture, degree-2 exterior and current-budget inverse.
Arguments: pinned finite aperture and metric-charge checkers. Conditional shell,
ideal zero-work clamp, normalized currents, not physical conductor or calibration.
"""
import sys, hashlib, json
from pathlib import Path
from itertools import product
import numpy as np
from scipy.optimize import brentq
from scipy.integrate import solve_ivp

def blob(p):
    b=Path(p).read_bytes();return hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
p,m=sys.argv[1:3]
assert blob(p)=='06d683bd2dfd24d4ad9de0620ef3718001fdbe36'
assert blob(m)=='1f3ee2625ede999147386b8f94e9078d29c94e65'
old=sys.argv;sys.argv=[p,m];d={};exec(compile(Path(p).read_text().split('\nrows=[]')[0],p,'exec'),d);sys.argv=old
R,ht,mu,eps,ya,yg=[d[k] for k in ('R','height','mu','eps','ya','yg')]
# STF basis with Frobenius norm 1; original tangent l=2 normalization sqrt(5).
Q=[np.diag([1,-1,0])/np.sqrt(2),np.diag([1,1,-2])/np.sqrt(6)]
for i,j in ((0,1),(0,2),(1,2)):
    q=np.zeros((3,3));q[i,j]=q[j,i]=1/np.sqrt(2);Q.append(q)
Q=np.array(Q);ax=np.ones(3)/np.sqrt(3)
def angular(n):
    X=np.cross(n,np.eye(3)).T;P=np.eye(3)-np.outer(n,n);q=np.einsum('kij,j->ik',Q,n)
    return np.column_stack((np.sqrt(1.5)*X,np.sqrt(1.5)*P,np.sqrt(5)*X@q,np.sqrt(5)*P@q))
G=np.zeros((16,16));K=G.copy();J=G.copy()
for site in product((-1,0,1),repeat=3):
    nn=sum(x!=0 for x in site)
    if not nn:continue
    n=np.array(site)/np.sqrt(nn);w={1:1/21,2:4/105,3:9/280}[nn];B=angular(n);X=np.cross(n,np.eye(3)).T
    G+=w*B.T@B;K+=w*(ax@n)*B.T@B;J+=w*B.T@X@B
assert np.max(abs(G-np.eye(16)))<1e-14
assert np.max(abs(K-K.T))<1e-14 and np.max(abs(J+J.T))<1e-14
assert np.max(abs(K[:6,:6]-d['K']))<1e-14 and np.max(abs(J[:6,:6]-d['J']))<1e-14
# Degree <=7 angular products exact by prior OCT369 receipt. l=3+ still omitted.
def overlap(area,aspect,N):
    T,_=d['overlap'](area,aspect)
    if N==6:return T
    target=area/R**2
    def solid(y):return 4*np.arctan(aspect*y*y/np.sqrt(1+(aspect*aspect+1)*y*y))
    y=brentq(lambda y:solid(y)-target,0,2*np.sqrt(target/aspect),xtol=1e-25);x=aspect*y
    v=np.array([[a,b,1.] for b in (-y,y) for a in (-x,0,x)]);v/=np.linalg.norm(v,axis=1)[:,None]
    rows=[]
    for a,b in d['env']['edges']:
        n,t=v[a],v[b];cross=np.cross(n,t);u=cross/np.linalg.norm(cross);theta=np.arctan2(np.linalg.norm(cross),n@t)
        delta=t-n;delta[2]=-(delta[:2]@(t[:2]+n[:2]))/(t[2]+n[2]);summ=t+n
        tor=-np.tan(theta/2)*np.einsum('i,kij,j->k',u,Q,summ)
        pol=np.einsum('i,kij,j->k',delta,Q,summ)/2
        rows.append(np.sqrt(5)*np.r_[tor,pol])
    T=np.column_stack((T,rows));assert np.max(abs(d['env']['D']@T[:,11:]))<1e-14
    return T

def shell(f,N):
    w=2*np.pi*f; mats=[]
    for ell,typ,count in [(1,'TE',3),(1,'TM',3)]+([(2,'TE',5),(2,'TM',5)] if N==16 else []):
        L=ell*(ell+1);M=np.eye(2,dtype=complex)
        for r0,r1,sg in ((R,R+ht/2,0),(R+ht/2,R+ht,1e-9)):
            aa=sg+1j*w*eps
            def mat(r):
                a,b=(1j*w*mu,aa+L/(1j*w*mu*r*r)) if typ=='TE' else (1j*w*mu+L/(aa*r*r),aa)
                return np.array([[0,-a*ya],[-b/ya,0]],complex)
            sol=solve_ivp(lambda r,t:(mat(r)@t.reshape(2,2)).ravel(),(r0,r1),np.eye(2,dtype=complex).ravel(),rtol=2e-11,atol=2e-12)
            assert sol.success;M=sol.y[:,-1].reshape(2,2)@M
        mats += [M]*count
    A,B,C,D=[np.diag([M[i,j] for M in mats]) for i,j in ((0,0),(0,1),(1,0),(1,1))]
    z=f/7.83;I=np.eye(N);S=2*(I+.5*K[:N,:N])+J[:N,:N]+1j*z*1.5/(4-z*z+1j*2*z/3)*I;U=I+S
    M=U@(A-B*yg)-(C-D*yg);Z=np.linalg.solve(M,D-U@B);V=np.linalg.solve(M,2*I)
    return A,B,C,D,S,Z,V

def budget(T,Z,v,imax):
    H=(Z+Z.conj().T)/2;ev,U=np.linalg.eigh(H);assert min(ev)>0
    root=(U*np.sqrt(ev))@U.conj().T;inv=(U/np.sqrt(ev))@U.conj().T
    U,s,W=np.linalg.svd(root@T.conj().T,full_matrices=False);b=inv@v;g=U.conj().T@b
    # Work in singular coordinates; avoid inversion of normal matrix at small aperture.
    keep=s>s[0]*1e-12;g=np.where(keep,g,0);ss=np.where(keep,s,0)
    coeff=np.divide(g,2*s,out=np.zeros_like(g),where=keep)
    ideal=np.linalg.norm(g)**2/4;need=np.linalg.norm(coeff)
    if need<=imax:lam=0.;a=coeff
    else:
        def aof(l):return ss*g/(2*(ss**2+l))
        # solve in log lambda to cover curvature scales
        lam=np.exp(brentq(lambda l:np.linalg.norm(aof(np.exp(l)))/imax-1,-200,100,xtol=1e-12));a=aof(lam)
    i=W.conj().T@a;j=T.conj().T@i;power=np.vdot(i,T@(v-Z@j)).real
    p2=np.sum(np.real(np.conj(a)*ss*g)-ss**2*abs(a)**2)
    assert abs(power-p2)<2e-7*max(1,abs(p2))
    assert np.linalg.norm(i)<=imax*(1+1e-8) and power<=ideal+1e-7
    # dual upper certificate: P* <= lambda Imax² + sum |s*g|²/(4(s²+lambda))
    dual=ideal if lam==0 else lam*imax**2+np.sum(abs(ss*g)**2/(4*(ss**2+lam)))
    assert abs(p2-dual)<1e-10*max(1,abs(dual))
    return i,dict(power=float(p2),ideal=float(ideal),need=float(need),norm=float(np.linalg.norm(i)),lambda_=float(lam),dual_gap=float(abs(p2-dual)),rank=int(sum(keep)))
rows=[];checks=[]
for f in (.005,.05,3.915,7.83):
    Y=np.column_stack([d['native'](f,e)[0] for e in np.eye(4)])
    for N in (6,16):
        A,B,C,D,S,Z,V=shell(f,N);Zi=np.linalg.inv(Z)
        if N==6:
            prev=d['shell'](f);assert max(np.max(abs(x-y)) for x,y in zip((A,B,C,D,S,Z,V),prev))<1e-12
        for area in (1.,1e6,1e10):
          for aspect in (1.,1.5,(1+np.sqrt(5))/2):
            T=overlap(area,aspect,N);Ta,Tb=T[:4],T[4:];_,sb,vh=np.linalg.svd(Tb,full_matrices=True);rank=sum(sb>sb[0]*1e-12)
            for clamp in (False,True):
                F=vh[rank:].conj().T if clamp else np.eye(N);Zr=np.linalg.inv(F.conj().T@Zi@F);Tr=Ta@F
                for src in (0,4):
                    voc=V[:,src];vr=Zr@F.conj().T@Zi@voc
                    ar=np.linalg.solve(np.eye(F.shape[1])+Zr@Tr.conj().T@Y@Tr,vr);a=F@ar;i=Y@Ta@a;j=Zi@(voc-a);edge=Ta@a
                    _,useful,heat=d['native'](f,edge);load=np.vdot(edge,i).real
                    reaction=j-Ta.conj().T@i
                    if clamp:
                        assert np.linalg.norm(F.conj().T@reaction)<1e-9
                        assert np.linalg.norm(Tb@a)<1e-12
                    else:assert np.linalg.norm(reaction)<1e-9
                    h0=-yg*a-j;e1=A@a+B@h0;h1=C@a+D@h0;ei=np.eye(N)[:,src]
                    ref=np.linalg.norm(e1-ei)**2;sheet=np.vdot(e1,S@e1).real;ground=yg*np.vdot(a,a).real;rad=np.vdot(a,h0).real-np.vdot(e1,h1).real
                    err=1-ref-sheet-ground-rad-load;assert abs(err)<1e-9 and abs(load-useful-heat)<1e-9
                    # Constraint reaction has zero work, but current is not free resource.
                    react_work=np.vdot(a,reaction).real;assert abs(react_work)<1e-10
                    rnorm=np.linalg.norm(np.linalg.lstsq(Tb.T,reaction,rcond=1e-12)[0]) if clamp else 0.
                    budgets=[]
                    for limit in (1.,1e3,1e6,1e9):
                        ii,res=budget(Tr,Zr,vr,limit);aa=F@(vr-Zr@Tr.conj().T@ii);jj=Zi@(voc-aa);rr=jj-Ta.T@ii
                        res['clamp_current_norm']=float(np.linalg.norm(np.linalg.lstsq(Tb.T,rr,rcond=1e-12)[0])) if clamp else 0.
                        budgets.append(res)
                    rows.append(dict(f=f,N=N,area=area,aspect=aspect,src=src,clamp=clamp,load=load,useful=useful,err=err,react_work=react_work,clamp_current_norm=rnorm,unused_trace=np.linalg.norm(Tb@a),native_current=np.linalg.norm(i),higher_reflected=float(np.linalg.norm(e1[6:])**2),budgets=budgets))
print(json.dumps(dict(status='CONDITIONAL_L1_L2_CURRENT_BUDGET',cases=len(rows),budget_cases=4*len(rows),max_ledger=max(abs(r['err']) for r in rows),max_dual_gap=max(b['dual_gap'] for r in rows for b in r['budgets']),max_reaction_work=max(abs(r['react_work']) for r in rows),rows=rows),indent=2))

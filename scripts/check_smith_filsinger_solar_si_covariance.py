"""SI shell optimisation: original l<=2 layered TE/TM and seven-edge traces.
Conditional RMS source and current budgets; no calibrated natural source.
Donor equations: aperture_current_budget, finite_return_refinement, radial_shell.
"""
import json
import numpy as np
import sympy as sp
from itertools import product
from scipy.integrate import solve_ivp
from scipy.optimize import brentq
# Canonical SI.agda Dimension order L,M,T,I,Theta,N,J; derived EM dimensions.
V=sp.Matrix([2,1,-3,-1,0,0,0]); A=sp.Matrix([0,0,0,1,0,0,0]); L=sp.Matrix([1,0,0,0,0,0,0]); t=sp.Matrix([0,0,1,0,0,0,0]); W=sp.Matrix([2,1,-3,0,0,0,0])
assert V+A==W and V-A==sp.Matrix([2,1,-3,-2,0,0,0])
assert (V-L)+(A-L)==W-2*L and W+t==sp.Matrix([2,1,-2,0,0,0,0])
assert 2*V-(V-A)==W
# Source amplitude e=r E_t; h=r(H cross n)_t/ya; angular average normalized to 1.
R=6371000.;ht=110000.;mu=4*np.pi*1e-7;eps=8.8541878128e-12;ya=1/(mu*1e6);kappa=4*np.pi*ya;yg=.1
edges=[(1,4),(2,5),(0,1),(1,2),(3,4),(4,5),(0,3)]
D=np.array([[1,0,1,0,-1,0,-1],[-1,1,0,1,0,-1,0]])
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

def trace(area,aspect,angle):
    target=area/R**2;solid=lambda y:4*np.arctan(aspect*y*y/np.sqrt(1+(aspect*aspect+1)*y*y));y=brentq(lambda y:solid(y)-target,0,2*np.sqrt(target/aspect),xtol=1e-25)
    v=np.array([[a,b,1.] for b in (-y,y) for a in (-aspect*y,0,aspect*y)]);v/=np.linalg.norm(v,axis=1)[:,None]
    c,s=np.cos(angle),np.sin(angle);v=v@np.array([[c,s,0],[-s,c,0],[0,0,1]])
    rows=[]
    for a,b in edges:
        n,t=v[a],v[b];cross=np.cross(n,t);length=np.linalg.norm(cross);u=cross/length;theta=np.arctan2(length,n@t)
        delta=t-n;summ=t+n;delta[2]=-(delta[:2]@summ[:2])/summ[2]
        tor=-np.tan(theta/2)*np.einsum('i,kij,j->k',u,Q,summ);pol=np.einsum('i,kij,j->k',delta,Q,summ)/2
        rows.append(np.r_[np.sqrt(1.5)*np.r_[-theta*u,delta],np.sqrt(5)*np.r_[tor,pol]])
    T=np.array(rows);assert np.max(abs(D@T[:,[3,4,5,11,12,13,14,15]]))<1e-14
    return T

def shell(f):
    w=2*np.pi*f;mats=[]
    for ell,typ,count in [(1,'TE',3),(1,'TM',3),(2,'TE',5),(2,'TM',5)]:
        LL=ell*(ell+1);M=np.eye(2,dtype=complex)
        for lo,hi,sg in ((R,R+ht/2,0),(R+ht/2,R+ht,1e-9)):
            aa=sg+1j*w*eps
            def mat(r):
                a,b=(1j*w*mu,aa+LL/(1j*w*mu*r*r)) if typ=='TE' else (1j*w*mu+LL/(aa*r*r),aa)
                return np.array([[0,-a*ya],[-b/ya,0]],complex)
            sol=solve_ivp(lambda r,t:(mat(r)@t.reshape(2,2)).ravel(),(lo,hi),np.eye(2,dtype=complex).ravel(),rtol=2e-11,atol=2e-12);assert sol.success;M=sol.y[:,-1].reshape(2,2)@M
        mats += [M]*count
    A,B,C,D=[np.diag([m[i,j] for m in mats]) for i,j in ((0,0),(0,1),(1,0),(1,1))]
    I=np.eye(16);z=f/7.83;S=2*(I+.5*K)+J+1j*z*1.5/(4-z*z+1j*2*z/3)*I;U=I+S
    M=U@(A-B*yg)-(C-D*yg);Z=np.linalg.solve(M,D-U@B);V=np.linalg.solve(M,2*I)
    assert np.min(np.linalg.eigvalsh((Z+Z.conj().T)/2))>0
    return A,B,C,D,S,Z,V
# Conditional current budget: E ||i||^2 <= Imax^2 in physical amperes.
# Dual: maximize work-lambda*current^2 via covariance eigenvalue/Ky Fan.
# Use lambda>0 to regularize near-invisible port directions, not remove them.
def policy(H,V,probs,rank,limit):
    def at(lam):
        ev,U=np.linalg.eigh(H+lam*np.eye(7));assert min(ev)>0
        W=(U/np.sqrt(ev))@U.conj().T
        B=W@V;curr=[];dual=lam*limit**2;dirs=[]
        for p in probs:
            e,U=np.linalg.eigh((B*p)@B.conj().T);U=U[:,-rank:];P=U@U.conj().T
            curr.append(W@P@B/2);dual+=np.sum(e[-rank:])/(4*len(probs));dirs.append(P)
        norm=sum(np.sum(np.sum(abs(i)**2,axis=0)*p) for i,p in zip(curr,probs))/len(probs)
        work=sum(np.sum((np.sum((i.conj()*V).real,axis=0)-np.sum((i.conj()*(H@i)).real,axis=0))*p) for i,p in zip(curr,probs))/len(probs)
        return norm,work,dual,curr,dirs
    scale=max(np.linalg.norm(H,2),np.linalg.norm(V,2)/limit,1e-25)
    lo=scale*1e-14;hi=scale*1e4
    assert at(lo)[0]>limit**2 and at(hi)[0]<limit**2
    lam=np.exp(brentq(lambda l:at(np.exp(l))[0]/limit**2-1,np.log(lo),np.log(hi),xtol=1e-12))
    norm,work,dual,curr,dirs=at(lam)
    assert abs(norm/limit**2-1)<1e-6 and abs(dual-work)<1e-7*max(abs(dual),1e-30)
    return work,dual,curr,dirs,lam

rows=[];maxledger=0.;maxpair=0.
for f in (.005,.05,3.915,7.83):
    A,B,C,Dm,S,Z,V=shell(f)
    # Three synthetic equal-power states: TE_x, TE_y, TM_x, 1 W total modal incident per block.
    u=np.eye(16)[:,[0,1,3]]/np.sqrt(kappa);voc=V@u
    for area,aspect,angle in product((1.,1e6),(1.,1.5,(1+np.sqrt(5))/2,2.),(0.,np.pi/4,np.pi/2)):
        T=trace(area,aspect,angle);Zp=T@Z@T.T/kappa;H=(Zp+Zp.conj().T)/2;Vp=T@voc
        limit=.001;persist=.9;P=np.full((3,3),(1-persist)/2);np.fill_diagonal(P,persist)
        fixed=policy(H,Vp,[np.ones(3)/3],1,limit);track=policy(H,Vp,P,1,limit);full=policy(H,Vp,[np.ones(3)/3],7,limit)
        assert fixed[0]<=track[0]+1e-14 and track[0]<=full[0]+1e-14
        def ledger(sol,probs):
            global maxledger,maxpair
            natural=loss=work=0.
            for i,p in zip(sol[2],probs):
                j=T.T@i/kappa;e=voc-Z@j;h=-yg*e-j;e1=A@e+B@h;h1=C@e+Dm@h
                out=kappa*np.sum(abs(e1-u)**2,axis=0);natural_i=1-out
                sheet=kappa*np.sum((e1.conj()*(S@e1)).real,axis=0);ground=kappa*yg*np.sum(abs(e)**2,axis=0)
                radial=kappa*np.sum((e.conj()*h-e1.conj()*h1).real,axis=0)
                load=np.sum((i.conj()*(T@e)).real,axis=0)
                pair=kappa*np.sum((j.conj()*e).real,axis=0)
                maxpair=max(maxpair,np.max(abs(pair-load)))
                maxledger=max(maxledger,np.max(abs(natural_i-sheet-ground-radial-load)))
                assert np.min(radial)>-1e-10
                natural+=p@natural_i/len(probs);loss+=p@(sheet+ground+radial)/len(probs);work+=p@load/len(probs)
            assert abs(work-sol[0])<1e-12
            return natural,loss,work
        nf,lf,wf=ledger(fixed,[np.ones(3)/3]);na,la,wa=ledger(track,P);ledger(full,[np.ones(3)/3])
        assert abs((na-nf)-(la-lf)-(wa-wf))<1e-12
        # Count state changes as conservative switching rate (even if projectors coincide).
        gain=wa-wf
        rows.append(dict(f=f,area=area,aspect=aspect,angle_rad=angle,incident_W=1.,current_rms_limit_A=limit,fixed_W=wf,causal_W=wa,full_W=full[0],budget_W=gain,access_delta_W=na-nf,loss_delta_W=la-lf,max_cost_per_switch_J_at_1s=gain/(1-persist),dual_gap_W=max(abs(x[1]-x[0]) for x in (fixed,track,full))))
assert maxledger<1e-8 and maxpair<1e-12
# Independent loop threshold (uniform sinusoidal B; ideal match, no electric pickup).
# P=(2 pi f N A B)^2/(4R). No assumed environmental source from B alone.
loop=[]
for f in (3.915,7.83):
    for power in (1e-6,1.,7.3):
        loop.append(dict(f=f,target_W=power,B_rms_T_at_1m2turn_1ohm=np.sqrt(4*power)/(2*np.pi*f)))
print(json.dumps(dict(status='CONDITIONAL_SI_COVARIANCE',kappa_S=kappa,rows=rows,max_ledger_W=maxledger,max_pair_W=maxpair,loop=loop,physical_admission=False),indent=2))

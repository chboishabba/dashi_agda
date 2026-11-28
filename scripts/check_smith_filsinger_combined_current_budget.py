"""Combined active and clamp current budget for the pinned exterior fixture.
Arguments: current-budget checker, finite aperture checker, metric-charge checker.
All currents normalized, no calibrated conductor or physical boundary claim.
"""
import sys,hashlib,json
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
p,a,m=sys.argv[1:4]
raw=Path(p).read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='97d67fa9e4af6f61835f766fbe89994a922c48cc'
old=sys.argv;sys.argv=[p,a,m];d={};exec(compile(raw.decode().split('\nrows=[];checks=[]')[0],p,'exec'),d);sys.argv=old
rows=[]
for f in (.005,.05,3.915,7.83):
 for N in (6,16):
    *_,Z,V=d['shell'](f,N);H=(Z+Z.conj().T)/2;ev,U=np.linalg.eigh(H);assert min(ev)>0
    root=(U*np.sqrt(ev))@U.conj().T;inv=(U/np.sqrt(ev))@U.conj().T
    for area in (1.,1e6,1e10):
     for aspect in (1.,1.5,(1+np.sqrt(5))/2):
        T=d['overlap'](area,aspect,N);Tb=T[4:];_,sb,vh=np.linalg.svd(Tb,full_matrices=True);rank=int(sum(sb>sb[0]*1e-12));C=vh[:rank]
        B=C@Z@T.T;u,s,w=np.linalg.svd(B,full_matrices=True);rk=int(sum(s>s[0]*1e-12));F=w[rk:].conj().T
        assert rk==rank
        for src in (0,4):
            v=V[:,src];rhs=C@v;k0=w[:rk].conj().T@((u[:,:rk].conj().T@rhs)/s[:rk]);need=np.linalg.norm(k0)
            assert np.linalg.norm(B@k0-rhs)<1e-6
            assert np.linalg.norm(F.conj().T@k0)<1e-8*max(1,need)
            # Affine constraint k=k0+F x; exact orthogonality. The work
            # objective is constant plus linear term minus positive quadratic.
            b=inv@v;z0=root@T.T@k0;L=root@T.T@F
            U2,s2,W2=np.linalg.svd(L,full_matrices=False);keep=s2>s2[0]*1e-12;ss=np.where(keep,s2,0)
            g=np.where(keep,U2.conj().T@(b-2*z0),0)
            c0=np.vdot(z0,b).real-np.vdot(z0,z0).real
            coeff=np.divide(g,2*s2,out=np.zeros_like(g),where=keep)
            vals=[]
            for limit in (1.,1e3,1e6,1e9):
                if need>limit:vals.append(dict(limit=limit,feasible=False));continue
                radius=np.sqrt(max(0.,(limit-need)*(limit+need)))
                if radius==0:coef=np.zeros_like(g);lam=None
                elif np.linalg.norm(coeff)<=radius:coef=coeff;lam=0.
                else:
                    def fun(l):return ss*g/(2*(ss**2+l))
                    lam=np.exp(brentq(lambda l:np.linalg.norm(fun(np.exp(l)))/radius-1,-200,100,xtol=1e-12));coef=fun(lam)
                x=F@(W2.conj().T@coef);k=k0+x;field=v-Z@T.T@k
                power=c0+np.sum(np.real(np.conj(coef)*ss*g)-ss**2*abs(coef)**2)
                dual=c0+(np.linalg.norm(g)**2/4 if lam==0 else 0. if lam is None else lam*radius**2+np.sum(abs(ss*g)**2/(4*(ss**2+lam))))
                assert abs(power-dual)<1e-9*max(1,abs(dual))
                assert np.linalg.norm(k)<=limit*(1+1e-8)
                # A negative maximal power is not passive extraction.
                err=np.linalg.norm(C@field);direct=np.vdot(k,T@field).real
                assert err<1e-6 and abs(direct-power)<1e-6*max(1,abs(power))
                vals.append(dict(limit=limit,feasible=True,power=float(power),passive_positive=bool(power>0),norm=float(np.linalg.norm(k)),clamp_residual=float(err),dual_gap=float(abs(power-dual))))
            rows.append(dict(f=f,N=N,area=area,aspect=aspect,src=src,minimum_combined_current=float(need),min_constraint_residual=float(np.linalg.norm(B@k0-rhs)),cases=vals))
print(json.dumps(dict(status='CONDITIONAL_COMBINED_CURRENT_BUDGET',rows=len(rows),budget_cases=4*len(rows),feasible=sum(x['feasible'] for r in rows for x in r['cases']),positive=sum(x.get('passive_positive',False) for r in rows for x in r['cases']),max_min_constraint_residual=max(r['min_constraint_residual'] for r in rows),data=rows),indent=2))

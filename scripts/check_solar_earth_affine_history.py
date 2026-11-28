"""Affine future-work and signed history residual; no physical actuator model.
Usage: python check.py path/to/check_solar_earth_future_consumer.py path/to/PF_fig_PF.nc
"""
import hashlib,sys,json,itertools
from pathlib import Path
import sympy as s
import numpy as np
import xarray as xr
raw=Path(sys.argv[1]).read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='8a024a71503131fdfd9aaf4f422bcdd8307d7927'
# Consume the original finite fixture and its full prior assertions.
env={};exec(compile(raw,sys.argv[1],'exec'),env)
A,B=env['A'],env['B'];e=s.eye(5)
F=[a.row_join(d).col_join(e[4,:]) for a,d in [(A,s.Matrix([0,0,1,0])),(B,s.Matrix([1,0,0,0]))]]
ix=[(i,j) for i in range(5) for j in range(i,5)]
row=lambda q:s.Matrix([[q[i,j]*(1 if i==j else 2) for i,j in ix]])
vec=lambda c:s.Matrix([c[i,j] for i,j in ix])
Q=e[:,0]*e[0,:];W=e[:,1]*e[1,:]-e[:,2]*e[2,:];K=e[:,3]*e[3,:];one=e[:,4]*e[4,:]
def closure(forms):
    forms=list(forms); ranks=[len(forms)]
    while True:
        old=list(forms)
        for a in F:
            for h in old:
                g=a.T*h*a
                if s.Matrix.vstack(*(row(q) for q in forms+[g])).rank()>len(forms):forms.append(g)
        if len(forms)==len(old):break
        ranks.append(len(forms))
    R=s.Matrix.vstack(*(row(h) for h in forms));D=[]
    for a in F:
        P=s.Matrix.vstack(*(row(a.T*h*a) for h in forms));d=P*R.pinv();assert d*R==P;D.append(d)
    return R,D,ranks
R,D,ranks=closure([Q,W,one]);Rk,Dk,kranks=closure([Q,W,one,K])
assert R.rank()==10 and Rk.rank()==11
# Accumulated signed work, terminal storage and known affine source histories.
checks=0
for word in itertools.product(range(2),repeat=5):
    x=s.Matrix([1,2,-1,4,1]);y=s.Matrix([1,2,-1,9,1]);z=R*vec(x*x.T);acc=s.S.Zero
    for u in word:
        assert z[1]==(x.T*W*x)[0];acc+=z[1]
        x=F[u]*x;y=F[u]*y;z=D[u]*z
        assert z==R*vec(x*x.T)==R*vec(y*y.T);checks+=1
    assert (x.T*K*x)[0]!=(y.T*K*y)[0]
    assert Rk*vec(x*x.T)!=Rk*vec(y*y.T)
# Exact quadratic goal adjoint; arbitrary symmetric approximate moment history.
word=[0,1,0];X=[s.Matrix([1,2,3,4,1])];Y=[s.Matrix([0,2,3,4,1])]
for i,u in enumerate(word):
    X.append(F[u]*X[-1]);Y.append(F[u]*Y[-1]+e[:,i])
C=[x*x.T for x in X];E=[y*y.T for y in Y]
Z=[None]*4;Z[-1]=Q+K
for i in range(2,-1,-1):Z[i]=W+F[word[i]].T*Z[i+1]*F[word[i]]
tr=s.trace
actual=tr((Q+K)*(C[-1]-E[-1]))+sum(tr(W*(C[i]-E[i])) for i in range(3))
initial=tr(Z[0]*(C[0]-E[0]));terms=[tr(Z[i+1]*(F[u]*E[i]*F[u].T-E[i+1])) for i,u in enumerate(word)]
assert actual==initial+sum(terms)
# Original GAMERA selected keogram: audit ONLY the observed component product.
p=Path(sys.argv[2]);assert hashlib.sha256(p.read_bytes()).hexdigest()=='8ff495be1ebdd6609813061880b8faf08ac8365540e8ac2d2d64961c9b3b6880'
with xr.open_dataset(p,decode_cf=False) as ds:
    t=ds.tplt.values.ravel();a=ds.emrd_plts.values;b=ds.bphi_plts.values
assert a.shape==b.shape==(61,615)
# Weighted projection onto constant and fundamental on the original sample clock.
w=np.r_[np.diff(t)[0]/2,(t[2:]-t[:-2])/2,np.diff(t)[-1]/2];w=w/w.sum()
L=np.column_stack([np.ones(len(t)),np.cos(2*np.pi*t/200),np.sin(2*np.pi*t/200)])
project=lambda x:L@np.linalg.lstsq(np.sqrt(w)[:,None]*L,np.sqrt(w)[:,None]*x,rcond=None)[0]
a0,b0=project(a),project(b);da,db=a-a0,b-b0
inner=lambda x,y:np.sum(w[:,None]*x*y,axis=0)
scale=1e-12/(4*np.pi*1e-7)
full=inner(a,b)*scale;low=inner(a0,b0)*scale;res=inner(da,db)*scale
rad=np.sqrt(inner(da,da)*inner(db,db))*scale
err=float(np.max(abs(full-low-res)));assert err<1e-17
assert np.all(abs(res)<=rad+1e-17)
print(json.dumps(dict(status='AFFINE_WORK_QUOTIENT_AND_OBSERVED_COMPONENT_RESIDUAL',ranks=ranks,storage_ranks=kranks,word_step_checks=checks,adjoint=dict(goal_error=str(actual),initial=str(initial),residual_terms=list(map(str,terms))),keogram=dict(samples=list(a.shape),max_identity_error_W_m2=err,max_omitted_product_W_m2=float(max(abs(res))),max_bound_W_m2=float(max(rad)),strict_sign_certificates=int(sum(abs(low)>rad)),sign_reversals=int(sum(full*low<0))),physical_admission=False),indent=2))

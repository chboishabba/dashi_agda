"""S1 source admission: published summaries, exact cross-spectrum obstruction,
and conditional inverse on pinned full-return shell. No raw data replay.
Args: finite-return, current-budget, aperture, metric-charge checkers.
"""
import sys,json,hashlib
from pathlib import Path
import numpy as np
import sympy as s
paths=sys.argv[1:5]
expected=['291933beaaf7995fb56fe5fc9a03de396ab80822','97d67fa9e4af6f61835f766fbe89994a922c48cc','06d683bd2dfd24d4ad9de0620ef3718001fdbe36','1f3ee2625ede999147386b8f94e9078d29c94e65']
for path,sha in zip(paths,expected):
    raw=Path(path).read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==sha
# Published EISCAT Table 1: event integrated, not incident or ground work.
R=s.Rational;duration=135*60;E=[124*10**11,73*10**11,87*10**11]
assert sum(E)==284*10**11
mean=[R(v,duration) for v in E]
# Exact cross spectral ambiguity: same positive autospectra, opposite or
# quadrature cross terms. Real outward E x H normal flux is signed.
a,b=s.symbols('a b',positive=True,real=True)
for z in (1,-1,s.I,-s.I,0):
    C=s.Matrix([[a*a,a*b*z],[a*b*s.conjugate(z),b*b]])
    assert C.H==C and C.det()==a*a*b*b*(1-z*s.conjugate(z))
    assert s.re(C[0,1])==a*b*s.re(z)
# Sampling and published transfer coverage, not an anti-alias certificate.
freq=[R(5,1000),R(50,1000),R(3915,1000),R(783,100),R(7800)]
coverage={name:[bool(lo<=f<=hi) for f in freq] for name,lo,hi in [('AusLAMP_period_range',R(1,64000),1/R('5.3')),('minute_Nyquist',0,R(1,120)),('second_Nyquist',0,R(1,2))]}
# Literature sensitivity scales are not co-located measured cross PSDs.
mu0=4*np.pi*1e-7
flux_bound=200e-6*1e-12/mu0
# Consume actual finite-return model prefix and its pinned donors.
old=sys.argv;sys.argv=paths;env={};exec(compile(Path(paths[0]).read_text().split('\nrows=[];max_quad=')[0],paths[0],'exec'),env);sys.argv=old
rows=[];N=48;area=1.;g=1.;n=np.array([0.,0.,1.]);Bobs=env['angular'](n,N)[:2,:]
for f in (.005,7.83):
    *_,Z,V=env['shell'](f,N);T=env['overlap'](area,1.,N)
    Y=np.column_stack([env['native'](f,e,g)[0] for e in np.eye(7)])
    Rport=np.linalg.solve(np.eye(7)+T@Z@T.T@Y,T@V)
    # Original useful circuit output linear row, with sqrt(load conductance).
    Ac=env['Ac'];Kc=env['Kc'];L=env['L'];beta=env['beta'];rad=env['rad'];w=f/7.83
    obs=np.sqrt(.52)*(np.linalg.solve(1j*w*np.eye(9)-Ac,beta*rad*Kc.T@L.T/2)[-1]@Rport)
    # One hypothetical *unloaded* local tangent observer at patch center.
    M=Bobs@V;U,sv,W=np.linalg.svd(M,full_matrices=True);rank=int(sum(sv>sv[0]*1e-12));assert rank==2
    F=W[rank:].conj().T;assert np.linalg.norm(M@F)<1e-10
    for source in (0,4):
        truth=np.eye(N)[:,source];y=M@truth
        u0=W[:rank].conj().T@((U[:,:rank].conj().T@y)/sv[:rank]);assert np.linalg.norm(M@u0-y)<1e-10
        assert np.linalg.norm(F.conj().T@u0)<1e-10
        budget=1.;radius=np.sqrt(max(0.,budget-np.vdot(u0,u0).real));c=obs@u0;t=obs@F;spread=radius*np.linalg.norm(t)
        # Exact geometric disk on the complex observation fibre; attain endpoints.
        hi=(abs(c)+spread)**2;lo=max(0.,abs(c)-spread)**2
        phase=c/abs(c) if abs(c)>0 else 1.;direction=t.conj()/np.linalg.norm(t)
        maxu=u0+F@(radius*phase*direction)
        minu=u0-F@(min(radius,abs(c)/np.linalg.norm(t))*phase*direction)
        for v,p in [(maxu,hi),(minu,lo)]:
            assert np.linalg.norm(M@v-y)<1e-10 and np.linalg.norm(v)<=1+1e-10
            assert abs(abs(obs@v)**2-p)<1e-10*max(p,1e-30)
        actual=abs(obs@truth)**2;assert lo-1e-26<=actual<=hi+1e-26
        rows.append(dict(f=f,source=source,rank=rank,nullity=N-rank,min_incident_norm_sq=float(np.vdot(u0,u0).real),lower=float(lo),upper=float(hi),actual=float(actual),unseen_output_radius=float(spread)))
print(json.dumps(dict(status='PUBLISHED_SUMMARY_AND_CONDITIONAL_SPECTRAL_ADMISSION',event_duration_s=duration,mean_dissipation_W=[float(v) for v in mean],mean_EM_dissipation_W=float(mean[0]+mean[1]),mean_total_dissipation_W=float(sum(mean)),coverage=coverage,illustrative_cross_PSD_upper_W_m2_Hz=flux_bound,rows=rows,scope='Published event summaries only, no raw data downloaded. Sensitivity scales give conditional Cauchy bound only. Observer and incident unit norm are synthetic normalized same-shell fixtures, no physical field/current calibration or empirical fit.'),indent=2))

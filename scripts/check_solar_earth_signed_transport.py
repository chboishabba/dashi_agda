"""Source-owned restricted Maxwell flux cascade and GAMERA pair alignment.
No actual regional propagation or actuator admission.
Usage: python check.py /path/to/tangential_maxwell.py /path/to/PF_fig_PF.nc
"""
import hashlib,sys,json
from pathlib import Path
import sympy as s
import numpy as np
import xarray as xr
raw=Path(sys.argv[1]).read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='c8294bac77068ec47677b1c02053d99dfc76d0af'
ns={};exec(compile(raw,sys.argv[1],'exec'),ns)
gen=ns['tangential_generator'];step=ns['transfer_midpoint_z']
J=s.Matrix([[0,-1],[1,0]]);I=s.eye(4);G=s.zeros(2).row_join(-J/2).col_join((J/2).row_join(s.zeros(2)))
# RMS fields, exp(-i wt), positive z, scalar real mu and real transverse k.
w,m,k=s.symbols('w m k',positive=True,real=True)
a,b,c,d,e,f,g,h,z,t=s.symbols('a b c d e f g h z t',real=True)
eps=s.Matrix([[a+s.I*b,c+s.I*d,0],[e+s.I*f,g+s.I*h,0],[0,0,z+s.I*t]])
M=gen(w,k,m,eps[0,0],eps[1,1],eps[2,2],eps[0,1],eps[1,0])
L=s.Matrix([[1,0,0,0],[0,1,0,0],[0,0,0,-k/(w*eps[2,2])]])
loss=w*L.H*((eps-eps.H)/(2*s.I))*L
assert (M.H*G+G*M+loss).applyfunc(s.simplify)==s.zeros(4)
# Exact rational discretization, arbitrary anisotropic passive test layers.
R=s.Rational;layers=[gen(2,1,1,2,3,4, s.I/3,-s.I/3),gen(2,1,1,2+s.I,3+2*s.I,4+s.I),gen(2,1,1,3+s.I,2+s.I,2+s.I,R(1,3),R(1,3))]
T=I;loss_sum=s.zeros(4);ranks=[]
for M in layers:
    dz=R(1,5);A=I-dz*M/2;U=step(M,dz);D=-(M.H*G+G*M);D=D.applyfunc(s.simplify)
    assert D.is_positive_semidefinite
    Ld=dz*A.inv().H*D*A.inv();Ld=Ld.applyfunc(s.simplify)
    assert (G-U.H*G*U-Ld).applyfunc(s.simplify)==s.zeros(4)
    assert Ld == Ld.H
    # PSD follows by congruence of D with invertible A, dz > 0.
    loss_sum=(loss_sum+T.H*Ld*T).applyfunc(s.simplify);T=(U*T).applyfunc(s.simplify);ranks.append(D.rank())
assert (G-T.H*G*T-loss_sum).applyfunc(s.simplify)==s.zeros(4)
assert T==ns['three_layer_tangential_transfer'](layers,[R(1,5)]*3).applyfunc(s.simplify)
# The ground impedance graph w=[P h; J h] has exact flux Herm(P).
P=s.Matrix([[2+s.I,1+s.I],[1-s.I,3-s.I]]);K=P.col_join(J)
assert K.H*G*K==(P+P.H)/2
K0=T.inv()*K
assert (K0.H*G*K0-K.H*G*K-K0.H*loss_sum*K0).applyfunc(s.simplify)==s.zeros(2)
# Paired scalar power coordinates: for r>0, a+/a-=(E +/- r H)/(2sqrt(r)).
er,ei,hr,hi=s.symbols('er ei hr hi',real=True);E=er+s.I*ei;H=hr+s.I*hi;r=s.symbols('r',positive=True)
p=(E+r*H)/(2*s.sqrt(r));n=(E-r*H)/(2*s.sqrt(r))
assert s.simplify(p*s.conjugate(p)-n*s.conjugate(n)-s.re(E*s.conjugate(H)))==0
# Actual excerpt: weighted RMS and 200s phasor fit, not physical directional flux.
path=Path(sys.argv[2]);assert hashlib.sha256(path.read_bytes()).hexdigest()=='8ff495be1ebdd6609813061880b8faf08ac8365540e8ac2d2d64961c9b3b6880'
with xr.open_dataset(path,decode_cf=False) as ds:
    time=ds.tplt.values.ravel();x=ds.emrd_plts.values*1e-3;y=ds.bphi_plts.values*1e-9/(4*np.pi*1e-7);pos=ds.dsfl.values.ravel();trace=ds.fltraces.values
assert x.shape==y.shape==(61,615) and trace.shape==(3,609)
wt=np.r_[np.diff(time)[0]/2,(time[2:]-time[:-2])/2,np.diff(time)[-1]/2];wt/=wt.sum()
F=np.column_stack([np.ones(len(time)),np.cos(2*np.pi*time/200),np.sin(2*np.pi*time/200)])
fit=lambda v:np.linalg.lstsq(np.sqrt(wt)[:,None]*F,np.sqrt(wt)[:,None]*v,rcond=None)[0]
x0,y0=fit(x),fit(y);xp=(x0[1]-1j*x0[2])/np.sqrt(2);yp=(y0[1]-1j*y0[2])/np.sqrt(2)
results={};maxerr=0.
for name,X,Y,weights in [('full',x,y,wt),('fundamental',xp[None,:],yp[None,:],np.ones(1))]:
    U=np.sum(weights[:,None]*abs(X)**2,axis=0);V=np.sum(weights[:,None]*abs(Y)**2,axis=0);C=np.sum(weights[:,None]*(X*Y.conj()).real,axis=0)
    assert np.all(U>0) and np.all(V>0)
    gross=np.sqrt(U*V);chi=abs(C)/gross;assert max(chi)<=1+1e-12
    frac=(1-chi)/2; rr=np.sqrt(U/V)
    # Equality witness for abstract split, not a physical reference impedance.
    pp=(X+rr*Y)/(2*np.sqrt(rr));nn=(X-rr*Y)/(2*np.sqrt(rr));Pp=np.sum(weights[:,None]*abs(pp)**2,axis=0);Pn=np.sum(weights[:,None]*abs(nn)**2,axis=0)
    maxerr=max(maxerr,float(max(abs(Pp-Pn-C))),float(max(abs(Pp+Pn-gross))))
    assert np.allclose(np.minimum(Pp,Pn)/(Pp+Pn),frac,rtol=1e-9,atol=1e-12)
    results[name]=dict(signed_component_product_W_m2=[float(C.min()),float(C.max())],positive=int(sum(C>0)),negative=int(sum(C<0)),alignment_quantiles=np.percentile(chi,[0,25,50,75,100]).tolist(),lesser_split_fraction_quantiles=np.percentile(frac,[0,25,50,75,100]).tolist())
assert maxerr<1e-17
print(json.dumps(dict(status='CONDITIONAL_SIGNED_TRANSPORT_AND_ORIGINAL_PAIR_ALIGNMENT',loss_ranks=ranks,max_split_error_W_m2=maxerr,data_shape=list(x.shape),separate_trace_shape=list(trace.shape),results=results,physical_admission=False),indent=2))

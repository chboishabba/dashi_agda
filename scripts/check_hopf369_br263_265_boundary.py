"""Boundary source split, contracted product-rule ledger, open discrete boundary work."""
import inspect
import numpy as np
import check_hopf369_br257_259_subsidiary_evolution as donor
from check_hopf369_br260_262_operator_weld import matched
from check_hopf369_br256_spatial import diff


def split(h0,h1,dt,dx):
    E=(h0['E']+h1['E'])/2; I=(h0['I']+h1['I'])/2
    G=(h0['G']+h1['G'])/2; den=(h0['den']+h1['den'])/2
    def source(E,Et):
        DE=np.zeros(E.shape[:-2]+(5,5,5));DE[...,0,:,:]=Et
        for i in range(1,4):DE[...,i,:,:]=diff(E,dx,i-1)
        CE=DE-np.einsum('...aki,...aj->...kij',G,E)-np.einsum('...akj,...ia->...kij',G,E)
        return den[...,None]*(-2*np.einsum('...ki,...kij->...j',I,CE)+np.einsum('...ij,...kij->...k',I,CE))
    mask=np.zeros(E.shape[:3]);mask[2:-2,2:-2,2:-2]=1;mask=mask[...,None,None]
    Et=(h1['E']-h0['E'])/dt
    F=source(E,Et);Fi=source(E*mask,Et*mask);Fb=source(E*(1-mask),Et*(1-mask))
    assert np.max(abs(F-Fi-Fb))<1e-12
    # Exact contracted spatial Leibniz remainder, computed also from stencil increments.
    worst=0.;rem=0.
    for k in range(1,4):
        a=I[...,k,:]; b=E
        r=diff(np.einsum('...i,...ij->...j',a,b),dx,k-1)-np.einsum('...i,...ij->...j',diff(a,dx,k-1),b)-np.einsum('...i,...ij->...j',a,diff(b,dx,k-1))
        aa=np.moveaxis(a,k-1,0);bb=np.moveaxis(b,k-1,0)
        rr=sum(w*np.einsum('...i,...ij->...j',aa[2+j:len(aa)-2+j]-aa[2:-2],bb[2+j:len(bb)-2+j]-bb[2:-2]) for j,w in [(-2,1),(-1,-8),(1,8),(2,-1)])/(12*dx)
        r=np.moveaxis(r,k-1,0)[2:-2];worst=max(worst,np.max(abs(r-rr)));rem=max(rem,np.max(abs(r)))
    assert worst<1e-12
    sl=(slice(2,-2),)*3; core=(slice(4,-4),)*3
    print('BR263 split total/interior/exterior/core',*[float(np.max(abs(x))) for x in (F[sl],Fi[sl],Fb[sl],F[core])],'BR264 remainder/error',rem,worst,flush=True)
    return F[sl]


def run(homogeneous=False):
    src=inspect.getsource(donor.run)
    # Use the actual non-skew derivative on the restricted domain; retain its boundary form.
    start=src.index('        pads=');end=src.index('    def grad',start)
    src=src[:start]+'        return diff(q,dx,i)\n'+src[end:]
    start=src.index('    rng=');end=src.index('    def coeff',start)
    src=src[:start]+src[end:]
    start=src.index("        E=h['E']");end=src.index('        maxforce=',start)
    src=src[:start]+'        F=split(h0,h1,dt,dx)\n'+src[end:]
    src=src.replace('worst=0.;total=0.;','boundary_total=0.;worst=0.;total=0.;')
    src=src.replace('        work=dt*dv*', '''        w=grad(qm);j=B[..., :,None]*u[...,None,:]+np.einsum('...ij,...jm->...im',D,w)
        boundary=dt*dv*(np.sum(u*div(j))+np.sum(grad(u)*j))
        boundary_total+=boundary
        work=boundary+dt*dv*''')
    src=src.replace('        old=pack(q,p);','        assert np.max(abs(lin(np.zeros(2*size))))==0\n        old=pack(q,p);')
    src+='    print("BR265 boundary work",boundary_total,flush=True)\n'
    if homogeneous:
        src=src.replace('worst=0.;total=0.;','q[:]=0;p[:]=0;worst=0.;total=0.;')
        src=src.replace('F=split(h0,h1,dt,dx)','F=np.zeros(shape)')
        src+='    assert np.max(abs(q))==0 and np.max(abs(p))==0 and final==0\n'
        src+='    print("BR265 homogeneous zero control PASS",flush=True)\n'
    ns=dict(vars(donor),geometry=matched(),split=split);exec(src,ns);ns['run'](11,8)

if __name__=='__main__':
    import sys
    run('--homogeneous' in sys.argv)

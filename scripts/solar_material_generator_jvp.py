"""Same-mesh positive-support derivative of original Maxwell/material generator.
Consumes the Whitney edge-current map and diagonal Hodge; no topology changes.
"""
import numpy as np

def material_jvp(model,volumes,D,nu,dD,dnu):
    D,nu,dD,dnu=[np.asarray(v,float) for v in (D,nu,dD,dnu)]
    vol=np.asarray(volumes,float); n=len(vol)
    assert D.shape==nu.shape==dD.shape==dnu.shape==(n,3)
    assert np.all(D>=0) and np.all(nu>=0) and np.all(vol>0)
    if np.any((D==0)&((dD!=0)|(dnu!=0))):
        raise ValueError('zero-density support transition needs separate chart')
    me=np.asarray(model['energy_masses'][0],float)
    W=np.asarray(model['material_map'],float)
    ne=len(me); N=model['generator'].shape[0]; nf=N-ne-9*n
    assert nf>=0 and W.shape==(ne,3*n)
    dA=np.zeros((N,N)); dloss=np.zeros((N,N))
    for o in range(n):
        base=W[:,3*o:3*o+3]/np.sqrt(me)[:,None]
        for j in range(3):
            sl=slice(ne+nf+9*o+3*j,ne+nf+9*o+3*j+3)
            if D[o,j]>0:
                dc=base*dD[o,j]/(2*np.sqrt(D[o,j]*vol[o]))
                dA[:ne,sl]=-dc;dA[sl,:ne]=dc.T
                dloss[sl,sl]=np.eye(3)*dnu[o,j]
    assert np.allclose(dA,-dA.T,atol=1e-13,rtol=0)
    return dict(d_generator=dA-dloss,d_exchange=dA,d_loss=dloss)

def amplitude_exchange_jvp(model,volumes,amplitude,d_amplitude):
    """Reciprocal operator derivative in q=sqrt(D) coordinates, including q=0.

    Only the off-diagonal Whitney exchange is differentiated here.
    The native loss and gyro blocks switch support at q=0; their full
    generator derivative is NOT licensed by this smooth exchange chart.
    The timed propagator also needs an explicit new-support stage.
    """
    q,dq=[np.asarray(v,float) for v in (amplitude,d_amplitude)]
    vol=np.asarray(volumes,float);n=len(vol)
    if q.shape!=(n,3) or dq.shape!=q.shape or np.any(q<0) or np.any(vol<=0):
        raise ValueError('invalid population amplitude support chart')
    if np.any((q==0)&(dq<0)):
        raise ValueError('amplitude would cross negative half-line')
    me=np.asarray(model['energy_masses'][0],float)
    W=np.asarray(model['material_map'],float)
    ne=len(me);N=model['generator'].shape[0];nf=N-ne-9*n
    if nf<0 or W.shape!=(ne,3*n): raise ValueError('material map mismatch')
    out=np.zeros((N,N))
    for o in range(n):
        base=W[:,3*o:3*o+3]/np.sqrt(me*vol[o])[:,None]
        for j in range(3):
            sl=slice(ne+nf+9*o+3*j,ne+nf+9*o+3*j+3)
            dc=base*dq[o,j]
            out[:ne,sl]=-dc;out[sl,:ne]=dc.T
    assert np.array_equal(out,-out.T)
    return dict(d_exchange=out,full_generator_jvp_admitted=False,
                zero_support_stage_weld_required=bool(np.any((q==0)&(dq!=0))))

def fixtures():
    rng=np.random.default_rng(369);ne,nf,n=5,3,2;N=ne+nf+9*n
    W=rng.normal(size=(ne,3*n));me=1+rng.random(ne);vol=np.array([2.,3.])
    D=rng.uniform(.5,2.5,(n,3));nu=rng.uniform(.2,1.2,(n,3))
    dD=rng.normal(size=(n,3))*.1;dnu=rng.normal(size=(n,3))*.1
    model=dict(energy_masses=(me,np.ones(nf)),material_map=W,generator=np.zeros((N,N)))
    derivative=material_jvp(model,vol,D,nu,dD,dnu)['d_generator']
    def assemble(d,v):
        A=np.zeros((N,N))
        for o in range(n):
            for j in range(3):
                sl=slice(ne+nf+9*o+3*j,ne+nf+9*o+3*j+3)
                C=W[:,3*o:3*o+3]*np.sqrt(d[o,j]/vol[o])/np.sqrt(me)[:,None]
                A[:ne,sl]=-C;A[sl,:ne]=C.T;A[sl,sl]-=np.eye(3)*v[o,j]
        return A
    errors=[]
    for h in (1e-3,1e-4,1e-5):
        errors.append(float(np.max(np.abs((assemble(D+h*dD,nu+h*dnu)-assemble(D-h*dD,nu-h*dnu))/(2*h)-derivative))))
    assert errors[-1]<1e-10
    negative=False
    try:
        d=D.copy();d[0,0]=0
        material_jvp(model,vol,d,nu,dD,dnu)
    except ValueError:negative=True
    assert negative
    return dict(errors=errors,zero_support_rejected=negative)
if __name__=='__main__':
    print(fixtures())

"""Signed bidirectional space/time refinement of periodic SI histories.
Use explicit independently supplied spatial restriction; never identify radar
rows with mesh adjacency. Preserve the complete complement and zero mode.
"""
import numpy as np

def split(x,R,L):
    x,R,L=map(lambda v:np.asarray(v,float),(x,R,L))
    if not np.allclose(R@L,np.eye(R.shape[0]),rtol=1e-12,atol=1e-12):
        raise ValueError('not a right inverse')
    y=x@R.T; detail=x-y@L.T
    assert np.allclose(detail@R.T,0,atol=1e-10*max(1.,np.linalg.norm(x)))
    assert np.allclose(y@L.T+detail,x)
    return y,detail

def split_time(x,m):
    """Odd Fourier chart: keep signed modes -m..m, store every discarded mode."""
    x=np.asarray(x,float); n=len(x)
    if n%2!=1 or not 0<=m<=n//2: raise ValueError('odd Fourier grid')
    z=np.fft.fftshift(np.fft.fft(x,axis=0)/n,axes=0)
    mid=n//2; keep=z[mid-m:mid+m+1].copy()
    rest=z.copy(); rest[mid-m:mid+m+1]=0
    return keep,rest

def reopen_time(keep,rest):
    z=rest.copy(); m=len(keep)//2; mid=len(rest)//2
    z[mid-m:mid+m+1]+=keep
    x=np.fft.ifft(np.fft.ifftshift(z,axes=0)*len(z),axis=0)
    assert np.max(abs(x.imag))<1e-10*max(1.,np.linalg.norm(x.real))
    return x.real

def compare(fine,coarse,R,L):
    fine,coarse=np.asarray(fine,float),np.asarray(coarse,float)
    if len(coarse)%2!=1 or len(fine)<len(coarse): raise ValueError('resolution')
    y,detail=split(fine,R,L)
    k,rest=split_time(y,len(coarse)//2)
    low=np.fft.ifft(np.fft.ifftshift(k,axes=0)*len(k),axis=0).real
    rho=low-coarse
    recovered=reopen_time(np.fft.fftshift(np.fft.fft(coarse+rho,axis=0)/len(coarse),axes=0),rest)@np.asarray(L).T+detail
    assert np.allclose(recovered,fine)
    # Independent path: temporal restriction then spatial restriction.
    k2,_=split_time(fine,len(coarse)//2)
    square=k-k2@np.asarray(R).T
    assert np.allclose(square,0,atol=1e-10*max(1.,np.linalg.norm(k)))
    return dict(signed_residual=rho,spatial_complement=detail,temporal_complement=rest,
                zero_mode=k[len(k)//2],square_residual=square,reconstruction_error=float(np.max(abs(recovered-fine))))

def fixtures():
    rng=np.random.default_rng(369); cases=0; worst=0.
    for n in (5,9,17):
        for m in (3,5):
            if m>n: continue
            R=np.array([[.5,.5,0,0],[0,0,1,0]])
            L=np.linalg.pinv(R)
            x=rng.normal(size=(n,4)); y=rng.normal(size=(m,2))
            out=compare(x,y,R,L); worst=max(worst,out['reconstruction_error']); cases+=1
    return dict(cases=cases,max_reconstruction_error=worst)
if __name__=='__main__':
    import json
    print(json.dumps(fixtures(),indent=2))

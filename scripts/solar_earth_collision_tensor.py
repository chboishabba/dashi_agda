"""Source-backed two-ion conditional tensor; DOI 10.1186/s40623-017-0677-4 eqs 3–5.
This is a published alternative collision law, not the original 2024 heating replay.
"""
import datetime as dt
import hashlib
import json
import h5py
import numpy as np
from scipy.constants import elementary_charge as e, electron_mass as me, atomic_mass as u, epsilon_0, mu_0, c

def composition(root,rows):
    with h5py.File(root/'MAD6400_2017-12-18_bella_60@vhf.hdf5') as f: a=f['Data/Table Layout'][:]
    key={(int(x['recno']),float(x['range'])):x for x in a}
    b=np.array([key[r['record'],r['range_km']] for r in rows]); assert np.allclose(b['ne'],[r['ne'] for r in rows],rtol=0,atol=0)
    p=np.array([b['pm'],b['po+']],float).T
    assert np.all(p>=0) and np.allclose(p.sum(axis=1),1,atol=4e-8,rtol=0)
    # The fitted composition priors are not independent observations. Normalize rounding only.
    return p/p.sum(axis=1)[:,None]

def rates(rows,neutral):
    te=np.array([r['te'] for r in rows]); ti=np.array([r['ti'] for r in rows]); O,N2,O2=neutral[:,1],neutral[:,2],neutral[:,3]; tr=(ti+neutral[:,10])/2
    assert np.all((te>0)&(te<1/1.21e-4)) and np.all(tr>0)
    ve=2.33e-17*N2*(1-1.21e-4*te)*te+1.82e-16*O2*(1+.036*np.sqrt(te))*np.sqrt(te)+8.9e-17*O*(1+5.7e-4*te)*np.sqrt(te)
    vm=1e-16*(4.29*N2+4.23*O2+2.41*O)
    log=np.log10(tr); vo=6.82e-16*N2+6.66e-16*O2+3.42e-17*O*np.sqrt(tr)*(1.08-.139*log+.00451*log**2)
    out=np.array([ve,vm,vo]).T; assert np.all(np.isfinite(out)) and np.all(out>0)
    return out

def tensor_replay(root,rows,B,storm,daily,packet=None):
    n=len(rows); mag=np.linalg.norm(B,axis=1); b=B/mag[:,None]; ne=np.array([r['ne'] for r in rows]); mass=np.array([me,30.5*u,16*u]); charge=e*np.array([-1,1,1]); pop=ne[:,None]*np.column_stack([np.ones(n),composition(root,rows)])
    D=pop*charge**2/mass; Om=mag[:,None]*charge/mass; I=np.eye(3); pp=b[:,:,None]*b[:,None,:]; pt=I-pp
    J=np.zeros((n,3,3)); J[:,0,1]=-b[:,2]; J[:,0,2]=b[:,1]; J[:,1,0]=b[:,2]; J[:,1,2]=-b[:,0]; J[:,2,0]=-b[:,1]; J[:,2,1]=b[:,0]
    assert np.max(np.abs(J@J+pt))<1e-14
    qs=lambda x:np.quantile(x,[0,.5,1],axis=0).tolist(); out={}; tensors={}; freq=[0,3.915,7.83,7800]
    for label,neutral in [('history',storm),('daily',daily)]:
        nu=rates(rows,neutral); out[label]={'rates_s-1':qs(nu),'frequencies':{}}; tensors[label]=[]
        for f in freq:
            w=2*np.pi*f; a=nu-1j*w; den=a*a+Om*Om; p=np.sum(D*a/den,axis=1); h=np.sum(-D*Om/den,axis=1); par=np.sum(D/a,axis=1)
            sig=p[:,None,None]*pt+h[:,None,None]*J+par[:,None,None]*pp
            mat=a[:,:,None,None]*I+Om[:,:,None,None]*J[:,None]; direct=np.sum(D[:,:,None,None]*np.linalg.inv(mat),axis=1)
            rel=float(np.max(np.linalg.norm(sig-direct,axis=(1,2))/np.linalg.norm(direct,axis=(1,2)))); assert rel<1e-10
            # Hermitian dissipation eigenvalues in the shared circular frame.
            zp=np.sum(D/(a+1j*Om),axis=1); zm=np.sum(D/(a-1j*Om),axis=1)
            ev=np.linalg.eigvalsh((sig+sig.conj().swapaxes(1,2))/2); exact=np.sort(np.column_stack([par.real,zp.real,zm.real]),axis=1)
            assert np.all(ev>=-1e-12) and np.allclose(ev,exact,rtol=1e-7,atol=1e-12)
            for sign,z in [(1,zp),(-1,zm)]:
                det=sign*Om-w; assert np.all(det!=0); P=np.sum(np.where(det>0,D/det,0),axis=1); N=np.sum(np.where(det<0,-D/det,0),axis=1); radius=(P+N)/2
                assert np.all(np.abs(z-1j*(N-P)/2)<=radius*(1+1e-10)) and np.all(np.abs(z)<=np.maximum(P,N)*(1+1e-10))
            if f==0: assert np.all(np.hypot(p.real,h.real)<=e*ne/mag*(1+1e-10))
            # Existing tilted Schur/flux identity in NED frame; k=w/c is a test chart, not an inferred wave.
            flux_res=None
            if f:
                eps=epsilon_0*I+1j*sig/w; k=w/c; L=np.zeros((n,3,4),complex); L[:,0,0]=1; L[:,1,1]=1; L[:,2,0]=-eps[:,2,0]/eps[:,2,2]; L[:,2,1]=-eps[:,2,1]/eps[:,2,2]; L[:,2,3]=-k/(w*eps[:,2,2])
                M=np.zeros((n,4,4),complex); M[:,0,3]=1j*w*mu_0; M[:,0]+=1j*k*L[:,2]; M[:,1,2]=-1j*w*mu_0; M[:,2,1]=1j*k*k/(w*mu_0); M[:,2]-=1j*w*(eps[:,1:2,:]@L)[:,0]; M[:,3]=1j*w*(eps[:,0:1,:]@L)[:,0]
                G=np.array([[0,0,0,.5],[0,0,-.5,0],[0,-.5,0,0],[.5,0,0,0]])
                loss=L.conj().swapaxes(1,2)@((sig+sig.conj().swapaxes(1,2))/2)@L
                lhs=M.conj().swapaxes(1,2)@G+G@M; flux_res=float(np.max(np.linalg.norm(lhs+loss,axis=(1,2))/np.maximum(np.linalg.norm(loss,axis=(1,2)),1e-30))); assert flux_res<1e-8
            out[label]['frequencies'][str(f)]={'P_real':qs(p.real),'H_real':qs(h.real),'parallel_real':qs(par.real),'max_inverse_relative_error':rel,'max_flux_relative_residual':flux_res}
            tensors[label].append(sig)
    # A deterministic key-preserving derived model packet; never promote it to measured fields.
    hasher=hashlib.sha256(); file=open(packet,'w') if packet else None
    try:
        for i,r in enumerate(rows):
            rec={'record':r['record'],'range_km':r['range_km'],'utc':r['utc'],'B_NED_T':B[i].tolist(),'neutral_history_SI':storm[i].tolist(),'neutral_daily_SI':daily[i].tolist(),'tensor_by_history_and_frequency':{label:{str(f):np.stack([z[i].real,z[i].imag],axis=-1).tolist() for f,z in zip(freq,ls)} for label,ls in tensors.items()}}
            line=json.dumps(rec,sort_keys=True,separators=(',',':'),allow_nan=False)+'\n'; hasher.update(line.encode());
            if file: file.write(line)
    finally:
        if file: file.close()
    return {'model':'published 2017 two-ion approximation; fitted PM/PO+ priors; no wind, Coulomb collision, pressure or population history','rows':n,'tensor_evaluations':n*len(freq)*2,'packet_sha256':hasher.hexdigest(),'results':out}

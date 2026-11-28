"""3+1 timed local propagation consumer of the indexed Cayley/cone contract.

Donors: SmithFilsingerIndexedCayleyFaceWeldExact,
SmithFilsingerLocalCausalADEReachExact, SmithFilsingerYeeCFLConeGuardExact,
LargePosetContinuumLorentz31. Discrete schedule support is NOT continuum
Maxwell support. Internal coordinates share their physical site, not extra
spatial dimensions. All distances in metres and times in seconds.
"""
import numpy as np
from scipy.constants import c
from scipy.linalg import solve

def validate_mesh(mesh,d):
    xyz=np.asarray(mesh['positions_m'],float)
    site=np.asarray(mesh['coordinate_site'],int)
    assert xyz.ndim==2 and xyz.shape[1]==3 and np.isfinite(xyz).all()
    assert site.shape==(d,) and np.all((site>=0)&(site<len(xyz)))
    faces={}
    for f in mesh['faces']:
        i,j=f['source'],f['target']
        assert f['id'] not in faces and 0<=i<len(xyz) and 0<=j<len(xyz) and i!=j
        normal=np.asarray(f['normal'],float)
        assert normal.shape==(3,) and np.isclose(normal@normal,1)
        assert f['area_m2']>0 and normal@(xyz[j]-xyz[i])>0
        faces[f['id']]=f
    return xyz,site,faces

def timed_step(x,H,force,dt,mesh,loss_forms=None,source_port=None,incident=0.,retain_local_midpoint=False,retain_stage_residuals=False):
    """Lie product of local midpoint maps, partitioning generator exactly.
    One serial stage consumes its own elapsed physical time. Coefficients are
    rescaled so integrated first-order generator equals dt*H. A remote stage
    is rejected unless its actual allotted interval satisfies the cone.
    This is a distinct approximation, not the original dense midpoint map.
    """
    x=np.array(x,float,copy=True); H=np.asarray(H,float); force=np.asarray(force,float)
    d=len(x); assert H.shape==(d,d) and force.shape==(d,) and dt>0
    xyz,site,faces=validate_mesh(mesh,d)
    groups=[np.flatnonzero(site==i) for i in range(len(xyz))]
    forms={} if loss_forms is None else {k:np.asarray(v,float) for k,v in loss_forms.items()}
    for a in forms.values():
        assert a.shape==(d,d) and np.allclose(a,a.T)
        if np.any(a[site[:,None]!=site[None,:]]!=0): raise ValueError('loss form must be site-local')
    if forms and not np.allclose(sum(forms.values()),-(H+H.T)/2,rtol=1e-10,atol=1e-12): raise ValueError('loss partition mismatch')
    channel={k:0. for k in forms}; incoming=outgoing=0.
    local_mid=np.zeros(d) if retain_local_midpoint else None
    reflected=None
    from fractions import Fraction
    exact_error=Fraction(0); midpoint_error=[Fraction(0)]*d
    def rational(v): return Fraction(float(v))
    if source_port is not None:
        source_port=np.asarray(source_port,float); assert source_port.shape==(d,)
        assert len(np.unique(site[source_port!=0]))==1
        assert np.allclose(force,2*incident*source_port)
        assert 'source' in forms and np.allclose(forms['source'],np.outer(source_port,source_port))
    pieces=[]; accounted=np.zeros_like(H)
    for ix in groups:
        if not len(ix): continue
        a=H[np.ix_(ix,ix)]
        pieces.append((ix,a,force[ix],None))
        accounted[np.ix_(ix,ix)]=a
    # Off-site couplings must be skew exchange on actual indexed faces.
    bypair={}
    for f in faces.values():
        key=tuple(sorted((f['source'],f['target'])))
        if key in bypair: raise ValueError('ambiguous face ownership')
        bypair[key]=f
    for i in range(d):
        for j in range(i+1,d):
            if site[i]==site[j] or (H[i,j]==0 and H[j,i]==0): continue
            if not np.isclose(H[i,j],-H[j,i],rtol=1e-12,atol=0):
                raise ValueError('nonlocal dissipative/direct-feedthrough operator')
            f=bypair.get(tuple(sorted((site[i],site[j]))))
            if f is None: raise ValueError('missing original face')
            ix=np.array([i,j]); a=H[np.ix_(ix,ix)].copy(); np.fill_diagonal(a,0)
            pieces.append((ix,a,np.zeros(2),f['id']))
            accounted[i,j]=H[i,j]; accounted[j,i]=H[j,i]
    assert np.array_equal(accounted,H)
    tau=dt/len(pieces); gain=dt/tau
    speed=float(mesh.get('front_speed_m_s',c))
    assert 0<speed<=c
    # Earliest arrival from each initially occupied coordinate and injection.
    reachable=np.flatnonzero(x!=0); arrival=np.full(d,np.inf); arrival[reachable]=0
    work=loss=0.; receipts=[]
    for k,(ix,a,b,fid) in enumerate(pieces):
        t0=k*tau; t1=(k+1)*tau
        distance=float(np.max(np.linalg.norm(xyz[site[ix]][:,None]-xyz[site[ix]][None,:],axis=-1)))
        if distance>speed*tau: raise ValueError('stage violates calibrated distance/time cone')
        old=x[ix].copy()
        # Source roots are explicit, located on this local site.
        roots=ix[b!=0]; arrival[roots]=np.minimum(arrival[roots],t0)
        if np.any(arrival[ix]<=t0): arrival[ix]=np.minimum(arrival[ix],t1)
        I=np.eye(len(ix)); y=solve(I-dt*a/2,(I+dt*a/2)@old+dt*b)
        if retain_stage_residuals:
            # Exact residual of the binary64 input coefficients, not of the
            # underlying physical material/metric model. All previous stage
            # error contracts when the exact symmetric part is nonpositive.
            import sympy as sp
            aa=sp.Matrix([[sp.Rational(float(v)) for v in row] for row in a])
            if not (-(aa+aa.T)).is_positive_semidefinite:
                raise ValueError('exact dissipativity failed')
            hh=rational(dt); rr=[]
            for ii in range(len(ix)):
                ri=rational(y[ii])-rational(old[ii])-hh*rational(b[ii])
                ri-=hh*sum(rational(a[ii,jj])*(rational(y[jj])+rational(old[jj]))/2 for jj in range(len(ix)))
                rr.append(abs(ri))
            local_error=sum(rr)
            if fid is None:
                for ii in ix: midpoint_error[ii]=exact_error+local_error/2
            exact_error+=local_error
        mid=(old+y)/2; w=dt*float(mid@b); q=-dt*float(mid@a@mid)
        assert q>=-1e-10*max(1.,abs(w),float(old@old))
        assert abs((y@y-old@old)/2-w+q)<1e-9*max(1.,abs(w),float(old@old))
        if fid is None:
            if local_mid is not None: local_mid[ix]=mid
            for name,F in forms.items(): channel[name]+=dt*float(mid@F[np.ix_(ix,ix)]@mid)
            if source_port is not None and np.any(source_port[ix]!=0):
                reflected=float(mid@source_port[ix]-incident)
                incoming+=dt*incident**2; outgoing+=dt*reflected**2
        x[ix]=y; work+=w; loss+=q
        assert np.all(x[arrival>t1]==0)
        receipts.append(dict(face_id=fid,coordinates=ix.tolist(),start_s=t0,end_s=t1,distance_m=distance,source_roots=roots.tolist(),work_J=w,loss_J=q))
    if forms: assert abs(sum(channel.values())-loss)<1e-9*max(1.,abs(loss))
    if source_port is not None: assert abs(work-channel['source']-incoming+outgoing)<1e-9*max(1.,incoming,outgoing)
    return x,dict(work_J=work,loss_J=loss,loss_channels_J=channel,incident_J=incoming,outgoing_J=outgoing,events=receipts,arrival_s=[float(a) if np.isfinite(a) else None for a in arrival],
                  exact_binary_stage_error=str(exact_error) if retain_stage_residuals else None,
                  exact_binary_midpoint_error=[str(v) for v in midpoint_error] if retain_stage_residuals else None,
                  local_midpoint=None if local_mid is None else local_mid.tolist(),reflected_amplitude=reflected,
                  physical_front_admitted=False,stage_speed_bound_m_s=speed,
                  approximation='serial local midpoint product; first order consistent at fixed mesh, admissible time intervals only')

def fixtures():
    mesh=dict(positions_m=[[0,0,0],[1,0,0],[2,0,0]],coordinate_site=[0,1,2],
        faces=[dict(id='a',source=0,target=1,normal=[1,0,0],area_m2=1),dict(id='b',source=1,target=2,normal=[1,0,0],area_m2=1)])
    H=np.array([[0.,-1,0],[1,0,-1],[0,1,0]])
    x=np.array([1.,0,0]); y,w=timed_step(x,H,np.zeros(3),1e-6,mesh)
    assert abs(y@y-x@x)<1e-12
    assert w['arrival_s'][2]>w['arrival_s'][1]
    rejected=False
    try: timed_step(x,H,np.zeros(3),1e-10,mesh)
    except ValueError: rejected=True
    assert rejected
    return dict(energy_residual=float(abs(y@y-x@x)/2),short_clock_rejected=rejected,receipt=w)

if __name__=='__main__':
    import json
    print(json.dumps(fixtures(),indent=2))

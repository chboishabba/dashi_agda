"""Periodic thermal/Maxwell weld on existing Grid and IncidentGrid owners.
Normalized conditional model; fixed population, collision heat exported to bath.
"""
import json
import numpy as np


def thermal(p,h):
    # theta' = p - theta, exact step for nonnegative held input.
    p=np.asarray(p,float); assert np.all(p>=0)
    a=np.exp(-h); b=-np.expm1(-h)
    x=np.zeros(p.shape[1])
    for u in p: x=a*x+b*u
    x=x/(-np.expm1(-h*len(p))); hist=[x.copy()]; mid=[]; heat=0.
    for u in p:
        mid.append(np.exp(-h/2)*x- np.expm1(-h/2)*u)
        y=a*x+b*u; heat+=np.sum(h*u-y+x); x=y; hist.append(x.copy())
    assert np.max(abs(x-hist[0]))<1e-12
    return np.array(hist),np.array(mid),float(heat)


def periodic(maps, offsets):
    A=np.eye(len(offsets[0])); b=np.zeros(len(A))
    for T,c in zip(maps,offsets): A=T@A; b=T@b+c
    if max(abs(np.linalg.eigvals(A)))>=1-1e-12: raise ValueError('no certified attracting return in selected model')
    x=np.linalg.solve(np.eye(len(A))-A,b)
    return x


def run(k,l,source,control,amp=.03):
    from solar_earth_spatial_transport import Grid,cell
    from solar_earth_incident_port import IncidentGrid
    n=2**k; N=2**l; dx=1/n; h=1/N
    t=(np.arange(N)+.5)*h; r=(np.arange(n)+.5)*dx
    p=amp*(1+np.cos(2*np.pi*t[:,None]))*(1+r[None,:]) if control else np.zeros((N,n))
    th,mid,cool=thermal(p,h); a=np.zeros((N,2,2)); a[:,0,0]=float(source)*.4; a[:,0,1]=float(source)*.2*np.cos(2*np.pi*t)
    stages=[]; maps=[]; offsets=[]
    for theta,inc in zip(mid,a):
        g=Grid(dx,[cell(1.,(1.,),(.5+v,),(-2.,),.3) for v in theta],1.)
        m=IncidentGrid(g,h,[1.,1.]); z=np.zeros(g.size); no=np.zeros((2,2))
        maps.append(np.column_stack([m.step(v,no,z)[0] for v in np.eye(g.size)])); offsets.append(m.step(z,inc,z)[0]); stages.append(m)
    x=periodic(maps,offsets); initial=x.copy(); hist=[x.copy()]; ledger=np.zeros(6)
    for m,inc in zip(stages,a):
        x,w,_=m.step(x,inc,np.zeros_like(x)); ledger+=w; hist.append(x.copy())
    err=float(np.linalg.norm(x-initial)); assert err<1e-9
    I,O,Q,L,P,R=ledger; paid=dx*h*p.sum(); bath=dx*cool
    residual=(x@x-initial@initial)/2+O+Q+L+bath-I-paid
    assert abs(residual)<1e-9 and abs(paid-bath)<1e-10 and P==R==0
    if not source: assert abs(L)<1e-12
    return dict(k=k,l=l,history=np.array(hist),thermal=th,ledger=ledger,paid=float(paid),net=float(L-paid),return_error=err,balance=float(residual))


def restrict(fine,k):
    # Energy-normalized cell average and shared physical face trace. Not isometry.
    n=2**k; z=np.asarray(fine); assert z.shape[-1]==12*n+2*(2*n-1)
    cells=z[...,:12*n].reshape(*z.shape[:-1],n,2,6).sum(axis=-2)/np.sqrt(2)
    faces=z[...,12*n:].reshape(*z.shape[:-1],2*n-1,2)[...,1::2,:]*np.sqrt(2)
    return np.concatenate([cells.reshape(*z.shape[:-1],6*n),faces.reshape(*z.shape[:-1],2*(n-1))],axis=-1)


def fixtures():
    rows=[]
    for k,l in ((1,3),(2,3),(1,4),(2,4)):
        for src,ctl in ((False,False),(False,True),(True,False),(True,True)):
            a=run(k,l,src,ctl); rows.append({key:val.tolist() if isinstance(val,np.ndarray) else val for key,val in a.items() if key not in ('history','thermal')})
    c=run(1,3,True,True); f=run(2,4,True,True)
    rho=restrict(f['history'][::2],1)-c['history']; rt=f['thermal'][::2].reshape(9,2,2).mean(axis=-1)-c['thermal']
    assert np.max(abs(rho))>0 and np.allclose(c['history']+rho,restrict(f['history'][::2],1))
    print(json.dumps(dict(worlds=rows,shared_time_signed_residual=rho.tolist(),thermal_residual=rt.tolist(),physical_admission=False),indent=2))

if __name__=='__main__': fixtures()

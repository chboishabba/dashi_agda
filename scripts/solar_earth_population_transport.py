"""Charge-neutral population events between indexed Maxwell/Drude stages.
Only mean-velocity removal and prescribed birth velocity; no chemistry fit.
"""
import json
import numpy as np
from solar_earth_spatial_transport import Grid, verify_step


class PopulationGrid:
    def __init__(self, dx, mu, eps, mass, charge, n, nu, B, load, periodic=False):
        self.mass=np.asarray(mass,float); self.charge=np.asarray(charge,float)
        self.n=np.array(n,float); self.nu=np.array(nu,float); self.B=np.array(B,float)
        self.eps=np.array(eps,float); self.load=np.array(load,float)
        if self.n.ndim!=2 or self.n.shape!=self.nu.shape or self.mass.shape!=self.charge.shape or self.mass.shape!=(self.n.shape[1],) or self.B.shape!=(len(self.n),3) or self.eps.shape!=self.load.shape or self.eps.shape!=(len(self.n),): raise ValueError('material shapes')
        if not all(np.isfinite(a).all() for a in (self.mass,self.charge,self.n,self.nu,self.B,self.eps,self.load)) or np.any(self.mass<=0) or np.any(self.charge==0) or np.any(self.n<0): raise ValueError('invalid population')
        mag=np.linalg.norm(self.B,axis=1); cells=[]
        for i in range(len(self.n)):
            b=self.B[i]/mag[i] if mag[i]>0 else np.array([0.,0.,1.])
            cells.append(dict(eps=self.eps[i],D=self.n[i]*self.charge**2/self.mass,nu=self.nu[i],omega=mag[i]*self.charge/self.mass,b=b,load=self.load[i]))
        self.grid=Grid(dx,cells,mu,periodic)

    def velocities(self,z):
        z=np.asarray(z,float)
        if z.shape!=(self.grid.size,) or not np.isfinite(z).all(): raise ValueError('state')
        v=np.zeros((*self.n.shape,3))
        for i,(sl,_,_) in enumerate(self.grid.local):
            for k,j in enumerate(np.flatnonzero(self.n[i]>0)):
                v[i,j]=np.sign(self.charge[j])*z[sl.start+3+3*k:sl.start+6+3*k]/np.sqrt(self.grid.dx*self.mass[j]*self.n[i,j])
        return v

    def event(self,z,removed,created,birth,nu=None,B=None):
        r,c,b=map(lambda a:np.asarray(a,float),(removed,created,birth))
        if r.shape!=self.n.shape or c.shape!=self.n.shape or b.shape!=(*self.n.shape,3) or not all(np.isfinite(a).all() for a in (r,c,b)) or np.any(r<0) or np.any(r>self.n) or np.any(c<0): raise ValueError('invalid event')
        # No unmetered local charge creation: scale tolerance to actual charge turnover.
        delta_charge=(c-r)@self.charge; scale=(c+r)@np.abs(self.charge)
        if np.any(np.abs(delta_charge)>1e-12*scale): raise ValueError('event changes net charge; explicit charge port required')
        v=self.velocities(z); a=self.n-r; t=a+c
        p=a[:,:,None]*v+c[:,:,None]*b
        vv=np.divide(p,t[:,:,None],out=np.zeros_like(p),where=t[:,:,None]>0)
        weight=self.grid.dx*self.mass[None,:]/2
        birth_in=weight*c*np.sum(b*b,axis=2); removed_out=weight*r*np.sum(v*v,axis=2)
        mixing=weight*np.divide(a*c,t,out=np.zeros_like(t),where=t>0)*np.sum((v-b)**2,axis=2)
        after=PopulationGrid(self.grid.dx,self.grid.mu,self.eps,self.mass,self.charge,t,self.nu if nu is None else nu,self.B if B is None else B,self.load,self.grid.periodic)
        out=np.zeros(after.grid.size)
        for i,((old,_,_),(new,_,_)) in enumerate(zip(self.grid.local,after.grid.local)):
            out[new.start:new.start+3]=z[old.start:old.start+3]
            for k,j in enumerate(np.flatnonzero(t[i]>0)):
                out[new.start+3+3*k:new.start+6+3*k]=np.sign(self.charge[j])*np.sqrt(self.grid.dx*self.mass[j]*t[i,j])*vv[i,j]
        for old,new in zip(self.grid.faces,after.grid.faces): out[new]=z[old]
        # Per species mean-energy accounting, plus complete numerical-state balance.
        expected=weight*(t*np.sum(vv*vv,axis=2)-self.n*np.sum(v*v,axis=2))
        residual=expected-birth_in+removed_out+mixing
        global_res=(out@out-z@z)/2-birth_in.sum()+removed_out.sum()+mixing.sum()
        assert np.max(np.abs(residual))<1e-10 and abs(global_res)<1e-10
        return after,out,dict(birth=birth_in,removed=removed_out,mixing=mixing,max_residual=max(float(np.max(np.abs(residual))),abs(float(global_res))))


def fixtures():
    # Charge-neutral pair creation/removal, unequal masses, signed gyro rotation.
    m=[1.,4.]; q=[-1.,1.]; eps=[1.,2.]; B=[[0.,0.,1.],[.2,.1,-.5]]; nu=[[.3,.5],[.2,.4]]
    worst=0.; cases=0
    for n in (0.,1.,2.):
        for r in np.arange(n+1):
            for c in (0.,1.,2.):
                p=PopulationGrid(.7,[1.2],eps,m,q,[[n,n],[n,n]],nu,B,[.1,0.]); z=np.linspace(-.5,.5,p.grid.size)
                for sign in (-1.,0.,1.):
                    b=np.array([[[.2,sign,.1],[sign,-.1,.3]],[[sign,.2,.1],[.2,.3,sign]]]); rr=np.full_like(p.n,r); cc=np.full_like(p.n,c)
                    after,v,w=p.event(z,rr,cc,b); worst=max(worst,w['max_residual']); cases+=1
                    assert np.all(w['mixing']>=0) and np.all(after.n==n-r+c)
                    # Every field and face value survives the change of species chart.
                    for old,new in zip(p.grid.faces,after.grid.faces): assert np.array_equal(z[old],v[new])
                    for (old,_,_),(new,_,_) in zip(p.grid.local,after.grid.local): assert np.array_equal(z[old.start:old.start+3],v[new.start:new.start+3])
    p=PopulationGrid(.7,[1.2],eps,m,q,[[1.,1.],[1.,1.]],nu,B,[.1,0.]); z=np.linspace(-.5,.5,p.grid.size)
    try: p.event(z,np.zeros_like(p.n),np.array([[1.,0.],[0.,0.]]),np.zeros((*p.n.shape,3)))
    except ValueError: pass
    else: raise AssertionError('unmetered charge created')
    initial=z.copy(); initial_n=p.n.copy(); ext=ctrl=mat=load=birth=removed=mix=0.; sequence=[]
    for r,c in ((1.,0.),(0.,1.),(1.,1.)):
        h=.04; v,w,err=verify_step(p.grid,z,h,p.grid.prepare(h),(.1,.2),(-.2,.1)); worst=max(worst,err)
        ext+=w['exterior_inward'].sum(); ctrl+=w['controller']; mat+=w['material_loss'].sum(); load+=w['load'].sum()
        p,z,w=p.event(v,np.full_like(p.n,r),np.full_like(p.n,c),np.zeros((*p.n.shape,3)))
        birth+=w['birth'].sum(); removed+=w['removed'].sum(); mix+=w['mixing'].sum(); worst=max(worst,w['max_residual']); sequence.append(p.grid.size)
    res=(z@z-initial@initial)/2+mat+load+removed+mix-ext-ctrl-birth
    assert abs(res)<1e-10 and np.array_equal(p.n,initial_n) and np.linalg.norm(z-initial)>1e-3
    return dict(event_fixtures=cases,charge_creation_rejected=True,max_local_residual=worst,combined_sequence_residual=float(res),sequence_state_dimensions=sequence,density_return_without_state_return=True,full_state_difference=float(np.linalg.norm(z-initial)),physical_admission=False)

if __name__=='__main__': print(json.dumps(fixtures(),indent=2))

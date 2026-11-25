"""P0P: externally driven extension of original reactive_pnp_369.
Blocking ionic boundary, grounded electrostatic Poisson, fixed geometry.
Prescribed inductive edge voltage is not self-consistent Maxwell backreaction.
Numerical synthetic assay, not BH4 calibration or kernel acceptance.
"""
import numpy as np
from scipy.optimize import root
import reactive_pnp_369 as base

L,R=np.array(base.BONDS).T

def hopf_cochain():
    """A0 integral, in EXACT base.BONDS order; evaluated in float64."""
    out=[]
    for i,j in base.BONDS:
        p=np.array(base.POINTS[i],dtype=float); q=np.array(base.POINTS[j],dtype=float)
        axis=int(np.flatnonzero(q-p)[0]); x,y,z=p
        c=1+sum(p[k]**2 for k in range(3) if k!=axis)
        def primitive(v):
            I1=np.arctan(v/np.sqrt(c))/np.sqrt(c)
            I2=v/(2*c*(c+v*v))+I1/(2*c)
            if axis==0: return -4*z/(2*(c+v*v))-4*y*I2
            if axis==1: return -4*z/(2*(c+v*v))+4*x*I2
            return 2*I1+4*(1-c)*I2
        out.append(primitive(q[axis])-primitive(p[axis]))
    return np.array(out)

def checked_drive(voltage):
    v=np.asarray(voltage,dtype=float)
    if v.shape!=(54,) or not np.all(np.isfinite(v)):
        raise ValueError('finite signed voltage for each original bond required')
    return v

def flux_parts(c,phi,m,voltage):
    u=(phi[R]-phi[L]-voltage)[:,None]*m.z[None,:]*m.F/m.RT
    a=c[L]*base.bernoulli(u); b=c[R]*base.bernoulli(-u)
    return a,b,(m.D/m.h)*(a-b)

def rhs(c,m,voltage,phi=None):
    if phi is None: phi=base.poisson(c,m)
    a,b,J=flux_parts(c,phi,m,voltage)
    out=np.zeros_like(c)
    np.add.at(out,L,-J/m.h); np.add.at(out,R,J/m.h)
    if len(m.kf): out+=base.reaction_rates(c,m)@(m.products-m.reactants)
    return out

def implicit_step(c0,dt,m,voltage,tol=1e-9):
    voltage=checked_drive(voltage); c0=np.asarray(c0,dtype=float)
    if c0.shape!=(27,len(m.z)) or not np.all(np.isfinite(c0)) or np.any(c0<=0) or not np.isfinite(dt) or dt<=0:
        raise ValueError('positive finite original state and timestep required')
    p0=base.poisson(c0,m)
    def residual(y):
        c=np.exp(np.clip(y.reshape(c0.shape),-60,60))
        return (c-c0-dt*rhs(c,m,voltage)).ravel()
    sol=root(residual,np.log(c0).ravel(),options={'xtol':1e-10})
    if not np.all(np.isfinite(sol.x)) or np.any(np.abs(sol.x)>=59): raise RuntimeError('invalid log root')
    c=np.exp(sol.x.reshape(c0.shape)); p=base.poisson(c,m)
    defect=c-c0-dt*rhs(c,m,voltage,p); err=float(np.max(np.abs(defect)))
    if not np.isfinite(err) or err>tol: raise RuntimeError('implicit residual unpaid')
    a,b,J=flux_parts(c,p,m,voltage)
    if np.any(a<=0) or np.any(b<=0): raise RuntimeError('nonpositive SG branch')
    mu=m.standard_mu[None,:]+m.RT*np.log(c)+m.F*p[:,None]*m.z[None,:]
    # All powers have the same volume/area factors as original solver.
    W=m.h**2*float(np.sum(J*m.F*m.z[None,:]*voltage[:,None]))
    Dt=m.h**2*m.RT*float(np.sum(J*(np.log(a)-np.log(b))))
    Dr=-m.h**3*float(np.sum(base.reaction_rates(c,m)*(mu@(m.products-m.reactants).T)))
    E0=base.free_energy(c0,p0,m); E1=base.free_energy(c,p,m)
    Bchem=m.h**3*m.RT*float(np.sum(c0*np.log(c0/c)-c0+c))
    Belec=.5*m.h**3*m.epsilon*float((p-p0)@base.poisson_matrix(m.h)@(p-p0))
    Rnum=m.h**3*float(np.sum(mu*defect))
    closure=(E1-E0)-dt*(W-Dt-Dr)+Bchem+Belec-Rnum
    charge=float(m.h**3*np.sum((c-c0)*m.F*m.z[None,:]))
    poisson=float(np.max(np.abs(m.epsilon*base.poisson_matrix(m.h)@p-(m.F*(c@m.z)+m.fixed_charge))))
    scale=max(1,abs(E0),abs(E1),abs(dt*W),abs(dt*Dt),abs(dt*Dr))
    vals=[W,Dt,Dr,E0,E1,Bchem,Belec,Rnum,closure,charge,poisson]
    if not np.all(np.isfinite(vals)) or min(Dt,Dr,Bchem,Belec)<-1e-9*scale or abs(closure)>1e-9*scale or abs(charge)>1e-7 or poisson>1e-8:
        raise RuntimeError('driven ledger or conservation unpaid')
    return c,dict(residual=err,minimum=float(c.min()),work=dt*W,transport_loss=dt*Dt,reaction_loss=dt*Dr,
                  chemical_bregman=Bchem,electrostatic_bregman=Belec,numerical_work=Rnum,closure=closure,
                  energy_change=E1-E0,charge_defect=charge,poisson_residual=poisson)

def assay():
    # Original 3-species synthetic reaction plus 29x12 size analogue.
    # No authentic BH4 species or measured parameters used.
    records=[]; u=hopf_cochain()
    for n in (3,29):
        if n==3:
            A=np.array([[1,1,0]]); B=np.array([[0,0,1]]); z=np.array([1,-1,0])
        else:
            A=np.eye(n,dtype=int)[0:24:2]; B=np.eye(n,dtype=int)[1:24:2]; z=np.repeat(np.arange(15)%3-1,2)[:n]
        m=base.Model(z=z,D=np.linspace(.08,.12,n),reactants=A,products=B,kf=np.full(len(A),.04),kb=np.full(len(A),.04),standard_mu=np.zeros(n))
        c0=1+.15*np.sin(np.arange(27*n).reshape(27,n)); p=base.poisson(c0,m)
        np.testing.assert_allclose(flux_parts(c0,p,m,np.zeros(54))[2],base.native_flux(c0,p,m),rtol=1e-13,atol=1e-14)
        for amp in (0.,-1.,1.,4.):
            c,receipt=implicit_step(c0,.08,m,amp*u)
            if n==3:
                np.testing.assert_allclose((c-c0).sum(axis=0)@np.array([[1,0],[0,1],[1,1]]),0,atol=1e-8)
            else: np.testing.assert_allclose((c-c0).sum(axis=0)@np.repeat(np.eye(15),2,axis=0)[:n],0,atol=1e-8)
            records.append(dict(species=n,drive=amp,**receipt))
    # Equilibrium uniform neutral pair: drive causes positive free-energy change.
    m=base.Model(z=np.array([1,-1]),D=np.ones(2)*.1,reactants=np.zeros((0,2),int),products=np.zeros((0,2),int),kf=np.zeros(0),kb=np.zeros(0),standard_mu=np.zeros(2))
    _,r=implicit_step(np.ones((27,2)),.08,m,u)
    assert r['energy_change']>0 and r['work']>0
    records.append(dict(species=2,drive=1.,**r))
    for bad in (np.zeros(53),np.full(54,np.nan)):
        try: checked_drive(bad)
        except ValueError: pass
        else: raise AssertionError('invalid drive accepted')
    return records

if __name__=='__main__':
    import json
    print(json.dumps(assay(),indent=2))

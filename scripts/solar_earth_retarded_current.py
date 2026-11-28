"""Local retarded current step, with original-row stiffness and tensor replay.
Frozen coefficients and prescribed fields only; not spatial Maxwell propagation.
"""
import hashlib
import json
import sys
from pathlib import Path
import h5py
import numpy as np
import sympy as s
from scipy.constants import elementary_charge as e, electron_mass as me, atomic_mass as u
from scipy.linalg import expm
from scipy.integrate import quad
from solar_earth_model_inputs import radar
from solar_earth_collision_tensor import rates, composition


def phi(z):
    """Entire functions (exp(z)-1)/z and (exp(z)-1-z)/z²."""
    if abs(z) < 1e-3:
        a, b, t = 1.+0j, .5+0j, 1.+0j
        for k in range(1, 10):
            t *= z/(k+1)
            a += t
            b += t/(k+2)
        return a, b
    a = np.expm1(z)/z
    return a, (a-1)/z


def cross(b):
    x,y,z = b
    return np.array([[0.,-z,y],[z,0.,-x],[-y,x,0.]])


def frozen_maps(nu, omega, b, h):
    """T=exp(hA), F=int T, G=int F; A=-nu I-omega [b×]."""
    if not np.isfinite([nu,omega,h]).all() or nu < 0 or h < 0:
        raise ValueError('invalid frozen step')
    b=np.asarray(b,dtype=float)
    if b.shape != (3,) or not np.isclose(b@b,1,rtol=0,atol=1e-12):
        raise ValueError('unit magnetic axis required (arbitrary axis at zero field)')
    P=np.outer(b,b); Q=np.eye(3)-P; J=cross(b)
    zp=-nu*h; z=complex(-nu,-omega)*h
    fp,gp=phi(zp); f,g=phi(z)
    def lift(p,t): return p.real*P+t.real*Q+t.imag*J
    return lift(np.exp(zp),np.exp(z)),h*lift(fp,f),h*h*lift(gp,g)


def step(j,E,D,nu,omega,b,h):
    """Current, time integral and signed field work for prescribed constant E.
    Loss is the analytical energy-balance remainder, not an independent meter.
    """
    j=np.asarray(j,dtype=float); E=np.asarray(E,dtype=float)
    if j.shape != (3,) or E.shape != (3,) or not np.isfinite([*j,*E,D]).all() or D < 0:
        raise ValueError('invalid current state')
    T,F,G=frozen_maps(nu,omega,b,h)
    if D == 0:
        if np.any(j): raise ValueError('nonzero current in empty species')
        return j.copy(),j.copy(),0.,0.,0.
    j1=T@j+D*(F@E); integral=F@j+D*(G@E)
    work=float(E@integral); delta=float((j1-j)@(j1+j)/(2*D)); loss=work-delta
    return j1,integral,work,delta,loss


def fixture_tests():
    # Analytic local storage identity and propagator/transfer identity.
    D,nu,w=s.symbols('D nu w',positive=True); j,E=s.Matrix(s.symbols('j:3',real=True)),s.Matrix(s.symbols('E:3',real=True)); J=s.Matrix([[0,-1,0],[1,0,0],[0,0,0]])
    A=-nu*s.eye(3)-w*J
    assert s.expand(j.dot(A*j+D*E)/D-j.dot(E)+nu*j.dot(j)/D)==0
    assert A+A.T==-2*nu*s.eye(3)
    # Independently use an augmented dense exponential to integrate the current.
    # Dissipation is separately quadrature-integrated, not merely ledger rearrangement.
    b=np.array([2.,-1.,2.])/3; j=np.array([1.,-2.,.3]); E=np.array([-.4,.7,1.2]); D=1.7
    count=0; max_state=0.; max_loss=0.
    for nu in (0.,.2,3.):
        for om in (-7.,0.,11.):
            for h in (1e-6,.07,1.2):
                A=-nu*np.eye(3)-om*cross(b)
                L=np.zeros((7,7)); L[:3,:3]=A; L[:3,3]=D*E; L[4:,:3]=np.eye(3)
                init=np.r_[j,1.,0.,0.,0.]; ref=expm(h*L)@init
                j1,integ,W,dK,Q=step(j,E,D,nu,om,b,h)
                err=np.max(np.abs(np.r_[j1-ref[:3],integ-ref[4:]])); max_state=max(max_state,float(err)); assert err<1e-11
                def integrand(t):
                    z=(expm(t*L)@init)[:3]; return nu*(z@z)/D
                q=quad(integrand,0,h,epsabs=1e-11,epsrel=1e-11)[0]
                err=abs(Q-q); max_loss=max(max_loss,err); assert err<1e-10 and Q>=-1e-12
                a=step(j,E,D,nu,om,b,h/2); c=step(a[0],E,D,nu,om,b,h/2)
                assert np.allclose(c[0],j1,atol=1e-11) and np.allclose(a[1]+c[1],integ,atol=1e-11)
                assert abs(a[4]+c[4]-Q)<1e-10
                count+=1
    assert step(np.zeros(3),E,0.,1.,0.,b,.1)[2:]==(0.,0.,0.)
    try: step(j,E,0.,1.,0.,b,.1)
    except ValueError: pass
    else: raise AssertionError('empty-state nonzero current accepted')
    return {'symbolic_identities':2,'independent_driven_fixtures':count,'max_state_integral_error':max_state,'max_loss_error':max_loss,'empty_chart_guard':True}



def periodic_window(fields, durations, species, b):
    """Periodic current state for a prescribed piecewise-constant field history.
    Each species tuple is (D, nu, signed omega), positive damping required.
    No optimization of, or inference about, the physical field.
    """
    fields=np.asarray(fields,float); durations=np.asarray(durations,float)
    if fields.shape!=(len(durations),3) or len(durations)==0 or np.any(durations<=0):
        raise ValueError('invalid window')
    if any(D<0 or nu<=0 for D,nu,om in species): raise ValueError('damped species required')
    if not np.isfinite(fields).all() or not np.isfinite(durations).all(): raise ValueError('nonfinite window')
    total=float(durations.sum()); Ebar=durations@fields/total
    currents=[]; work=0.; loss=0.; mean_loss=0.; restore=0.; delta=0.
    for D,nu,om in species:
        if not D: currents.append(np.zeros(3)); continue
        T=np.eye(3); offset=np.zeros(3)
        for E,h in zip(fields,durations):
            A,F,_=frozen_maps(nu,om,b,h); T=A@T; offset=A@offset+D*(F@E)
        initial=np.linalg.solve(np.eye(3)-T,offset); j=initial.copy(); integ=np.zeros(3)
        for E,h in zip(fields,durations):
            j,J,W,dK,Q=step(j,E,D,nu,om,b,h); integ+=J; work+=W; loss+=Q; delta+=dK
        restore=max(restore,float(np.linalg.norm(j-initial)))
        currents.append(integ/total); mean_loss+=nu*float(integ@integ)/(D*total)
    return dict(mean_currents=np.array(currents),mean_field=Ebar,work=work,loss=loss,storage_change=delta,mean_current_loss=mean_loss,fluctuation_loss=loss-mean_loss,return_error=restore)


def periodic_tests():
    # Exact Jensen identity on a weighted discrete carrier. Continuous analogue
    # follows by expanding the square under integration, with the same mean.
    t1,t2=s.symbols('t1 t2',positive=True); x,y=s.symbols('x y',real=True); z=(t1*x+t2*y)/(t1+t2)
    assert s.cancel(t1*x*x+t2*y*y-(t1+t2)*z*z-t1*(x-z)**2-t2*(y-z)**2)==0
    b=np.array([0.,0.,1.]); ray=np.array([.8,0,.6]); species=[(2.,.3,7.),(.7,1.2,-2.)]
    # Explicitly hypothetical local linear fields and positive rates, not an experiment.
    h=np.array([.2,.3,.4,.5]); E=np.array([[.2,.3,0],[-.4,.7,0],[.6,-.3,0],[.1,-.1,0]])
    mean=h@E/h.sum(); const=np.tile(mean,(len(h),1)); count=0; max_return=0.; max_mean_err=0.
    for scale in (0.,.1,1.,3.):
        v=periodic_window(const+scale*(E-const),h,species,b); base=periodic_window(const,h,species,b)
        expect=np.array([np.linalg.solve(nu*np.eye(3)+om*cross(b),D*mean) for D,nu,om in species]); err=float(np.max(np.abs(v['mean_currents']-expect))); max_mean_err=max(max_mean_err,err)
        assert err<1e-12 and v['fluctuation_loss']>=-1e-12 and abs(v['work']-v['loss'])<1e-12
        assert v['return_error']<1e-12 and abs(v['storage_change'])<1e-12; max_return=max(max_return,v['return_error'])
        assert abs(base['work']-v['mean_current_loss'])<1e-12
        if scale: assert v['work']>base['work']
        else: assert abs(v['fluctuation_loss'])<1e-12
        # Same mean current observer, different energy; no hidden source assigned.
        assert np.allclose(v['mean_currents']@ray,base['mean_currents']@ray,atol=1e-12)
        count+=1
    return {'weighted_variance_identity':1,'periodic_fixtures':count,'max_return_error':max_return,'max_mean_current_error':max_mean_err}


def replay(root,packet):
    rows=radar(root); raw=packet.read_bytes(); digest=hashlib.sha256(raw).hexdigest()
    assert digest=='d771b81b3498e4cf9424325afe9e27f1c3f8125d0ba6c608c175cb62bd955fb6'
    model=[json.loads(x) for x in raw.splitlines()]; assert len(rows)==len(model)==3087
    for r,x in zip(rows,model): assert all(r[k]==x[k] for k in ('record','range_km','utc'))
    with h5py.File(root/'MAD6400_2017-12-18_bella_60@vhf.hdf5') as f: a=f['Data/Table Layout'][:]
    dur={(int(x['recno']),float(x['range'])):float(x['ut2_unix']-x['ut1_unix']) for x in a}
    h=np.array([dur[r['record'],r['range_km']] for r in rows])[:,None]
    B=np.array([x['B_NED_T'] for x in model]); mag=np.linalg.norm(B,axis=1); b=B/mag[:,None]
    mass=np.array([me,30.5*u,16*u]); charge=e*np.array([-1,1,1]); om=mag[:,None]*charge/mass
    ne=np.array([r['ne'] for r in rows]); D=ne[:,None]*np.column_stack([np.ones(len(rows)),composition(root,rows)])*charge**2/mass
    P=b[:,:,None]*b[:,None,:]; Q=np.eye(3)-P; J=np.array([cross(x) for x in b])
    quant=lambda x:np.quantile(x,[0,.5,1],axis=0).tolist(); out={}; errors=[]
    for label in ('history','daily'):
        nu=rates(rows,np.array([x['neutral_'+label+'_SI'] for x in model]))
        # Exact frozen homogeneous contraction, versus midpoint stability function.
        z=h*(-nu-1j*om); zp=-h*nu
        cayley=np.abs((1+z/2)/(1-z/2)); cayley_p=np.abs((1+zp/2)/(1-zp/2))
        assert np.all(cayley<=1+1e-14) and np.all(cayley_p<=1+1e-14)
        # Retarded causal resolvent: integral exp(A t) exp(iw t) D dt.
        # Compare independently assembled eigenprojectors with original tensor.
        plus=(Q-1j*J)/2; minus=(Q+1j*J)/2
        for f in (0,3.915,7.83,7800):
            a=nu-2j*np.pi*f
            r=np.sum(D/a,axis=1)[:,None,None]*P+np.sum(D/(a+1j*om),axis=1)[:,None,None]*plus+np.sum(D/(a-1j*om),axis=1)[:,None,None]*minus
            orig=np.array([x['tensor_by_history_and_frequency'][label][str(f)] for x in model]); orig=orig[...,0]+1j*orig[...,1]
            err=float(np.max(np.linalg.norm(r-orig,axis=(1,2))/np.linalg.norm(orig,axis=(1,2)))); assert err<1e-10; errors.append(err)
        active=D>0
        out[label]={'exact_log10_free_memory':quant(zp/np.log(10)), 'midpoint_perp_free_memory':quant(cayley),'midpoint_parallel_free_memory':quant(cayley_p),'active_species_rows':int(active.sum()),'active_perp_midpoint_above_half':int((active&(cayley>.5)).sum()),'active_exact_below_1e_30':int((active&(zp<-30*np.log(10))).sum())}
    return {'rows':len(rows),'records':len(set(r['record'] for r in rows)),'packet_sha256':digest,'species_history_slots':len(rows)*3*2,'retarded_tensor_checks':len(rows)*4*2,'max_retarded_tensor_relative_error':max(errors),'histories':out}

if __name__=='__main__':
    print(json.dumps({'status':'CONDITIONAL_LOCAL_RETARDED_CURRENT','fixtures':fixture_tests(),'periodic':periodic_tests(),'replay':replay(Path(sys.argv[1]),Path(sys.argv[2])),'physical_admission':False,'scope':'Frozen local coefficients, analytic prescribed-field step, no measured E or propagation; midpoint comparison uses radar integration duration only as a diagnostic, not actual solver step. Zero populations excluded from active counts. No physical extraction.'},indent=2))

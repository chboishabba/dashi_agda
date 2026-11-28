"""Same-boundary frequency-lift of original SI shell + signed Drude material.
Synthetic dimensionless added sheet; not calibrated thermal or HF response.
Original donor definition prefix and signed sideband source are hash pinned.
"""
from pathlib import Path
import hashlib
import numpy as np
import sympy as sp
from scipy.linalg import block_diag
from itertools import product
from solar_earth_thermal_vector import sideband
import solar_earth_thermal_vector as thermal

HERE=Path(__file__).resolve().parent
raw=(HERE/'check_smith_filsinger_solar_si_covariance.py').read_bytes()
prefix=raw.split(b'\nrows=[];maxledger=')[0]
assert hashlib.sha1(prefix).hexdigest()=='ab105e28cf1abbd145d4fd7a02daecfea8d124cc'
raw2=Path(thermal.__file__).read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw2)).encode()+b'\0'+raw2).hexdigest()=='2f897b0fcc6fe710462c35c2b9e8069396ab7083'
env={};exec(compile(prefix,'original_si_covariance_prefix','exec'),env)
angular,trace,shell0,kappa,yg,R,axis=[env[k] for k in ('angular','trace','shell','kappa','yg','R','axis')]

def symbolic():
    # D is the positive Drude weight; nu>=0, gyro force does no work.
    j,D,nu,E,dD=sp.symbols('j D nu E dD',real=True)
    U=j*j/(2*D);jd=D*E-nu*j
    assert sp.cancel(sp.diff(U,j)*jd+sp.diff(U,D)*dD-j*E+nu*j*j/D+dD*j*j/(2*D**2))==0
    # Fixed D and real collision modulation => passive electrical port.
    a,b,d=sp.symbols('a b d',real=True)
    assert sp.expand((a+b)**2+(a-b)**2-2*(a*a+b*b))==0


def material(freqs,nu=30.,D=30.,gyro=10.,delta=10.):
    """Finite signed Floquet ladder; cosine nu=nu0+2 delta (axis.n) cos.
    D fixed. Same added sheet on passive and modulated cases; normalized units.
    """
    n=len(freqs);assert nu>2*abs(delta) and D>0
    b=axis;J=np.cross(b,np.eye(3)).T
    Y=np.zeros((16*n,16*n),complex);parts=[]
    for p in product((-1,0,1),repeat=3):
        nn=sum(t!=0 for t in p)
        if not nn:continue
        site=np.array(p)/np.sqrt(nn);w={1:1/21,2:4/105,3:9/280}[nn]
        B=block_diag(*([angular(site)]*n));q=delta*(site@axis)
        # +i omega shell convention; donor sideband uses -i omega.
        A=block_diag(*[(nu+2j*np.pi*f)*np.eye(3)+gyro*J for f in freqs])
        for k in range(n-1):
            A[3*k:3*k+3,3*k+3:3*k+6]=q*np.eye(3)
            A[3*k+3:3*k+6,3*k:3*k+3]=q*np.eye(3)
        H=(A+A.conj().T)/2;assert np.linalg.eigvalsh(H).min()>0
        L=D*np.linalg.solve(A,B);Y+=w*B.T@L;parts.append((w,B,L,H,q,D))
    assert np.linalg.eigvalsh((Y+Y.conj().T)/2).min()>0
    return Y,parts


def derivative_test(freqs):
    f,g=freqs[:2];nu,D,gyro=30.,30.,10.;b=axis;J=np.cross(b,np.eye(3)).T
    E=np.array([1.,2.,-1.]);A=block_diag(*[(nu+2j*np.pi*v)*np.eye(3)+gyro*J for v in (f,g)])
    B=np.block([[np.zeros((3,3)),np.eye(3)],[np.eye(3),np.zeros((3,3))]])
    rhs=np.r_[D*E,np.zeros(3)];der=-np.linalg.solve(A,B@np.linalg.solve(A,rhs))[3:]
    orig=sideband(nu,gyro,b,D,1,0,-2*np.pi*(g-f),-2*np.pi*f,E)
    assert np.linalg.norm(der-orig)<1e-12
    return float(np.linalg.norm(der-orig))

CACHE={}
def radial(f):
    if abs(f) not in CACHE:CACHE[abs(f)]=shell0(abs(f))[:5]
    return tuple(m.conj() if f<0 else m for m in CACHE[abs(f)])


def exterior(freqs,delta,nu=30.,D=30.):
    mats=list(zip(*[radial(f) for f in freqs]));A,B,C,F,S=[block_diag(*m) for m in mats]
    Y,parts=material(freqs,nu,D,delta=delta)
    U=np.eye(len(A))+S+Y;M=U@(A-B*yg)-(C-F*yg)
    Z=np.linalg.solve(M,F-U@B);V=np.linalg.solve(M,2*np.eye(len(A)))
    assert np.linalg.eigvalsh((Z+Z.conj().T)/2).min()>0
    return A,B,C,F,S,Y,Z,V,parts


def optimal(ext,freqs,area=1e6,aspect=1.,angle=np.pi/2,floor=.1):
    A,B,C,F,S,Y,Z,V,parts=ext;n=len(freqs);center=n//2
    T0=trace(area,aspect,angle);T=block_diag(*([T0]*n))
    lengths=R*np.linalg.norm(T0[:,:3],axis=1)/np.sqrt(1.5)
    total=5*np.sqrt(area)*1e-6;uniform=total*lengths/lengths.sum()
    u=np.zeros((16*n,3),complex);u[16*center+np.array([0,1,3]),np.arange(3)]=1/np.sqrt(kappa)
    voc=V@u;vp=T@voc;Zp=T@Z@T.T/kappa;H=(Zp+Zp.conj().T)/2
    rho=1.68e-8;best=None;upper=0.;maxerr=0.
    for volume in [uniform]+[floor*uniform+(1-floor)*total*np.eye(7)[k] for k in range(7)]:
        rc=rho*lengths**2/volume;cu=np.tile(rc,n);G=H+np.diag(cu)
        # Full arbitrary current upper relaxation, same copper on all bands.
        i=np.linalg.solve(G,vp)/2
        val=float(np.mean(np.sum((i.conj()*vp-i.conj()*(G@i)).real,axis=0)))
        up=float(np.mean(np.sum(abs(vp)**2/cu[:,None],axis=0))/4);upper=max(upper,up)
        assert val<=up*(1+1e-10)
        # Real positive edge load = copper resistance; independent ports,
        # no conjugate matching or cross-frequency receiver command needed.
        ir=np.linalg.solve(Zp+2*np.diag(cu),vp)
        passive=float(np.mean(np.sum(cu[:,None]*abs(ir)**2,axis=0)))
        density=float(np.max(np.sqrt(np.sum(abs(i.reshape(n,7,3))**2,axis=0))/(volume/lengths)[:,None]))
        assert density<=1e6
        j=T.T@i/kappa;e=voc-Z@j;h=-yg*e-j;e1=A@e+B@h;h1=C@e+F@h
        nat=1-kappa*np.sum(abs(e1-u)**2,axis=0)
        sheet=kappa*np.sum((e1.conj()*(S@e1)).real,axis=0)
        extra=kappa*np.sum((e1.conj()*(Y@e1)).real,axis=0)
        heat=np.zeros(3);omitted=np.zeros(3)
        for w,BB,L,HH,q,Dweight in parts:
            js=L@e1;heat+=kappa*w*np.sum((js.conj()*(HH@js)).real,axis=0)/Dweight
            omitted+=w*q*q*(np.sum(abs(js[:3])**2,axis=0)+np.sum(abs(js[-3:])**2,axis=0))
        # Heat identity for fixed D; residual is omitted current-equation RHS,
        # not an upper bound on the full Maxwell solution error.
        assert np.max(abs(extra-heat))<1e-11
        ground=kappa*yg*np.sum(abs(e)**2,axis=0)
        radial_loss=kappa*np.sum((e.conj()*h-e1.conj()*h1).real,axis=0)
        port=np.sum((i.conj()*(T@e)).real,axis=0);copper=np.sum(cu[:,None]*abs(i)**2,axis=0)
        err=float(np.max(abs(nat-sheet-extra-ground-radial_loss-port)));maxerr=max(maxerr,err)
        assert err<1e-8 and abs(float(np.mean(port-copper))-val)<1e-18
        row=dict(ideal=val,diagonal_load=passive,natural=float(nat.mean()),extra_sheet_heat=float(extra.mean()),copper=float(copper.mean()),other_loss=float(np.mean(sheet+ground+radial_loss)),sideband_voltage=float(np.linalg.norm(np.delete((T@e).reshape(n,7,3),center,axis=0))),omitted_current_rhs_norm=float(np.sqrt(omitted.mean())),density=density)
        if best is None or val>best['ideal']:best=row
    return dict(best,allocation_upper=upper,max_ledger=maxerr)


def signed_pair_bound(carrier,mod,nu=30.,gyro=10.,delta=10.):
    # Exact symmetric sideband elimination at zero impressed sideband field.
    a,w=sp.symbols('a w',real=True)
    assert sp.cancel(1/(a+sp.I*w)+1/(a-sp.I*w)-2*a/(a*a+w*w))==0
    J=np.cross(axis,np.eye(3)).T;A=(nu+2j*np.pi*carrier)*np.eye(3)+gyro*J
    W=2*np.pi*mod;I=np.eye(3);norm=np.linalg.norm(A,2)
    direct=delta**2*(np.linalg.inv(A+1j*W*I)+np.linalg.inv(A-1j*W*I))
    paired=2*delta**2*A@np.linalg.inv(A@A+W*W*I)
    assert np.linalg.norm(direct-paired)<1e-12
    bound=2*delta**2*norm/(W*W-norm*norm);assert W>norm and np.linalg.norm(paired,2)<=bound*(1+1e-10)
    return dict(signed_pair_norm=float(np.linalg.norm(paired,2)),upper=float(bound),relative_to_nu=float(bound/nu))


def thermal_mean_reverse(base,active):
    # Same mean temperature, bath, linear cooling and other heat sources;
    # stationary passive reference is assumed thermally balanced.
    # Integrating C*Tdot=Qnat+Qheater-k*(T-Tbath) over a restored cycle
    # forces mean absorbed heater = Qpassive-Qactive.
    q0,q1=base['extra_sheet_heat'],active['extra_sheet_heat'];heater=q0-q1
    margin=active['allocation_upper']-base['diagonal_load']
    return dict(required_mean_absorbed_heater=heater,gross_relaxation_margin=margin,
                heating_only_compatible_mean=heater>=0,paid_margin_upper_at_selected_heat=margin-max(0,heater))


def four_world(freqs):
    # Distinguish independent low source from direct high-frequency driver.
    # Modulation is imposed when driver on, not inferred from its incident power.
    base=exterior(freqs,0);active=exterior(freqs,10);n=len(freqs);center=n//2
    T0=trace(1e6,1.,np.pi/2);T=block_diag(*([T0]*n));length=R*np.linalg.norm(T0[:,:3],axis=1)/np.sqrt(1.5)
    volume=.005*length/length.sum();cu=np.tile(1.68e-8*length**2/volume,n)
    low=np.zeros(16*n,complex);high=low.copy();low[16*center]=1/np.sqrt(kappa);high[16*(center+1)]=1/np.sqrt(kappa)
    def world(ext,u):
        A,B,C,F,S,Y,Z,V,parts=ext
        Zp=T@Z@T.T/kappa; i=np.linalg.solve(Zp+2*np.diag(cu),T@V@u)
        e=V@u-Z@T.T@i/kappa;h=-yg*e-T.T@i/kappa;e1=A@e+B@h;h1=C@e+F@h
        incident=kappa*np.vdot(u,u).real;net=incident-kappa*np.vdot(e1-u,e1-u).real
        loss=kappa*(np.vdot(e1,(S+Y)@e1).real+yg*np.vdot(e,e).real+np.vdot(e,h).real-np.vdot(e1,h1).real)
        load=np.sum(cu*abs(i)**2);assert abs(net-loss-2*load)<1e-8
        return float(np.sum(cu[7*center:7*(center+1)]*abs(i[7*center:7*(center+1)])**2)),float(load)
    zero=world(base,low*0);natural=world(base,low);driver=world(active,high);low_active=world(active,low)
    both=(np.array(world(active,low+high))+np.array(world(active,low-high)))/2
    assert np.allclose(both,np.array(low_active)+driver,rtol=1e-10,atol=1e-28)
    assert zero==(0.,0.) and world(active,low*0)==zero
    interaction=both-np.array(natural)-driver
    return dict(frequencies=freqs,output_order=['LF_load','all_load'],off=zero,natural_only=natural,
                driver_only=driver,both_phase_average=both.tolist(),interaction=interaction.tolist(),
                driver_incident_W=1.,both_minus_driver_input_and_natural=(both-np.array(natural)-1).tolist())


def run():
    symbolic();thermal.fixtures();
    for carrier,mod,order in [(7.83,3.915,1),(3.915,7800.,1),(3.915,7800.,2)]:
        freqs=[carrier+j*mod for j in range(-order,order+1)]
        assert all(f!=0 for f in freqs) and len(set(map(abs,freqs)))==len(freqs)
        err=derivative_test(freqs);base=exterior(freqs,0);active=exterior(freqs,10)
        static=optimal(base,freqs);dyn=optimal(active,freqs)
        print(dict(freqs=freqs,derivative_error=err,passive=static,modulated=dyn,ideal_delta=dyn['ideal']-static['ideal'],thermal_reverse=thermal_mean_reverse(static,dyn)),flush=True)
    print('SIGNED_PAIR',signed_pair_bound(3.915,7800.),flush=True)
    print('FOUR_WORLDS',four_world([-7792.17,3.915,7800.]),flush=True)
    print('PASS signed coupled exterior, work-adjoint seven-edge traces, fixed-D passivity, equal material and omitted ladder residual; no HF actuation cost admitted')
if __name__=='__main__':run()

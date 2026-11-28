"""Steelman lossless radial Maxwell + original seven-edge aperture inverse.
Exact algebra and numerical replay of idealized donor radial ODE; no physical loss removal.
"""
from pathlib import Path
import hashlib
import numpy as np
import sympy as S
from solar_steelman_unity import geometry, modal_cycle, recovery


def identities():
    sig,w,eps,mu,ya,r,L=S.symbols('sigma w eps mu ya r L',positive=True,real=True)
    a0=sig+S.I*w*eps
    te=(S.I*w*mu,a0+L/(S.I*w*mu*r*r))
    tm=(S.I*w*mu+L/(a0*r*r),a0)
    assert S.re(te[0])==0 and S.re(te[1])==sig
    assert S.simplify(S.re(tm[0])-L*sig/(r*r*(sig*sig+w*w*eps*eps)))==0
    assert S.re(tm[1])==sig
    e,h=S.symbols('e h',complex=True);a,b=S.symbols('a b',complex=True)
    flux=S.re(S.conjugate(-a*ya*h)*h+S.conjugate(e)*(-b*e/ya))
    assert S.simplify(S.expand_complex(flux+ya*S.re(a)*S.Abs(h)**2+S.re(b)*S.Abs(e)**2/ya))==0
    # Top sheet: source u, total electric E=u+reflected, Hermitian loss s.
    u,E,s=S.symbols('u E s',real=True,nonnegative=True)
    downstream=2*u*E-(1+s)*E*E
    assert S.cancel(u*u/(1+s)-downstream-(1+s)*(E-u/(1+s))**2)==0
    # At zero reflection E=u, downstream=(1-s)u²; perfect capture and
    # maximum useful transfer are distinct if the occupied sheet dissipates.
    assert S.expand(downstream.subs(E,u)-(1-s)*u*u)==0
    return True


def donor():
    raw=(Path(__file__).resolve().parent/'check_smith_filsinger_solar_si_covariance.py').read_bytes()
    prefix=raw.split(b'\nrows=[];maxledger=')[0]
    assert hashlib.sha1(prefix).hexdigest()=='ab105e28cf1abbd145d4fd7a02daecfea8d124cc'
    marker=b'(R+ht/2,R+ht,1e-9)';assert prefix.count(marker)==1
    env={};exec(compile(prefix.replace(marker,b'(R+ht/2,R+ht,0)'), 'ideal_radial_donor', 'exec'),env)
    return env


def reverse(env,f):
    # Only the selected radial conductivity is set to zero. Original donor
    # upper-sheet S and ground shunt are NOT admitted losses in this steelman.
    A,B,C,D,S0,_,_=env['shell'](f);n=len(A);I=np.eye(n);kap=env['kappa']
    M=np.block([[A,B],[C,D]]);J=np.block([[np.zeros((n,n)),I],[I,np.zeros((n,n))]])
    flux_error=np.linalg.norm(M.conj().T@J@M-J,2)
    assert flux_error<1e-8
    E,H=np.split(np.linalg.solve(M,np.vstack((I,-I))),2,axis=0)
    # E,H map incident wave to ground fields for exactly zero reflection.
    assert np.linalg.norm(E.conj().T@H+H.conj().T@E+2*I,2)<1e-8
    # Original 7-edge trace; retain all voltages. Choose strongest three
    # real edge-current directions, a declared coherent receiver subspace.
    T=env['trace'](1e6,1.5,np.pi/2);Uedge,sv,_=np.linalg.svd(T,full_matrices=False)
    K=Uedge[:,:3];assert np.linalg.matrix_rank(K)==3
    current=T.T@K/kap
    Uraw=np.linalg.solve(-H,current)
    Q,s,Vh=np.linalg.svd(Uraw,full_matrices=False)
    incoming=Q/np.sqrt(kap);icoord=Vh.conj().T@np.diag(1/(np.sqrt(kap)*s))
    assert np.linalg.norm(kap*incoming.conj().T@incoming-np.eye(3))<1e-10
    # Actual donor port equations with zero upper shunt: e0=V u-Z j.
    V=np.linalg.solve(A-C,2*I);Z=np.linalg.solve(A-C,D-B)
    Zc=K.T@T@Z@T.T@K/kap;Hp=(Zc+Zc.conj().T)/2
    assert np.linalg.eigvalsh(Hp).min()>0
    assert np.linalg.norm(Zc-Zc.T)<1e-10*np.linalg.norm(Zc)
    load=Zc.conj().T # positive Hermitian part; reciprocal single-frequency match
    voc=K.T@T@V@incoming
    j=current@icoord;e=V@incoming-Z@j;h=-j
    top=A@e+B@h;topH=C@e+D@h
    err=np.linalg.norm(top-incoming)/np.linalg.norm(incoming)
    work=icoord.conj().T@Hp@icoord
    assert err<1e-6 and np.linalg.norm(work-np.eye(3))<1e-6
    assert np.linalg.norm(K.T@T@e-load@icoord)<1e-6*np.linalg.norm(voc)
    # Forward solve independently from matched load and incident source.
    ifwd=np.linalg.solve(Zc+load,voc);efwd=V@incoming-Z@current@ifwd
    bfwd=A@efwd-B@current@ifwd-incoming
    fwderr=np.linalg.norm(bfwd)/np.linalg.norm(incoming)
    assert fwderr<1e-6
    # Same Hopf DFT coherent input in the reverse-selected physical subspace.
    F,_=geometry();F=np.array(F.evalf(),complex);mode=F.conj().T[:,0]
    u=incoming@mode;i=ifwd@mode;ref=kap*np.linalg.norm(bfwd@mode)**2
    y=float(np.vdot(i,Hp@i).real);assert abs(y-1)<1e-6 and ref<1e-10
    # Actual original sheet S retained as a separate loss-bound diagnostic.
    SH=(S0+S0.conj().T)/2
    cap=float(np.linalg.eigvalsh(np.linalg.inv(I+SH)).max());assert 0<cap<1
    # Source outside reverse match subspace remains explicit; no claim
    # that the actual natural source occupies the selected coherent subspace.
    test=I[:,0]/np.sqrt(kap);res=test-Q@(Q.conj().T@test)
    residual=float(kap*np.vdot(res,res).real);assert 0<=residual<=1+1e-10
    # Factor the single-frequency reciprocal termination into real SPD
    # resistance (ideal transformer to unit reference ports) and real
    # symmetric reactance. Power-normalized outgoing coordinates.
    assert np.max(abs(Hp.imag))<1e-10*np.linalg.norm(Hp)
    R=Hp.real;X=load.imag;assert np.allclose(X,X.T,rtol=1e-10,atol=1e-20)
    ev,Vr=np.linalg.eigh(R);root=(Vr*np.sqrt(ev))@Vr.T
    out=root@ifwd;assert np.linalg.norm(out.conj().T@out-np.eye(3))<1e-6
    row=dict(frequency=f,flux_error=float(flux_error),reverse_error=float(err),forward_error=float(fwderr),
                coherent_incident=1.,coherent_reflection=float(ref),coherent_useful=y,
                original_sheet_upper=cap,example_unmatched_source_residual=residual,
                reverse_edge_current_norm=float(np.linalg.norm(K@i)),all_seven_edge_trace=True,
                current_subspace_dimension=3,physical_admission=False,
                min_reverse_current_norm=float(1/(np.sqrt(kap)*s[0])))
    return row,dict(incoming=incoming,ifwd=ifwd,root=root,out=out,reflection=bfwd,kappa=kap)


def run():
    identities();env=donor()
    low,hi=[reverse(env,f) for f in (3.915,7.83)]
    for row,_ in (low,hi):print(row,flush=True)
    # Compose the actual harmonic port maps with the same nonlinear modal
    # state. Full-frequency matched termination is an INTERFACE, not useful
    # heat. Attach the unit-reference converter there; do not count twice.
    F,_=geometry();x,M=modal_cycle(F);assert recovery(x,M)==S.Rational(1,2)
    F=np.array(F.evalf(),complex);c=F.conj().T[:,0];high=hi[1];half=low[1]
    r=high['out'].conj().T@(high['root']@high['ifwd']@c)
    source=F@r;assert np.linalg.norm(source-np.eye(3)[:,0])<1e-6
    h=np.array([complex(x[2]),complex(x[3]),0]);assert abs(np.vdot(h,h).real-1)<1e-12
    y=half['out'].conj().T@(half['root']@half['ifwd']@h)
    useful=abs((y[0]+y[1])/np.sqrt(2))**2;dark=abs((y[0]-y[1])/np.sqrt(2))**2+abs(y[2])**2
    ref_hi=high['kappa']*np.linalg.norm(high['reflection']@c)**2
    ref_lo=half['kappa']*np.linalg.norm(half['reflection']@h)**2
    assert abs(useful-1)<1e-6 and dark<1e-10
    print(dict(harmonic_port_composition=True,source_reopen_error=float(np.linalg.norm(source-np.eye(3)[:,0])),
               incident=1.,intermediate_work_counted_once=True,final_useful=float(useful),dark=float(dark),
               full_reflection=float(ref_hi),half_reflection=float(ref_lo)),flush=True)
    print('PASS radial/aperture reciprocal unity inverse, same normalized coherent modal boundary; no physical source or loss removal admitted')
if __name__=='__main__':run()

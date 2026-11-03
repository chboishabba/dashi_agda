#!/usr/bin/env python3
"""Flux-normalized 1+1D Dirac scattering on the EXISTING EFFECTIVE q=12 geometry.

Reuses check_mmp_global_effective_bvp_replay_20261024.run(with_profile=True).
NOT a 4D Hadamard-renormalized Einstein-Maxwell-Dirac fixed point, nor the
actual single-universe magnetic return-path topology of MMP 2018/2023.

H=-i*sigma_x*d/dz + N(z)*sqrt(n*(n+abs(q)))/r(z)*sigma_z;
z=integral dx/Nphysical, with Killing time normalized at RN infinity.
"""
import json,math
from pathlib import Path
import numpy as np
from scipy.interpolate import PchipInterpolator
from scipy.integrate import cumulative_trapezoid
from check_mmp_global_effective_bvp_replay_20261024 import run

sx=np.array([[0,1],[1,0]],complex)
sy=np.array([[0,-1j],[1j,0]],complex)
identity=np.eye(2,dtype=complex)
U=np.column_stack(([1/2**.5,1/2**.5],[1/2**.5,-1/2**.5]))

def geometry(q=12,L=22.516301125725,cutoff=240,n_inner=481,n_outer=1200):
    g=run(q,L,with_profile=True)
    ode=g['numerical_profile']; rj=g['match_radius']; xj=g['match_x']
    M=g['mass_RN']; Q=g['Q'];scale=g['lapse_scale_to_RN_clock']
    f=lambda r:1-2*M/r+Q*Q/(r*r)
    assert cutoff>rj and f(rj)>0
    x=np.linspace(0,xj,n_inner);vals=ode.sol(x)
    N=np.exp(vals[3])*scale
    z_in=cumulative_trapezoid(1/N,x,initial=0)
    rex=rj+(cutoff-rj)*np.linspace(0,1,n_outer)**1.6
    z_ex=z_in[-1]+cumulative_trapezoid(1/np.array([f(r) for r in rex]),rex,initial=0)
    zh=np.r_[z_in,z_ex[1:]]
    rh=np.r_[vals[0],rex[1:]]
    Nh=np.r_[N,np.sqrt(np.array([f(r) for r in rex[1:]]))]
    z=np.r_[-zh[:0:-1],zh]
    profile=PchipInterpolator(z,np.r_[(Nh/rh)[:0:-1],Nh/rh],extrapolate=False)
    return profile,float(zh[-1]),{'q':q,'L_throat_clock':L,'RN_mass':M,
        'radius_cutoff':cutoff,'RN_lapse_scale':scale,'throat_radius':g['throat_radius'],
        'junction_radius':rj,'optical_interior_asymptotic_clock':2*float(z_in[-1]),
        'optical_full_to_cutoffs':2*float(zh[-1]),'Ktt_jump':g['Ktt_jump']}

def exact_barrier(E,m,L):
    d=E*E-m*m
    t=(math.sin(math.sqrt(d)*L)**2/d if d>0 else
       math.sinh(math.sqrt(-d)*L)**2/(-d) if d<0 else L*L)
    return 1/(1+m*m*t)

def scattering(E,mass,zmin,zmax,h=.2,Az=None,endpoint_mass=None):
    """Exact matrix exponential on every midpoint cell: J=sigma_x conserved."""
    steps=math.ceil((zmax-zmin)/h); dz=(zmax-zmin)/steps;transfer=identity.copy()
    for k in range(steps):
        z=zmin+(k+.5)*dz
        m=float(mass(z));a=float(Az(z)) if Az is not None else 0.
        A=1j*E*sx-m*sy
        v=complex(m*m-E*E)**.5
        P=(identity+A*dz if abs(v)<1e-12 else
            np.cosh(v*dz)*identity+np.sinh(v*dz)/v*A)
        transfer=(np.exp(1j*a*dz)*P)@transfer
    flux_error=float(np.linalg.norm(transfer.conj().T@sx@transfer-sx))
    assert flux_error<3e-8,(E,flux_error)
    if endpoint_mass is None:
        B=U.conj().T@transfer@U
    else:
        # Adiabatic finite-radius lead: positive-energy locally massive
        # propagating spinors, with current normalized to +/-1.
        assert E>abs(endpoint_mass), "No propagating lead for this energy/mass"
        k=(E*E-endpoint_mass*endpoint_mass)**.5
        a=((E+endpoint_mass)/(2*k))**.5
        b=((E-endpoint_mass)/(2*k))**.5
        lead=np.column_stack(((a,b),(a,-b)))
        assert np.linalg.norm(lead.conj().T@sx@lead-np.diag([1.,-1.]))<1e-12
        B=np.linalg.inv(lead)@transfer@lead
    reflection=-B[1,0]/B[1,1]
    transmission=np.linalg.det(B)/B[1,1]
    R=abs(reflection)**2;T=abs(transmission)**2
    assert abs(R+T-1)<3e-8,(E,R,T)
    return {'r':reflection,'t':transmission,'R':float(R),'T':float(T),
        'flux_error':flux_error,'probability_error':float(abs(R+T-1))}

def selected_channel(t1,t2):
    """Two ASSUMED coherent angular modes, not a physical encoded pair."""
    K=np.diag([t1,t2]);D=identity-K.conj().T@K
    ev,Q=np.linalg.eigh(D)
    assert ev.min()>-1e-8
    root=Q@np.diag(np.sqrt(np.maximum(ev,0)))@Q.conj().T
    ops=[np.vstack((K,np.zeros((1,2),complex)))]
    for j in range(2):
        A=np.zeros((3,2),complex);A[2,:]=root[j,:];ops.append(A)
    TP=np.linalg.norm(sum((a.conj().T@a for a in ops),np.zeros((2,2),complex))-identity)
    s=np.linalg.svd(K,compute_uv=False)
    eta=float(np.sum(s*s)/2)
    Fe=float(np.sum(s)**2/4)
    assert TP<1e-10 and eta>0
    return {'mean_success':eta,'weighted_Fe':Fe,
        'conditional_Fe_ideal_local_correction':Fe/eta,
        'input_success_probability_span':float(abs(s[0]**2-s[1]**2)),
        'Kraus_trace_error':float(TP)}

def main():
    for E,m,length in ((.5,.8,3),(1.3,.8,3),(1.,1.,2)):
        out=scattering(E,lambda z:m,-length/2,length/2,h=.05)
        assert abs(out['T']-exact_barrier(E,m,length))<1e-6
    for E in (.2,.6,1.2):
        out=scattering(E,lambda z:0.,-15,15)
        assert abs(out['T']-1)<1e-8 and out['R']<1e-12
    phi=.4
    base=scattering(.5,lambda z:.25*math.exp(-z*z/9),-9,9,h=.045)
    gauged=scattering(.5,lambda z:.25*math.exp(-z*z/9),-9,9,h=.045,Az=lambda z:phi/18)
    assert abs(base['T']-gauged['T'])<1e-10
    assert abs(gauged['t']/base['t']-np.exp(1j*phi))<1e-9
    cases=[]
    for cutoff in (60.,120.,240.):
        profile,Z,geo=geometry(cutoff=cutoff)
        entry={'geometry':geo,'energies':{}}
        for energy in (.2,.55,1.):
            values={}
            for n in (0,1,2):
                fac=math.sqrt(n*(n+12))
                result=scattering(energy,lambda z,fac=fac:fac*profile(z),-Z,Z,h=.2,endpoint_mass=fac*float(profile(Z)))
                values[str(n)]={k:v for k,v in result.items() if k not in ('r','t')}
                if n==1:t1=result['t']
                if n==2:t2=result['t']
            assert abs(values['0']['T']-1)<1e-7
            values['two_mode_selected_channel']=selected_channel(t1,t2)
            entry['energies'][str(energy)]=values
        cases.append(entry)
    assert 1400<cases[0]['geometry']['optical_interior_asymptotic_clock']<1600
    for E in (.2,.55,1.):
        vals=cases[-1]['energies'][str(E)]
        print('E=',E,'LLL T=',round(vals['0']['T'],8),'n1 T=',round(vals['1']['T'],7),
            'n2 T=',round(vals['2']['T'],7),'channel mean eta=',round(vals['two_mode_selected_channel']['mean_success'],7),
            'conditional Fe=',round(vals['two_mode_selected_channel']['conditional_Fe_ideal_local_correction'],7))
    print('PASS: exact barrier, massless limit, J-unitarity, U1 gauge phase, local-mass flux leads, effective RN geometry and CPTP loss')
    print('OPEN: cutoff->infinity, global 4D Dirac state, true closed return, physical encoding, causal wavepacket')
    result={'cases':cases,'authority':'bounded scattering on piecewise effective GR source, not full MMP 4D'}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result,indent=2))
if __name__=='__main__':main()

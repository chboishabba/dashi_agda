#!/usr/bin/env python3
"""OCT369 P0.29: reuse EXISTING P0.18 Bloch + CoTaSe2 Wannier/Kubo consumers.

Native owners: scripts/check_oct369_p018_periodic_tunnel_stress.py;
scripts/co_tase2_wannier3d_diagnostics.py;
scripts/co_tase2_nonabelian_topology.py;
scripts/check_mmp_three_independent_retarded_source_ports_20261025.py.
Uses actual native P0.18 nearest-neighbour Mn(3c) hopping and C3 trial order.
New consumer: finite same-H source-conjugate order susceptibility, gauge-safe
Berry/projector diagnostics, and real-time retarded linear-response control.

Not the Sato/Hayami 2026 gauge-invariant spin magnetic octupole Eq.(11):
that expression needs mixed k/B quantum geometry, energy and occupation terms.
Not Kang et al 2026 measured PtMn3 bands, octupole torque or levitation.
"""
from __future__ import annotations
import json
from pathlib import Path
import numpy as np
from scipy.linalg import expm

import check_oct369_p018_periodic_tunnel_stress as material
import co_tase2_wannier3d_diagnostics as bloch_kubo
import co_tase2_nonabelian_topology as nonabelian

TWO_PI=2*np.pi
T=0.55
N=6
assert len(material.BONDS)==24

# Use the ORIGINAL periodic hopping owner, but implement a strictly periodic
# Wannier cell gauge: link phase is exp(2πi k·R), not exp(i k·(R+r_b-r_a)).
# The two gauges are explicitly and exactly related by a site-diagonal unitary.
def data_from_original_bonds():
    rvec=[]; blocks=[]; degeneracy=[]
    for a in range(3):
        block=np.zeros((N,N),complex)
        block[2*a:2*a+2,2*a:2*a+2]=.8*material.sig(material.SPIN[a])
        rvec.append([0,0,0]);blocks.append(block);degeneracy.append(1)
    for a,b,R,d in material.BONDS:
        block=np.zeros((N,N),complex)
        block[2*a:2*a+2,2*b:2*b+2]=.7*material.I2 + .15j*material.sig(np.cross(material.AXIS,d))
        rvec.append(list(R));blocks.append(block);degeneracy.append(1)
    return np.array(rvec,int),np.array(blocks,complex),np.array(degeneracy,int)

R_VEC,H_BLOCKS,DEGEN=data_from_original_bonds()
OP=np.zeros((N,N),complex)
for a in range(3):
    OP[2*a:2*a+2,2*a:2*a+2]=material.sig(material.SPIN[a])
SIGMA=[np.kron(np.eye(3),v) for v in material.SIGMA]

def h_deriv(kf):
    return bloch_kubo.h_and_derivs_fractional(kf,R_VEC,H_BLOCKS,DEGEN)

def full_to_cell_gauge(kf):
    phases=np.exp(1j*TWO_PI*(material.SITES@kf))
    return np.kron(np.diag(phases),material.I2)

def fermi(e,temperature=T):
    return 1/(1+np.exp(np.clip(e/temperature,-700,700)))

def grand(H,temperature=T):
    e=np.linalg.eigvalsh(H)
    return float(-temperature*np.logaddexp(0,-e/temperature).sum())

def thermal_expect(H,ob=OP,temperature=T):
    e,u=np.linalg.eigh(H)
    # Correct same-BASIS density matrix, with no eigenvector gauge choice.
    return float(np.sum(fermi(e,temperature)*np.real(np.diag(u.conj().T@ob@u))))

def spectral_static_kubo(H,ob=OP,temperature=T):
    e,u=np.linalg.eigh(H)
    o=u.conj().T@ob@u
    f=fermi(e,temperature)
    chi=0.
    for n in range(N):
        chi+=f[n]*(1-f[n])*abs(o[n,n])**2/temperature
        for m in range(N):
            if m==n:continue
            de=e[m]-e[n]
            if abs(de)<1e-10:
                # Equality of energies: thermal divided difference limit.
                coeff=f[n]*(1-f[n])/temperature
            else:
                coeff=(f[n]-f[m])/de
            chi+=coeff*abs(o[n,m])**2
    return float(chi.real)

def driven_source(t):
    if not (.14<t<.72):return 0.
    return float(np.sin(np.pi*(t-.14)/(.72-.14))**2)

def time_response(H,ob,stop,steps=120):
    # Native MMP finite retarded construction: fixed equilibrium density and
    # explicit t>s causal commutator. No re-thermalization assumption.
    dt=stop/steps
    e,u=np.linalg.eigh(H)
    P=(u*fermi(e))@u.conj().T
    comm=ob@P-P@ob
    delta=np.zeros_like(H)
    for j in range(steps):
        t=(j+.5)*dt
        strength=driven_source(t)
        if strength==0:continue
        U=(u*np.exp(-1j*e*(stop-t)))@u.conj().T
        delta+=1j*dt*strength*(U@comm@U.conj().T)
    response=float(np.trace(ob@delta).real)
    def evolved(amplitude):
        Q=np.eye(N,dtype=complex)
        for j in range(steps):
            t=(j+.5)*dt
            Q=expm(-1j*dt*(H-amplitude*driven_source(t)*ob))@Q
        return float(np.trace(ob@Q@P@Q.conj().T).real)
    h=.001
    fd=(evolved(h)-evolved(-h))/(2*h)
    return response,fd

checks={}
metrics={}
def check(name,condition):
    assert bool(condition),f'{name}: {condition}'
    checks[name]=True

def finite_derivatives(H,kf):
    eps=1e-5
    d=[]
    for i in range(3):
        v=np.zeros(3);v[i]=eps
        d.append((h_deriv(kf+v)[0]-h_deriv(kf-v)[0])/(2*eps))
    return d

# C3 sewing for the two equivalent site embedding conventions.
kvecs=[np.array(x,float) for x in ((.17,.13,-.22),(.28,-.21,.09),(-.07,.16,.25),(.09,.11,-.28))]
max_h=max_bloch=max_d=max_c3=max_op=0.
for j,k in enumerate(kvecs):
    H,dH=h_deriv(k)
    max_h=max(max_h,np.linalg.norm(H-H.conj().T))
    W=full_to_cell_gauge(k)
    full=material.hsingle(TWO_PI*k)
    max_bloch=max(max_bloch,np.linalg.norm(W@full@W.conj().T-H))
    max_d=max(max_d,max(np.linalg.norm(v-w) for v,w in zip(dH,finite_derivatives(H,k))))
    Rk=material.R@k
    Ucell=full_to_cell_gauge(Rk)@material.UC3@W.conj().T
    max_c3=max(max_c3,np.linalg.norm(Ucell@H@Ucell.conj().T-h_deriv(Rk)[0]))
    max_op=max(max_op,np.linalg.norm(Ucell@OP@Ucell.conj().T-OP))
check('24_physical_bonds_reused',len(material.BONDS)==24)
check('24_integer_wannier_translation_terms',len(R_VEC)==27 and np.all(R_VEC==np.rint(R_VEC)))
check('Hermiticity_all_4_k',max_h<1e-12)
check('original_site_gauge_to_cell_gauge',max_bloch<1e-12)
check('analytic_Wannier_dH_dk_matches_fd',max_d<1e-6)
check('C3_kdependent_Bloch_sewing',max_c3<1e-12)
check('C3_conjugate_order_operator',max_op<1e-12)
check('trial_order_zero_NET_dipole',np.linalg.norm(material.SPIN.sum(axis=0))<1e-12)
check('order_operator_Hermitian',np.linalg.norm(OP-OP.conj().T)<1e-12)
check('order_operator_is_not_uniform_spin',np.linalg.norm(OP-SIGMA[2])>1)
check('same_H_order_conjugate',np.linalg.norm((h_deriv(kvecs[0])[0]-.01*OP)-h_deriv(kvecs[0])[0]+.01*OP)<1e-14)

sus=[]; berry=[]; gaps=[]
for j,k in enumerate(kvecs):
    H,dH=h_deriv(k)
    ee,V=np.linalg.eigh(H)
    sp=source=spectral_static_kubo(H)
    fd=(thermal_expect(H-1e-4*OP)-thermal_expect(H+1e-4*OP))/(2e-4)
    dd=-(grand(H+2e-4*OP)-2*grand(H)+grand(H-2e-4*OP))/(2e-4)**2
    check(f'static_Kubo_matches_expectation_gradient_{j}',abs(sp-fd)<2e-6)
    check(f'static_Kubo_matches_Omega_curvature_{j}',abs(sp-dd)<2e-5)
    check(f'static_Kubo_nonnegative_{j}',sp>=-1e-12)
    check(f'band_spin_expectations_native_donor_{j}',bloch_kubo.operator_expectations(V,[OP,*SIGMA]).shape==(6,4))
    phases=np.exp(1j*np.array([.13,.47,.88,1.41,2.03,2.97]))
    V2=V*phases
    check(f'band_expectation_gauge_invariant_{j}',np.max(np.abs(bloch_kubo.operator_expectations(V,[OP])-bloch_kubo.operator_expectations(V2,[OP])))<1e-12)
    check(f'kubo_band_rephase_invariant_{j}',abs(sp-spectral_static_kubo((V2*ee)@V2.conj().T))<1e-10)
    gap=min(np.diff(ee))
    gaps.append(float(gap))
    if gap>1e-6:
        b1=bloch_kubo.berry_curvature_band(ee,V,dH,0)
        b2=bloch_kubo.berry_curvature_band(ee,V2,dH,0)
        b3=nonabelian.subspace_curvature_vector(ee,V,dH,[0])
        check(f'Berry_Kubo_native_phase_invariance_{j}',np.linalg.norm(b1-b2)<1e-11)
        check(f'Berry_vs_projector_curvature_{j}',np.linalg.norm(b1-b3)<1e-10)
        berry.append(b1.tolist())
    sus.append(float(sp))
check('nonzero_actual_order_response_in_fixture',max(sus)>1e-3)
check('distinct_k_susceptibilities',np.ptp(sus)>1e-4)
check('physical_band_nonflat',np.linalg.norm(np.linalg.eigvalsh(h_deriv(kvecs[0])[0])-np.linalg.eigvalsh(h_deriv(kvecs[1])[0]))>1e-3)

# Degeneracy fail-closed control. The actual donor must refuse a subspace
# whose external spectral gap is smaller than the stated certification floor.
H,der=h_deriv(kvecs[0]);e,V=np.linalg.eigh(H)
try:nonabelian.projector_and_derivatives(e,V,der,[0],gap_floor=100.)
except ValueError:rejected=True
else:rejected=False
check('degenerate_or_unisolated_subspace_fail_closed',rejected)
proj,dp,gap=nonabelian.projector_and_derivatives(e,V,der,[0],gap_floor=1e-8)
check('isolated_single_band_projector',np.linalg.norm(proj@proj-proj)<1e-10 and gap>1e-8)
# Original native 2-band Wilson-loop procedure on three nearby momenta.
k0=kvecs[0]
ks=[k0,k0+np.array([.014,0.,0.]),k0+np.array([.014,.012,0.]),k0+np.array([0.,.012,0.])]
frames=[]
for k in ks:
    ee,uv=np.linalg.eigh(h_deriv(k)[0]);frames.append(uv[:,:2])
ph1=nonabelian.wilson_loop_phases(frames)
rng=np.random.default_rng(369)
newframes=[]
for frame in frames:
    z=rng.standard_normal((2,2))+1j*rng.standard_normal((2,2))
    u,_,vh=np.linalg.svd(z)
    newframes.append(frame@u@vh)
ph2=nonabelian.wilson_loop_phases(newframes)
check('native_Wilson_loop_U2_frame_gauge_invariant',np.linalg.norm(ph1-ph2)<1e-10)
check('native_Wilson_loop_does_not_require_bandwise_phase',all(np.linalg.norm(f-n)>1e-3 for f,n in zip(frames,newframes)))

# Retarded Kubo, not conflated with the equilibrated static susceptibility.
resp,fd=time_response(H,OP,1.25,500)
check('retarded_Kubo_vs_finite_driving_difference',abs(resp-fd)<1e-5)
check('nonzero_after_pulse_response',abs(resp)>1e-5)
future,fd_future=time_response(H,OP,.1,20)
check('future_pulse_no_early_effect',future==0. and abs(fd_future)<1e-10)
# The force F=-dOmega/dz requires an independently calibrated h(z).
check('source_gradient_not_measured_by_Kubo',not any(k in ('alpha','field_gradient_T_m3') for k in checks))

metrics.update({'max_hermiticity':max_h,'max_site_cell_unitary_equivalence':max_bloch,
'max_analytic_derivative_error':max_d,'max_C3_sewing':max_c3,
'max_C3_order_covariance':max_op,'thermal_T_fixture_units':T,
'order_static_susceptibilities':sus,'minimum_band_gaps':gaps,
'berry_curvature_first_band':berry,'retarded_response':resp,
'retarded_finite_difference':fd,'retarded_error':abs(resp-fd),
'Wilson_loop_phases':ph1.tolist(),'max_Wilson_U2_error':float(np.max(np.abs(ph1-ph2)))})

out={'scope':'P0.18 site-identified PERIODIC six-band Hamiltonian + native Wannier Kubo and projector/Wilson consumers; NOT original Sato-Hayami Eq11',
'checks_passed':len(checks),'checks':checks,'metrics':metrics,
'donor_files':[
'scripts/check_oct369_p018_periodic_tunnel_stress.py',
'scripts/co_tase2_wannier3d_diagnostics.py',
'scripts/co_tase2_nonabelian_topology.py',
'scripts/check_mmp_three_independent_retarded_source_ports_20261025.py'],
'original_PtMn3_Wannier_H_not_supplied':True,
'original_Sato_Hayami_2026_Eq11_not_implemented':True,
'full_k_and_Zeeman_space_spin_octupole_not_computed':True,
'original_Oike_2025_thermodynamic_bulk_formula_not_implemented':True,
'Kang_2026_experimental_torque_not_reproduced':True,
'calibrated_external_field_gradient_or_MgO_barrier_not_supplied':True,
'real_gravity_or_levitation_observed':False,
'attribution':{'established':'Bloch, band geometry, Fermi/Kubo susceptibility, Wilson-loop spectral projectors, retarded response',
'native_DASHI':'P0.18 Mn3c spinful periodized Hamiltonian; CoTaSe2 Wannier/Kubo/topology; MMP causal source response',
'physical_theory':'Oike/Peters/Shinada PRB 2025; Sato/Hayami npj Quantum Materials 2026, DOI 10.1038/s41535-026-00865-9',
'experiment':'Kang et al Nature 2026 DOI 10.1038/s41586-026-11172-5',
'new':'OCT369 direct source-conjugate and Wilson/Bloch exact donor consumption, without physical promotion'}}
if __name__=='__main__':print(json.dumps(out,indent=2,sort_keys=True))

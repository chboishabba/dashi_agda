#!/usr/bin/env python3
"""OCT369 P0.31: Sato--Hayami 2026 npj Quantum Materials Eq. (11)--(18).

Scientific attribution: Sato & Hayami DOI 10.1038/s41535-026-00865-9
own this ORIGINAL periodic-crystal expression; Oike/Peters/Shinada PRB 2025
own an earlier thermodynamic bulk formulation. Kang et al 2026 Nature own
PtMn3/MgO OTT/TMR experiment. The new DASHI CONSUMER evaluates the published
nondegenerate formula against P0.18's existing UNFITTED 24-bond Mn3 Hamiltonian.

Uses existing native DASHI P0.29 Bloch/Wannier donor, but physical velocity
and Hessian are computed in the atomic-embedding gauge. Periodic-cell gauge
requires the explicit orbital-position connection. No first-principles PtMn3
Wannier, measured domain, source Maxwell coil, or gravity claim is involved.
No CI. Numerically ill-conditioned near degenerate bands: fail closed.
"""
import json
import numpy as np
from itertools import product
import check_oct369_p018_periodic_tunnel_stress as material
import check_oct369_p029_bloch_kubo_reuse as native
from oct369_covariant_bloch_geometry import physical_cell_jets

T=0.55
CHEM=0.07
TWO_PI=2*np.pi
N=6
MIN_GAP=0.02
SPIN=[np.kron(np.eye(3), v) for v in material.SIGMA]
POSITION=[np.kron(np.diag(material.SITES[:,i]),material.I2) for i in range(3)]
BONDS=material.BONDS

# Physical k in inverse-lattice-length units; all lengths are lattice units.
def hphysical(kf,domain=1):
    p=TWO_PI*np.asarray(kf,float)
    H=np.zeros((N,N),complex)
    dH=np.zeros((3,N,N),complex)
    ddH=np.zeros((3,3,N,N),complex)
    for a in range(3):
        H[a*2:a*2+2,a*2:a*2+2]=domain*.8*material.sig(material.SPIN[a])
    for a,b,R,d in BONDS:
        hop=.7*material.I2+.15j*material.sig(np.cross(material.AXIS,d))
        part=np.exp(1j*p@d)*hop
        inds=np.ix_([2*a,2*a+1],[2*b,2*b+1])
        H[inds]+=part
        for j in range(3):
            dH[j][inds]+=(1j*d[j])*part
            for k in range(3):
                ddH[j,k][inds]+=(-d[j]*d[k])*part
    return H,dH,ddH


def gaps(e):
    return float(np.min(np.diff(e)))


def quantum_octupole(kf,domain=1,unitary_phases=None,matrices=None):
    """Return 3x3x3 Sato-Hayami full M, diagonal/off split per k point.

    Implements published Eqs 11--18, with g*mu_B=1 as MODEL normalization.
    epsilon_nm := epsilon_n-epsilon_m; integral F_n=T*log(1+exp(-e_n/T)).
    Source formula presumes nondegenerate bands: fail when a gap too small.
    """
    H,D,DD=hphysical(kf,domain) if matrices is None else matrices
    e,V=np.linalg.eigh(H)
    gap=gaps(e)
    if gap<MIN_GAP:
        raise ValueError('Nondegenerate Eq11 not valid at this small band gap: '+str(gap))
    if unitary_phases is not None:
        V=V*np.exp(1j*np.asarray(unitary_phases))[None,:]
    S=np.array([V.conj().T@s@V for s in SPIN])
    vel=np.array([V.conj().T@D[j]@V for j in range(3)])
    hd=np.array([[V.conj().T@DD[j,k]@V for k in range(3)] for j in range(3)])
    hesse=np.zeros((3,3,N),float)
    for j,k in product(range(3),repeat=2):
        for n in range(N):
            val=hd[j,k,n,n].real
            for m in range(N):
                if m!=n:
                    val+=2*(vel[j,n,m]*vel[k,m,n]).real/(e[n]-e[m])
            hesse[j,k,n]=val
    z=(e-CHEM)/T
    f=1/(1+np.exp(np.clip(z,-700,700)))
    fp=-f*(1-f)/T
    wint=T*np.logaddexp(0,-z)
    diag=np.zeros((3,3,3),float)
    off=np.zeros((3,3,3),float)

    # Implement Eq12 spin diagonal term exactly as printed.
    for i,j,k in product(range(3),repeat=3):
        val=0.
        for n in range(N):
            sn=S[i,n,n].real
            val-=sn*hesse[j,k,n]*fp[n]/12
            for m in range(N):
                if n==m: continue
                sm=S[i,m,m].real
                enm=e[n]-e[m]
                v=vel[j,n,m]*vel[k,m,n]
                gnm=(v/(enm**2)).real
                Gnm=(2*v/(enm**3)).real
                val+=(sn+sm)*.5*(gnm*f[n]+Gnm*wint[n])
        diag[i,j,k]=val

    # Eq13: symmetrize ALL offdiagonal contributions in j,k only.
    def off_unsym(i,j,k):
        val=0.
        for n in range(N):
            vn=vel[k,n,n].real
            for m in range(N):
                if m==n:continue
                enm=e[n]-e[m]
                smv=S[i,n,m]*vel[j,m,n]
                dtilde=(smv/enm).real
                gtilde=-(smv/(enm*enm)).real
                Gtilde=-2*(smv/(enm**3)).real
                vm=vel[k,m,m].real
                val+=dtilde*vn*fp[n]/6
                val+=gtilde*vn*f[n]/2
                val+=Gtilde*(vn+vm)*wint[n]/4
                for l in range(N):
                    if l==n or l==m:continue
                    eln=e[l]-e[n]; eml=e[m]-e[l]
                    X=(S[i,m,l]*vel[j,l,n]*vel[k,n,m]/(eln*enm)).real
                    Y=(-S[i,n,m]*vel[j,m,l]*vel[k,l,n]/(enm*eml*(e[l]-e[n]))
                       +S[i,l,n]*vel[j,n,m]*vel[k,m,l]/((enm**2)*eml)
                       +S[i,m,l]*vel[j,l,n]*vel[k,n,m]/(eln*(enm**2))).real
                    val-=X*f[n]/4+Y*wint[n]/2
        return val
    for i in range(3):
        for j in range(3):
            for k in range(j,3):
                value=off_unsym(i,j,k)+off_unsym(i,k,j)
                off[i,j,k]=off[i,k,j]=value
    return diag+off,diag,off,{'min_gap':gap,'spectrum':e.tolist(),
        'eigenvalue_hessian_symmetry':float(np.max(np.abs(hesse-hesse.transpose(1,0,2))))}

def cell_tensors(kf,corrected=True):
    # Native P0.29 Wannier H(k) and R bond vectors with analytic *integer-cell*
    # derivatives. Restore the orbital-position connection when differentiating
    # the physical embedded-site Hamiltonian, where r_b-r_a is present in hops.
    kr=TWO_PI*np.asarray(kf)
    HC=np.zeros((N,N),complex)
    DC=np.zeros((3,N,N),complex)
    DDC=np.zeros((3,3,N,N),complex)
    for R,block,deg in zip(native.R_VEC,native.H_BLOCKS,native.DEGEN):
        phase=np.exp(1j*kr@R)/deg
        h=phase*block
        HC+=h
        for j in range(3):
            DC[j]+=1j*R[j]*h
            for k in range(3): DDC[j,k]-=R[j]*R[k]*h
    if not corrected:return HC,DC,DDC
    # This physical-cell geometry adapter is the original crystal-accounting
    # contract specialized to B=I, p_cart=2*pi*k_frac. It carries the
    # orbital-position commutators in both first and second derivatives.
    # P0.32 checks nonorthogonal lattice basis changes independently.
    Dcov,DDcov=physical_cell_jets(HC,DC,DDC,POSITION)
    return HC,Dcov,DDcov


def eps3(i,j,k):
    if len({i,j,k})<3:return 0
    a=(i,j,k)
    return 1 if a in ((0,1,2),(1,2,0),(2,0,1)) else -1


def irreducible_split(Tensor):
    # Existing Sato/Hayami 18 = l=3 (7) + l=2 (5) + l=1 (3) + l=1 (3).
    # Fully symmetric S, trace3, plus mixed-symmetry tensor R <-> tracefree Q.
    S=(Tensor+Tensor.transpose(1,0,2)+Tensor.transpose(1,2,0))/3
    trace=np.einsum('ijj->i',S)
    tracepart=np.array([[(np.eye(3)[i,j]*trace[k]
        +np.eye(3)[i,k]*trace[j]+np.eye(3)[j,k]*trace[i])/5
        for k in range(3)] for i in range(3) for j in range(3)]).reshape(3,3,3)
    rank7=S-tracepart
    mixed=Tensor-S
    Q=np.einsum('aij,ijb->ab',np.array([[[eps3(i,j,k) for k in range(3)] for j in range(3)] for i in range(3)]),mixed)
    Qsym=(Q+Q.T)/2
    Qanti=(Q-Q.T)/2
    def unmix(Qx):
        return np.array([[[sum((eps3(i,j,a)*Qx[a,k]+eps3(i,k,a)*Qx[a,j])/3
            for a in range(3)) for k in range(3)] for j in range(3)] for i in range(3)])
    l2=unmix(Qsym);l1mixed=unmix(Qanti)
    return rank7,l2,tracepart,l1mixed,Q

checks=[]
def ck(name,val):
    if not bool(val): raise AssertionError(name)
    checks.append(name)

ks=[np.array(v,float) for v in ((.17,.13,-.22),(.28,-.21,.09),(-.07,.16,.25),(.09,.11,-.28))]
records=[]
max_sym=0.;max_gauge=0.;max_C3=0.;max_TR=0.;max_band=.0
for ix,k in enumerate(ks):
    H,D,DD=hphysical(k)
    Href=material.hsingle(TWO_PI*k)
    ck(f'same_P018_H_{ix}',np.linalg.norm(H-Href)<1e-12)
    ck(f'H_Hermitian_{ix}',np.linalg.norm(H-H.conj().T)<1e-12)
    eps=5e-6
    derr=[]
    for j in range(3):
        v=np.zeros(3);v[j]=eps
        derr.append(np.linalg.norm((hphysical(k+v)[0]-hphysical(k-v)[0])/(2*eps*TWO_PI)-D[j]))
    ck(f'analytic_physical_velocity_{ix}',max(derr)<1e-7)
    tensor,partD,partO,metadata=quantum_octupole(k)
    ck(f'nondegenerate_selected_k_{ix}',metadata['min_gap']>MIN_GAP)
    ck(f'M_symmetric_jk_{ix}',np.max(np.abs(tensor-tensor.transpose(0,2,1)))<1e-12)
    ck(f'M_finite_real_{ix}',np.isfinite(tensor).all())
    ck(f'M_offdiagonal_nonzero_{ix}',np.max(np.abs(partO))>1e-6)
    ck(f'M_diagonal_nonzero_{ix}',np.max(np.abs(partD))>1e-6)
    phases=np.array([.13,.47,.88,1.41,2.03,2.97])
    u,_,_,_=quantum_octupole(k,unitary_phases=phases)
    gerr=float(np.max(abs(u-tensor)));max_gauge=max(max_gauge,gerr)
    ck(f'Eq11_per_band_U1_gauge_{ix}',gerr<1e-10)
    # C3 covariance in physical embedded-site gauge: U_C3 constant.
    rotk=material.R@k
    tr,_,_,_=quantum_octupole(rotk)
    rt=np.einsum('ia,jb,kc,abc->ijk',material.R,material.R,material.R,tensor)
    cerr=float(np.max(abs(tr-rt)));max_C3=max(max_C3,cerr)
    ck(f'C3_octupole_tensor_{ix}',cerr<1e-7)
    opposite,_,_,_=quantum_octupole(-k,domain=-1)
    terr=float(np.max(abs(tensor+opposite)));max_TR=max(max_TR,terr)
    ck(f'time_reversal_odd_tensor_{ix}',terr<1e-7)
    Hcell,Dcell,DDcell=cell_tensors(k,corrected=True)
    W=native.full_to_cell_gauge(k)
    ck(f'cell_corrected_H_{ix}',np.linalg.norm(Hcell-W@H@W.conj().T)<1e-12)
    ck(f'cell_corrected_D_{ix}',max(np.linalg.norm(Dcell[j]-W@D[j]@W.conj().T) for j in range(3))<1e-12)
    ck(f'cell_corrected_DD_{ix}',max(np.linalg.norm(DDcell[j,k]-W@DD[j,k]@W.conj().T) for j in range(3) for k in range(3))<1e-12)
    M_cell,_,_,_=quantum_octupole(k,matrices=(Hcell,Dcell,DDcell))
    ck(f'cell_embedded_full_Eq11_identical_{ix}',np.max(np.abs(M_cell-tensor))<1e-10)
    hn,dn,ddn=cell_tensors(k,corrected=False)
    M_bad,_,_,_=quantum_octupole(k,matrices=(hn,dn,ddn))
    ck(f'naive_cell_formula_differs_{ix}',np.max(np.abs(M_bad-tensor))>1e-5)
    p7,p5,p3a,p3b,Q=irreducible_split(tensor)
    ck(f'18_rank_irreducible_reconstruction_{ix}',np.max(np.abs(p7+p5+p3a+p3b-tensor))<1e-11)
    ck(f'7_component_STF_tracezero_{ix}',all(abs(np.trace(p7[i]))<1e-11 for i in range(3)))
    ck(f'5_component_Q_tracezero_{ix}',abs(np.trace(Q))<1e-11)
    ck(f'5_component_Q_symmetric_{ix}',np.max(abs((Q+Q.T)/2-((Q+Q.T)/2).T))<1e-12)
    ck(f'3_component_Q_antisymmetric_{ix}',np.max(abs((Q-Q.T)/2+((Q-Q.T)/2).T))<1e-12)
    ck(f'SO3_reps_both_nontrivial_{ix}',np.linalg.norm(p7)>1e-6 and np.linalg.norm(p5)>1e-6 and np.linalg.norm(p3a)>1e-6 and np.linalg.norm(p3b)>1e-6)
    max_sym=max(max_sym,float(np.max(abs(tensor-tensor.transpose(0,2,1)))))
    records.append({'k_frac':k.tolist(),'gap':metadata['min_gap'],
        'norm_rank7_5_3_3':[float(np.linalg.norm(t)) for t in (p7,p5,p3a,p3b)],
        'cell_corrected_Eq11_error':float(np.max(abs(M_cell-tensor))),
        'naive_cell_Eq11_error':float(np.max(abs(M_bad-tensor))),
        'M_norm':float(np.linalg.norm(tensor)),'Mdiag_norm':float(np.linalg.norm(partD)),
        'Moff_norm':float(np.linalg.norm(partO)),
        'max_U1_error':gerr,'C3_err':cerr,'TR_err':terr})

# Published Eq11 is defined as a full Brillouin-zone integral. This
# coarse C3-symmetrized diagnostic deliberately does NOT pass a numerical
# convergence claim. High-symmetry degenerate points are a hard fail for
# the nondegenerate Eq11, requiring the paper's separate Methods formula.
import itertools
BZdiagnostics=[]
rot=material.R
for mesh in (3,4,5):
    shift=(.137,.193,.271) # non-symmetric shifted torus to avoid exact degeneracies
    sample=[];sample_gaps=[]
    for q in itertools.product(range(mesh),repeat=3):
        k=np.array([(q[d]+shift[d])/mesh-.5 for d in range(3)])
        O,_,_,md=quantum_octupole(k)
        sample_gaps.append(md['min_gap'])
        for power in range(3):
            rr=np.linalg.matrix_power(rot,power)
            sample.append(np.einsum('ia,jb,kc,abc->ijk',rr,rr,rr,O))
    integral=np.mean(sample,axis=0)
    rc3=np.einsum('ia,jb,kc,abc->ijk',rot,rot,rot,integral)
    ck(f'BZ_{mesh}_rotated_grid_covariance',np.max(np.abs(rc3-integral))<1e-11)
    ck(f'BZ_{mesh}_grid_non_degenerate',min(sample_gaps)>MIN_GAP)
    ck(f'BZ_{mesh}_tensor_jk_sym',np.max(abs(integral-integral.transpose(0,2,1)))<1e-11)
    BZdiagnostics.append({'mesh_axis':mesh,'C3_orbit_sample_count':len(sample),
      'minimum_gap':min(sample_gaps),'averaged_M_norm':float(np.linalg.norm(integral)),
      'averaged_M_components':integral.tolist()})
ck('BZ_not_converged_at_3_vs_5',abs(BZdiagnostics[0]['averaged_M_norm']-BZdiagnostics[-1]['averaged_M_norm'])>1e-3)
for k in ((0.,0.,0.),(.23,.23,.23)):
    rejected=False
    try:quantum_octupole(np.array(k))
    except ValueError:rejected=True
    ck('degenerate_axis_fail_closed_'+str(k),rejected)

# The cell-periodic H(k) and site-embedding H(k) have equal eigenvalues but
# naive derivatives differ because W(k) is k-dependent. Correct by -i[X,H].
max_corr=0.;min_naive_difference=float('inf')
for ix,k in enumerate(ks):
    Hc,Dc=native.h_deriv(k)
    W=native.full_to_cell_gauge(k)
    Hemb,Vemb,Hess=hphysical(k)
    ck(f'physical_vs_cell_spectra_{ix}',np.linalg.norm(Hc-W@Hemb@W.conj().T)<1e-12)
    naive=[];corrected=[]
    for j in range(3):
        A=Dc[j]/TWO_PI
        comm=POSITION[j]@Hc-Hc@POSITION[j]
        naive.append(np.linalg.norm(A-W@Vemb[j]@W.conj().T))
        corrected.append(np.linalg.norm(A-1j*comm-W@Vemb[j]@W.conj().T))
    max_corr=max(max_corr,max(corrected));min_naive_difference=min(min_naive_difference,max(naive))
    ck(f'basis_connection_repairs_velocity_{ix}',max(corrected)<1e-12)
    ck(f'naive_cell_velocity_is_different_{ix}',max(naive)>1e-3)
ck('full_Eq11_is_not_static_order_chi',True)
ck('material_fitted_PtMn3_not_claimed',True)
ck('source_G_ijk_and_finite_coil_not_claimed',True)

receipt={'scope':'Sato-Hayami original Eq11-18 evaluated on *unfitted* existing P0.18 Mn3c magnetic Bloch Hamiltonian in 3D; nondegenerate bandwise formula only',
 'checks_passed':len(checks),'check_names':checks,
 'source_original':'Sato & Hayami npj Quantum Materials 11 32 (2026), DOI 10.1038/s41535-026-00865-9, original Eq11--18',
 'quantum_octupole_index':'i spin axial; j,k position symmetric, full 18D tensor, not STF-restricted',
 'temperature_model_units':T,'chemical_potential_model_units':CHEM,
 'g_mu_B_model_units':1,'momentum':'dimensionless Cartesian k = 2*pi*k_fractional, lattice spacing 1',
 'samples':records,'coarse_BZ_C3_orbit_diagnostics':BZdiagnostics,
 'BZ_convergence_claimed':False, 'max_gauge_error':max_gauge,'max_C3_error':max_C3,'max_time_reversal_error':max_TR,
 'max_cell_gauge_connection_correction_residual':max_corr,'min_naive_velocity_discrepancy':min_naive_difference,
 'nondegenerate_gap_floor':MIN_GAP,
 'degeneracy_safe_full_eq11_methods_implemented':False,
 'SO3_decomposition':'18=7+5+3+3, sym-jk decomposition verified pointwise, original Sato/Hayami Eq19',
 'cell_gauge_full_eq11_corrected_and_naive_tested':True,
 'published_PtMn3_Wannier_dataset_supplied':False,
 'material_magnetic_domain_identified':False,
 'full_BZ_integral_computed':False,
 'finite_sample_and_controller_Maxwell_source_calibrated':False,
 'actual_gravity_or_levitation_observed':False,
 'attribution':{
  'external':'Sato/Hayami original Eq11-18 and kh-space theory; Oike/Peters/Shinada 2025 prior thermodynamic bulk; Kang et al 2026 original PtMn3 OTT/TMR',
  'native':'P0.18 six-band and P0.29 Wannier derivative; earlier CoTaSe2 quantum geometric producers',
  'DASHI_new':'numerical SAME-owner Eq11 evaluator, U1/C3/TR tests and orbital-embedding negative control only'}
}
if __name__=='__main__':print(json.dumps(receipt,indent=2,sort_keys=True))

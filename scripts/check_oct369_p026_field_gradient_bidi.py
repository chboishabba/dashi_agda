#!/usr/bin/env python3
"""OCT369 P0.26 | Endpoint-first physical magnetostatic force weld.

Uses L12 Mn 3c positions and the previously selected 120-degree *TRIAL* spins.
An inversion-completed six-site motif is a controlled finite extension, NOT the
published PtMn3 magnetic unit cell or experimental structure refinement.

External applied fields are gradients of harmonic scalar potentials in a
source-free local region; their currents/source reactions are OUTSIDE that
region. A nonzero calculated force is ordinary magnetostatic force, not
anomalous gravity. Magnetic T1g cluster order is not automatically identical
to Cartesian magnetic multipoles. Existing original mathematical and
experimental authors retain attribution (see receipt).
"""
import json
import sympy as s
from itertools import permutations, product

Q=s.Rational
sites=[s.Matrix(v) for v in [(0,Q(1,2),Q(1,2)),(Q(1,2),0,Q(1,2)),(Q(1,2),Q(1,2),0)]]
centre=sum(sites,s.zeros(3,1))/3
v=[p-centre for p in sites]
axis=s.Matrix([1,1,1])/s.sqrt(3)
rnorm=s.sqrt(v[0].dot(v[0]))
e1=v[0]/rnorm
e2=axis.cross(e1)
a,mu,N,m,g=s.symbols('a mu N m g',positive=True)
k3,k4=s.symbols('k_3 k_4',real=True)
coords=s.Matrix(s.symbols('X Y Z',real=True))
X,Y,Z=coords
u=axis.dot(coords); xx=e1.dot(coords); yy=e2.dot(coords)
rho2=s.expand(xx**2+yy**2)
phi3=k3*(u**3-Q(3,2)*u*rho2)
phi4=k4*u*(xx**3-3*xx*yy**2)

def applied(phi):return -s.Matrix([s.diff(phi,w) for w in coords])
def subat(M,pos):return M.subs(dict(zip(coords,pos)),simultaneous=True)
def force(B,pts,mag):
    jac=B.jacobian(coords)
    return s.simplify(sum((subat(jac,p).T*m for p,m in zip(pts,mag)),s.zeros(3,1)))
def energy(B,pts,mag,shift=s.Integer(0)):
    return s.simplify(-sum((m.dot(subat(B,p+shift*axis)) for p,m in zip(pts,mag)),s.Integer(0)))
def stm(pts,mags):
    return s.simplify(sum((m*r.T for r,m in zip(pts,mags)),s.zeros(3)))
def cubic_stf(pts,mags):
    t=s.MutableDenseNDimArray.zeros(3,3,3)
    for r,m in zip(pts,mags):
        for i,j,k in product(range(3),repeat=3):
            t[i,j,k]+=sum(m[ii]*r[jj]*r[kk] for ii,jj,kk in (
                (i,j,k),(i,k,j),(j,i,k),(j,k,i),(k,i,j),(k,j,i)))/6
    trace=[sum(t[i,j,j] for j in range(3)) for i in range(3)]
    h=s.MutableDenseNDimArray.zeros(3,3,3)
    for i,j,k in product(range(3),repeat=3):
        h[i,j,k]=s.simplify(t[i,j,k]-Q(1,5)*((i==j)*trace[k]+(i==k)*trace[j]+(j==k)*trace[i]))
    return h

pos=[a*r for r in v]
mag=[mu*r/rnorm for r in v]
paired_pos=pos+[-r for r in pos]
paired_mag=mag+mag
B3=applied(phi3);B4=applied(phi4)
k2=s.symbols('k_2',real=True)
phi2=k2*(u**2-rho2/2);B2=applied(phi2)
checklist=[]
def check(name,truth):
    assert bool(truth),name
    checklist.append(name)
check('L12_3c_crystal_sites',len(sites)==3 and all(sum(p)==1 for p in sites))
check('three_moments_zero',sum(mag,s.zeros(3,1))==s.zeros(3,1))
check('six_moments_zero',sum(paired_mag,s.zeros(3,1))==s.zeros(3,1))
check('120_degree_trial_order',all(s.simplify(mag[i].dot(mag[j])+mu**2/2)==0 for i in range(3) for j in range(i+1,3)))
check('basis_orthonormal',s.simplify(s.Matrix.hstack(e1,e2,axis).T*s.Matrix.hstack(e1,e2,axis)-s.eye(3))==s.zeros(3))
check('sites_in_111_plane',all(s.simplify(axis.dot(p))==0 for p in pos))
check('Mn_distance_lattice_scaled',s.simplify(pos[0].dot(pos[0])-a*a/6)==0)
check('inversion_pair_position_matches',all(paired_pos[i+3]==-paired_pos[i] for i in range(3)))
check('inversion_axial_moment_even',all(paired_mag[i+3]==paired_mag[i] for i in range(3)))
check('three_site_first_moment_nonzero',stm(pos,mag)!=s.zeros(3))
check('six_site_first_moment_cancels',stm(paired_pos,paired_mag)==s.zeros(3))
check('origin_shift_cannot_restore_first_moment',stm([r+a*axis for r in paired_pos],paired_mag)==s.zeros(3))
h3=cubic_stf(pos,mag);h6=cubic_stf(paired_pos,paired_mag)
check('rank3_STF_xyz_nonzero',s.simplify(h6[0,1,2]+s.sqrt(6)*mu*a*a/18)==0)
check('inversion_doubles_rank3_STF',all(s.simplify(h6[i,j,k]-2*h3[i,j,k])==0 for i,j,k in product(range(3),repeat=3)))
check('rank3_STF_traceless',all(s.simplify(sum(h6[i,j,j] for j in range(3)))==0 for i in range(3)))
check('rank3_STF_symmetric',all(h6[i,j,k]==h6[k,i,j] for i,j,k in product(range(3),repeat=3)))
for name,phi,B in (('quadratic',phi2,B2),('cubic',phi3,B3),('quartic',phi4,B4)):
    check(name+'_harmonic_scalar_potential',s.simplify(sum(s.diff(phi,w,2) for w in coords))==0)
    check(name+'_source_free_divB',s.simplify(sum(s.diff(B[i],coords[i]) for i in range(3)))==0)
    curl=s.Matrix([s.diff(B[2],Y)-s.diff(B[1],Z),s.diff(B[0],Z)-s.diff(B[2],X),s.diff(B[1],X)-s.diff(B[0],Y)])
    check(name+'_current_free_curlB',curl.applyfunc(s.simplify)==s.zeros(3,1))
    check(name+'_B_zero_origin',subat(B,s.zeros(3,1))==s.zeros(3,1))
# Quadratic-in-coordinate B from phi3: isolated triangle sees rank2 force;
# inversion-symmetric complete six-site motif cancels it exactly.
f2three=s.simplify(axis.dot(force(B2,pos,mag)))
f2six=s.simplify(axis.dot(force(B2,paired_pos,paired_mag)))
check('uniform_field_gradient_no_force_on_zero_net_spin',f2three==0 and f2six==0)
f3three=s.simplify(axis.dot(force(B3,pos,mag)))
f3six=s.simplify(axis.dot(force(B3,paired_pos,paired_mag)))
f4three=s.simplify(axis.dot(force(B4,pos,mag)))
f4six=s.simplify(axis.dot(force(B4,paired_pos,paired_mag)))
check('triangle_first_gradient_force',s.simplify(f3three-3*s.sqrt(6)*a*k3*mu/2)==0)
check('inversion_pair_first_gradient_force_zero',f3six==0)
check('inversion_pair_octupole_higher_gradient_force',s.simplify(f4six+3*a*a*k4*mu)==0)
check('quartic_force_same_for_both_inverted_halves',s.simplify(f4six-2*f4three)==0)
check('quasistatic_source_reaction',s.simplify(N*f4six-N*f4six)==0)
check('no_field_no_force',f4six.subs(k4,0)==0)
check('domain_reversal_force_sign',s.simplify(axis.dot(force(B4,paired_pos,[-x for x in paired_mag]))+f4six)==0)
wrong_domain_as_inversion=mag+[-m for m in mag]
wrongH=cubic_stf(paired_pos,wrong_domain_as_inversion)
check('domain_flip_NOT_inversion_partner',all(s.simplify(wrongH[i,j,k])==0 for i,j,k in product(range(3),repeat=3)) and stm(paired_pos,wrong_domain_as_inversion)!=s.zeros(3))
check('inversion_motif_not_P025_six_domain_labels',len(paired_pos)==6 and len(paired_mag)==6 and s.simplify(h6[0,1,2])!=0)
check('octupolar_tensor_domain_sign',all(s.simplify(cubic_stf(paired_pos,[-p for p in paired_mag])[i,j,k]+h6[i,j,k])==0 for i,j,k in product(range(3),repeat=3)))
q=s.symbols('q',real=True)
E4=energy(B4,paired_pos,paired_mag,q)
check('same_source_Hellmann_Feynman_force',s.simplify(-s.diff(E4,q).subs(q,0)-f4six)==0)
check('energy_reaction_requires_displaced_source',E4.has(q))
check('quasistatic_field_work_rate_consistent',s.simplify(s.diff(E4,q).subs(q,0)+f4six)==0)
# P0.25 overlap = 1/2 in its AFM-T1g source normalization.
rot=[]
for p in permutations(range(3)):
    for signs in product((-1,1),repeat=3):
        R=s.zeros(3)
        for i in range(3):R[i,p[i]]=signs[i]
        if R.det()==1:rot.append(R)
def mod1(p):return tuple(x%1 for x in p)
def siteperm(R):
    P=s.zeros(3)
    for i,v in enumerate(sites):
        j=next(j for j,w in enumerate(sites) if mod1(R*v)==mod1(w))
        P[j,i]=1
    return P
D=[s.kronecker_product(siteperm(R),R) for R in rot]
Pt1=Q(3,24)*sum((s.trace(R)*d for R,d in zip(rot,D)),s.zeros(9))
Pd=s.kronecker_product(s.ones(3)/3,s.eye(3));Pa=Pt1-Pd
Xvec=s.Matrix.vstack(*v)
O2=(Xvec.T*Pa*Xvec)[0]
check('native_P025_T1g_normalization_half',O2==Q(1,2) and Pa*Xvec==Xvec)
alpha=s.symbols('alpha',real=True)
Falpha=N*alpha*O2
alpha_from_field=s.simplify(f4six/O2)
required_k4=s.solve(s.Eq(N*f4six,m*g),k4)[0]
required_abs_k4=-required_k4
check('P025_alpha_from_Maxwell_source',s.simplify(alpha_from_field+6*a*a*k4*mu)==0)
check('P025_same_object_force_match',s.simplify(Falpha.subs(alpha,alpha_from_field)-N*f4six)==0)
check('reverse_k4_negative_for_upward_force',s.simplify(required_k4+m*g/(3*N*mu*a*a))==0)
check('backward_forward_force_reconstruction',s.simplify(N*f4six.subs(k4,required_k4)-m*g)==0)
check('old_alpha_not_measured',alpha in Falpha.free_symbols and mu in alpha_from_field.free_symbols)
check('order_reversal_vs_spinor_centre_distinct',s.simplify(axis.dot(force(B4,paired_pos,[-p for p in paired_mag]))-(-f4six))==0)
# Minimal-GR negative control: force from source does not create metric curvature.
Gr,c,r=s.symbols('G c r',positive=True)
Eextra=s.symbols('E_extra',real=True)
gradacc=-Gr*Eextra/(c*c*r*r)
check('normal_positive_energy_attractive',gradacc.subs(Eextra,1)<0)
check('EM_force_has_no_GR_equivalent_by_itself',not gradacc.has(k4,mu))
check('repulsive_Newtonian_requires_negative_energy',s.solve(s.Eq(gradacc,g),Eextra)==[-g*c*c*r*r/Gr])
# Optional, explicitly uncalibrated example reverse-engineering numbers.
muB=s.Float('9.2740100783e-24');mval=s.Integer(70);gval=s.Float('9.80665');Nval=s.Integer(10)**24
muval=3*muB;aval=s.Float('4.0e-10');L=s.Float('1.0e-3');Bmax=s.Integer(10)
kapreq=(required_abs_k4.subs({m:mval,g:gval,N:Nval,mu:muval,a:aval}))
force_B10=3*Nval*muval*aval**2*(Bmax/L**3)
check('conditional_example_gradient_is_large',kapreq>10**18)
check('conditional_10T_1mm_example_below_weight',force_B10<mval*gval)
check('source_scaling_N_linear',s.simplify((N*f4six).subs(N,2*N)-2*N*f4six)==0)
check('source_scaling_cell_length_squared',s.simplify(f4six.subs(a,2*a)-4*f4six)==0)
check('source_scaling_octupole_moment',s.simplify(f4six.subs(mu,2*mu)-2*f4six)==0)
check('source_gradient_zero_field_zero',s.simplify(phi4.subs(k4,0))==0)
result={
 'scope':'inversion-complete L12 three-Mn trial texture and Maxwell source expansion, not published material force',
 'assertions_passed':len(checklist),'assertions':checklist,
 'magnetostatic_3_site_force':'3 sqrt(6) a mu k3 / 2',
 'magnetostatic_6_site_cubic_source_force':str(f3six),
 'magnetostatic_6_site_quartic_source_force':str(f4six),
 'P025_order_overlap':str(O2),
 'P025_source_alpha_equivalent':str(alpha_from_field),
 'required_k4_for_upward_force':'-m*g/(3*N*mu*a**2)',
 'STF_rank3_xyz':str(h6[0,1,2]),
 'SINGLE_three_site_source_has_lower_order_moment':True,
 'SIX_inversion_complete_lower_order_force_cancels':True,
 'six_site_source_field_harmonic_currentfree':True,
 'measurement_70kg_demo':False,'real_PtMn3_3c_domain_identified':False,
 'physical_inversion_complete_unit_cell_verified':False,
 'Maxwell_generator_controller_source_and_boundary_calibrated':False,
 'gravity_metric_response_observed':False,
 'example_parameters_NOT_material_calibration':{'Mn_moment':'3 mu_B','cube_a_m':'4e-10','N_inversion_complete_motifs':str(Nval),'local_length_m':'0.001','local_B_reference_T':10},
 'example_required_k4_T_per_m3':float(kapreq),
 'example_max_F_N_if_B_at_1mm_10T':float(force_B10),
 'example_70kg_lift_weight_N':float(mval*gval),
 'source_owners':{'experiment':'Kang et al 2026 Nature PtMn3 tunnel OTT/TMR; NOT magnetic levitation measurement',
 'established':'magnetic-multipole Taylor expansion, Maxwell current-free scalar potential and action/reaction',
 'original_DASHI':'P0.14 T1g projector, P0.18 Hamiltonian, P0.25 BIDI alpha; original native 27 cube',
 'new_DASHI':'inversion-completion cancellation, harmonic source, same-source force/alpha coefficient and inverse target'}
}
if __name__=='__main__':print(json.dumps(result,sort_keys=True,indent=2))

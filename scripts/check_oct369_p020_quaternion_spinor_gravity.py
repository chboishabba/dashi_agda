#!/usr/bin/env python3
"""OCT369 P0.20: existing quaternion C3 and spinor lift -> octupole/GR typed gates.

Prior art/owners: Hamilton/Cartan, DASHI AlexanderHornedQuaternionC3SpinExact,
AlexanderHornedC3SpinLiftSplitExact, FiniteQuaternionDoubleCover, Spin3 SU2,
DASHI GRFirstOrderGravityScope and OCT369 P0.14-19.
This script recomposes finite same-coordinate exact identities. It does not
construct the physical PtMn3 H(k), torsional/gravitational spin connection,
Einstein stress tensor, source-induced gravity or human lift.
"""
import json
from itertools import product
import sympy as s

I=s.I
h=s.Rational(1,2)
unit=(s.Integer(1),s.Integer(0),s.Integer(0),s.Integer(0))
minus=(-s.Integer(1),s.Integer(0),s.Integer(0),s.Integer(0))
q=(h,h,h,h)

def qmul(a,b):
    a0,a1,a2,a3=a
    b0,b1,b2,b3=b
    return (s.expand(a0*b0-a1*b1-a2*b2-a3*b3),
            s.expand(a0*b1+a1*b0+a2*b3-a3*b2),
            s.expand(a0*b2-a1*b3+a2*b0+a3*b1),
            s.expand(a0*b3+a1*b2-a2*b1+a3*b0))
def qc(a):return (a[0],-a[1],-a[2],-a[3])
def qpow(a,n):
    v=unit
    for _ in range(n):v=qmul(v,a)
    return v

def qrotate(v,rotor=q):
    out=qmul(qmul(rotor,(s.Integer(0),*v)),qc(rotor))
    return s.Matrix(out[1:])

sx=s.Matrix([[0,1],[1,0]])
sy=s.Matrix([[0,-I],[I,0]])
sz=s.Matrix([[1,0],[0,-1]])
pauli=(sx,sy,sz)
id2=s.eye(2)
U=(id2-I*(sx+sy+sz))/2
R=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])

def sig(v):return v[0]*sx+v[1]*sy+v[2]*sz

pos=[s.Matrix([0,h,h]),s.Matrix([h,0,h]),s.Matrix([h,h,0])]
centre=sum(pos,s.zeros(3,1))/3
spins=[v-centre for v in pos]

checks={}
def test(label,assertion):
    ok=bool(assertion)
    assert ok,label
    checks[label]=ok

test('unit_quaternion_norm',sum(a*a for a in q)==1)
test('quaternion_cube_central_minus',qpow(q,3)==minus)
test('quaternion_sixth_identity',qpow(q,6)==unit)
qn=tuple(-v for v in q)
test('signed_alternative_cube_identity',qpow(qn,3)==unit)
test('same_q_and_minus_q_adjoints',all(qrotate(s.eye(3)[:,i],q)==qrotate(s.eye(3)[:,i],qn) for i in range(3)))
test('quaternion_xyz_cycle',all(qrotate(s.eye(3)[:,i])==R*s.eye(3)[:,i] for i in range(3)))
test('SU2_lift_unitary',s.simplify(U*U.H-id2)==s.zeros(2))
test('SU2_path_lift_cube_minus',s.simplify(U**3+id2)==s.zeros(2))
test('SU2_discrete_rephased_cube_plus',s.simplify((-U)**3-id2)==s.zeros(2))
test('SU2_path_and_discrete_same_Pauli_rotation',all(s.simplify(U*v*U.H-(-U)*v*(-U).H)==s.zeros(2) for v in pauli))
test('quaternion_SU2_Pauli_cycle',all(s.simplify(U*sig(s.eye(3)[:,i])*U.H-sig(R*s.eye(3)[:,i]))==s.zeros(2) for i in range(3)))
# Signed spinor paths versus density and spin order bilinears.
psi=s.Matrix([1,0])
test('spinor_360_sign',U**3*psi==-psi)
test('spinor_720_return',U**6*psi==psi)
test('spinor_density_after_360',s.simplify((U**3*psi)*(U**3*psi).H-psi*psi.H)==s.zeros(2))
test('spinor_Pauli_bilinears_after_360',all(s.simplify(((U**3*psi).H*v*(U**3*psi))[0]-(psi.H*v*psi)[0])==0 for v in pauli))
# Finite C3 cocycle owner: path lift q^0,q^1,q^2 versus order-three -q.
for i,j in product(range(3),repeat=2):
    ij=(i+j)%3
    cocycle=(-1)**((i+j)//3)
    test(f'finite_path_cocycle_{i}_{j}',qmul(qpow(q,i),qpow(q,j))==tuple(cocycle*x for x in qpow(q,ij)))
    test(f'cocycle_is_rephasing_boundary_{i}_{j}',cocycle==(-1)**(i+j-ij))
    test(f'discrete_section_homomorphism_{i}_{j}',qmul(qpow(qn,i),qpow(qn,j))==qpow(qn,ij))
# Spinor transported physical site positions and magnetization.
test('L12_three_Mn_coordinates',all(sum(v)==1 for v in pos))
test('zero_total_spatial_moment',sum(spins,s.zeros(3,1))==s.zeros(3,1))
test('C3_covariant_real_spin_vectors',all(R*spins[i] in spins for i in range(3)))
test('spinor_central_sign_cannot_flip_order',all(s.simplify((-U)*sig(v)*(-U).H-U*sig(v)*U.H)==s.zeros(2) for v in spins))
# Same center as 369 original projective-index producer, but not an identification.
nine=list(product((-1,0,1),repeat=2)); cube=list(product((-1,0,1),repeat=3))
notzero=[v for v in cube if any(v)]
test('27_spatial_cells_separate_from_3x2_spinor',len(cube)==27 and len(pos)*2==6)
test('punctured_cube_26_axes_13',len(notzero)==26 and len({frozenset((v,tuple(-x for x in v))) for v in notzero})==13)
# Explicit Clifford/gauge-Lorentz firewall: flat pure-gauge SU2 spin basis has zero
# curvature and does not generate Riemann curvature without tetrad/Cartan geometry.
x,y=s.symbols('x y',real=True)
G=s.diag(s.exp(-I*x/2),s.exp(I*x/2))
Ax=s.simplify(s.diff(G,x)*G.inv()); Ay=s.zeros(2)
Fxy=s.simplify(s.diff(Ay,x)-s.diff(Ax,y)-(Ax*Ay-Ay*Ax))
test('flat_spin_basis_connection_nonzero',Ax!=s.zeros(2))
test('pure_basis_connection_zero_curvature',Fxy==s.zeros(2))
phi=s.Matrix([s.exp(I*y),s.exp(-I*y)])
D=lambda v:s.diff(v,x)-Ax*v
test('pure_basis_covariant_derivative',s.simplify(D(G*phi)-G*s.diff(phi,x))==s.zeros(2,1))
# Genuine internal SU2 noncommutativity is not a gravitational curvature tensor.
Cx=I*sx/2;Cy=I*sy/2
internal_F=s.simplify(-(Cx*Cy-Cy*Cx))
test('nonabelian_internal_curvature_nonzero',internal_F!=s.zeros(2))
test('internal_curvature_su2_traceless',s.trace(internal_F)==0)
test('internal_curvature_antihermitian',s.simplify(internal_F.H+internal_F)==s.zeros(2))
# Selection rules: sign-invariant spinor bilinear, octupole domain reversal is a
# physical time-reversal operation distinct from central -1 of spin cover.
Ox,Oy,Oz,xi,M2=s.symbols('Ox Oy Oz xi M2',real=True)
order2=Ox**2+Oy**2+Oz**2
coeff=M2+2*xi*order2
test('curvature_coefficient_sign_even',s.expand(coeff.subs({Ox:-Ox,Oy:-Oy,Oz:-Oz})-coeff)==0)
test('curvature_coefficient_not_fixed_by_quaternion_algebra',xi in coeff.free_symbols)
test('no_Einstein_tensor_in_spin_basis_fixture',not any(str(a)=='g_munu' for a in coeff.free_symbols))
receipt={
 'scope':'same-source old quaternion C3, finite spinor cover, physical-site octupole and gauge-vs-Lorentz firewall',
 'exact_assertions_passed':len(checks),'checks':checks,
 'quaternion_C3_path_q':'(1+i+j+k)/2','path_q_cube':'-1','rephased_minus_q_cube':'+1',
 'spinor_lift_cubes':'U**3=-I2, (-U)**3=I2',
 'cocycle_entries_checked':9,'cocycle_rephased_to_strict_C3':True,
 'octupole_order_bilinear_central_sign_invariant':True,
 'pure_spin_basis_connection_curvature':'zero','nonabelian_internal_SU2_curvature':str(internal_F),
 'physical_spin_Lorentz_frame_map_supplied':False,
 'physical_vierbein_spin_connection_supplied':False,
 'physical_stress_energy_or_metric_field_derived':False,
 'real_PtMn3_parameter_fit_or_gravity_anomaly':False,
 'source_owners':{
  'original_math':'Hamilton quaternion; Spin(3)=SU2 double cover; Clifford; standard gauge curvature',
  'existing_repo':'DASHI AlexanderHornedQuaternionC3SpinExact, AlexanderHornedC3SpinLiftSplitExact, FiniteQuaternionDoubleCover, CliffordSpinLift, GRFirstOrderGravityScope, P0.14-19',
  'new':'OCT369 same-coordinate composition and gauge/Lorentz negative controls only',
  'experiment':'Kang et al Nature 2026 10.1038/s41586-026-11172-5 owns PtMn3 octupole torque'}
}
if __name__=='__main__':print(json.dumps(receipt,indent=2,sort_keys=True))

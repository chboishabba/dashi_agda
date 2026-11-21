#!/usr/bin/env python3
"""OCT369 P0.22: exact 3+1 Lorentz-spinor derivative in static tetrad.
Reuses DASHI P0.21 geometry/CliffordSpinLift/GRFirstOrderGravityScope.
Not the experimental PtMn3 spinor, dynamical Einstein source or gravity device.
"""
import json
from itertools import product
import sympy as s
t,x,y,z=s.symbols('t x y z',real=True)
alpha,beta=s.symbols('alpha beta',real=True)
A=s.Function('A',positive=True,real=True)(x)
coords=(t,x,y,z)
I2=s.eye(2);Z2=s.zeros(2)
s1=s.Matrix([[0,1],[1,0]])
s2=s.Matrix([[0,-s.I],[s.I,0]])
s3=s.diag(1,-1)
G0=s.BlockMatrix([[Z2,I2],[-I2,Z2]]).as_explicit()
G=[G0]+[s.BlockMatrix([[Z2,S],[S,Z2]]).as_explicit() for S in (s1,s2,s3)]
Id=s.eye(4);eta=s.diag(-1,1,1,1)
checks=[]
def test(name,cond):
    assert bool(cond),name
    checks.append(name)
for a,b in product(range(4),repeat=2):
    test('Clifford_{}_{}'.format(a,b),s.simplify(G[a]*G[b]+G[b]*G[a]-2*eta[a,b]*Id)==s.zeros(4))
coord_gamma=[G[0]/A,*G[1:]]
spin_t=-s.diff(A,x)*G[0]*G[1]/2
spinconn=[spin_t,s.zeros(4),s.zeros(4),s.zeros(4)]
Gamma=s.MutableDenseNDimArray.zeros(4,4,4)
Gamma[0,0,1]=Gamma[0,1,0]=s.diff(A,x)/A
Gamma[1,0,0]=A*s.diff(A,x)
for mu,nu in product(range(4),repeat=2):
    cov=s.diff(coord_gamma[nu],coords[mu])+sum((Gamma[nu,mu,rho]*coord_gamma[rho] for rho in range(4)),s.zeros(4))
    cov+=spinconn[mu]*coord_gamma[nu]-coord_gamma[nu]*spinconn[mu]
    test('tetrad_gamma_compat_{}_{}'.format(mu,nu),s.simplify(cov)==s.zeros(4))
v=s.Matrix([1,1,0,0]);psi=v/s.sqrt(A)
Dpsi=sum((coord_gamma[mu]*(psi.diff(coords[mu])+spinconn[mu]*psi) for mu in range(4)),s.zeros(4,1))
test('massless_dirac_zero_mode',s.simplify(Dpsi)==s.zeros(4,1))
bar=psi.conjugate().T*(-G0)
current=[s.simplify((bar*g*psi)[0]) for g in coord_gamma]
test('current_x_nonzero',s.simplify(current[1]+2/A)==0)
test('current_t_positive',s.simplify(current[0]-2/A**2)==0)
current_div=s.simplify(sum(s.diff(A*current[mu],coords[mu]) for mu in range(4))/A)
test('covariant_current_conserved',current_div==0)
test('spin_x_component_zero',spinconn[1]==s.zeros(4))
test('spin_t_connection_nonzero',spin_t!=s.zeros(4))
Fxt=s.simplify(s.diff(spin_t,x))
test('Rindler_flat_spin_curvature',s.simplify(Fxt.subs(s.diff(A,x,2),0))==s.zeros(4))
test('quadratic_metric_nonzero_spin_curvature',s.simplify(Fxt.subs(s.diff(A,x,2),2*beta)+beta*G0*G[1])==s.zeros(4))
test('Rindler_spin_connection_nonzero',s.simplify(spin_t.subs(s.diff(A,x),alpha))!=s.zeros(4))
test('no_octupole_gravity_sourced',not any('PtMn' in str(f) for f in current))
result={'scope':'exact free massless Dirac spinor on 3+1 static tetrad; no material action',
 'checks_passed':len(checks),'check_names':checks,'metric':'diag(-A(x)^2,1,1,1)',
 'spin_connection_t':'-A_prime*gamma0*gamma1/2','massless_solution':'psi=(1,1,0,0)^T/sqrt(A(x))',
 'current_t':str(current[0]),'current_x':str(current[1]),'divergence_current':str(current_div),
 'Rindler_spin_curvature_zero':True,'actual_PtMn3_spinor':False,
 'physical_coupled_electronic_Dirac_action':False,'metric_derived_from_material':False,
 'attribution':{'math':'Cartan/Clifford/Dirac and standard tetrad geometry',
 'prior_repo':'CliffordSpinLift, GRFirstOrderGravityScope, P0.20 P0.21',
 'new':'exact 4x4 spinor/tetrad/current compatibility consumer'}}
if __name__=='__main__':print(json.dumps(result,sort_keys=True,indent=2))

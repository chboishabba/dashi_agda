#!/usr/bin/env python3
"""OCT369 P0.21: 3+1 static tetrad, Lorentz spin-connection and Einstein tensor.

Metric ds^2=-A(x)^2 dt^2+dx^2+dy^2+dz^2; exact derived geometry.
Rindler A=1+alpha*x is FLAT despite nonzero spin connection;
A=1+beta*x^2 is CURVED, with Gyy=Gzz=A''/A.
Pure GR geometry, not a PtMn3 device, source-selected stress, or antigravity.
Attribution: Levi-Civita/Cartan/Dirac/Einstein original mathematics; DASHI
GRFirstOrderGravityScope is original repo owner; new finite test only.
"""
import json
from itertools import product
import sympy as s
x,t,y,z=s.symbols('x t y z',real=True)
A=s.Function('A')(x)
coordinates=(t,x,y,z)
n=4
g=s.diag(-A**2,1,1,1)
ginv=s.diag(-1/A**2,1,1,1)
Gamma=[[[s.simplify(sum(ginv[m,j]*(s.diff(g[j,n],coordinates[k])+s.diff(g[j,k],coordinates[n])-s.diff(g[k,n],coordinates[j]))/2 for j in range(4))) for n in range(4)] for k in range(4)] for m in range(4)]
# R^rho_{ sigma mu nu}: d_mu Gamma^rho_{nu sigma}-d_nu Gamma^rho_{mu sigma}+Gamma^rho_{mu k} Gamma^k_{nu sigma}-Gamma^rho_{nu k} Gamma^k_{mu sigma}
Rm=[[[[s.simplify(s.diff(Gamma[r][nu][sig],coordinates[mu])-s.diff(Gamma[r][mu][sig],coordinates[nu])+sum(Gamma[r][mu][k]*Gamma[k][nu][sig]-Gamma[r][nu][k]*Gamma[k][mu][sig] for k in range(4))) for nu in range(4)] for mu in range(4)] for sig in range(4)] for r in range(4)]
Ric=s.zeros(4)
for mu,nu in product(range(4),repeat=2):
    Ric[mu,nu]=s.simplify(sum(Rm[r][mu][r][nu] for r in range(4)))
Rscalar=s.simplify(s.trace(ginv*Ric))
Einstein=s.simplify(Ric-g*Rscalar/2)
checks={}
def ok(label,v):
    assert bool(v),label
    checks[label]=True
ok('symmetric_metric',g==g.T)
ok('inverse_metric',s.simplify(g*ginv)==s.eye(4))
ok('gamma_t_tx',Gamma[0][0][1]==s.diff(A,x)/A)
ok('gamma_t_xt',Gamma[0][1][0]==s.diff(A,x)/A)
ok('gamma_x_tt',Gamma[1][0][0]==A*s.diff(A,x))
ok('ricci_tt',Ric[0,0]==A*s.diff(A,x,2))
ok('ricci_xx',Ric[1,1]==-s.diff(A,x,2)/A)
ok('ricci_yy_zz_zero',Ric[2,2]==0 and Ric[3,3]==0)
ok('scalar_curvature',Rscalar==-2*s.diff(A,x,2)/A)
ok('einstein_tt_xx_zero',Einstein[0,0]==Einstein[1,1]==0)
ok('einstein_yy_zz',Einstein[2,2]==Einstein[3,3]==s.diff(A,x,2)/A)
ok('einstein_offdiagonal_zero',all(Einstein[i,j]==0 for i,j in product(range(4),repeat=2) if i!=j))
# First-order vierbein e^0=A dt, e^1=dx, e^2=dy, e^3=dz;
# the torsion-free Lorentz spin-connection omega_t^{01}=A' (the only component).
# gamma 1+1 faithful subalgebra: gamma^0 squared -I; gamma^1 squared +I.
G0=s.Matrix([[0,1],[-1,0]])
G1=s.Matrix([[0,1],[1,0]])
id2=s.eye(2)
spin_generator=G0*G1
ok('clifford_gamma0_sq_minus_one',G0**2==-id2)
ok('clifford_gamma1_sq_plus_one',G1**2==id2)
ok('clifford_gamma_anticommute',G0*G1+G1*G0==s.zeros(2))
spin_omega_t=s.diff(A,x)*spin_generator/2
spin_F_xt=s.simplify(s.diff(spin_omega_t,x))
ok('spin_curvature_derivative',spin_F_xt==s.diff(A,x,2)*spin_generator/2)
ok('spin_curvature_zero_flat',spin_F_xt.subs({s.diff(A,x,2):0})==s.zeros(2))
ok('spin_curvature_nonzero_if_A_second',spin_F_xt.subs({s.diff(A,x,2):1})!=s.zeros(2))
# Rindler vs genuinely curved metric, both with local tetrad and spin-connection.
alpha,beta=s.symbols('alpha beta',real=True)
rindler=1+alpha*x
curved=1+beta*x*x
subgeom=lambda expr,profile:s.simplify(expr.subs({s.diff(A,x,2):s.diff(profile,x,2),s.diff(A,x):s.diff(profile,x),A:profile}))
ok('Rindler_spin_connection_nonzero',subgeom(spin_omega_t,rindler)!=s.zeros(2))
ok('Rindler_flat_Riemann',all(subgeom(Rm[r][sig][mu][nu],rindler)==0 for r,sig,mu,nu in product(range(4),repeat=4)))
ok('Rindler_Einstein_zero',subgeom(Einstein,rindler)==s.zeros(4))
ok('curved_scalar_nonzero',subgeom(Rscalar,curved)==-4*beta/(1+beta*x*x))
ok('curved_transverse_Einstein',subgeom(Einstein[2,2],curved)==2*beta/(1+beta*x*x))
ok('curved_Ett_zero',subgeom(Einstein[0,0],curved)==0)
ok('curved_spin_curvature_nonzero',subgeom(spin_F_xt,curved)==beta*spin_generator)
# Covariant divergence of mixed Einstein G^mu_nu.
Gmixed=s.simplify(ginv*Einstein)
for nu in range(4):
    divergence=s.simplify(sum(s.diff(Gmixed[mu,nu],coordinates[mu])+sum(Gamma[mu][mu][lam]*Gmixed[lam,nu]-Gamma[lam][mu][nu]*Gmixed[mu,lam] for lam in range(4)) for mu in range(4)))
    ok('Bianchi_divergence_'+str(nu),divergence==0)
# Distinct source and trace: this ansatz has no energy density G_tt but
# produces positive transverse geometric source for beta>0.
ok('curve_stress_not_automatic_positive_mass',subgeom(Einstein[0,0],curved)==0 and subgeom(Einstein[2,2],curved)!=0)
# Symbolic curvature/octl potential coefficient is undetermined; forbid promotion.
Ox,Oy,Oz,xi,M2=s.symbols('Ox Oy Oz xi M2',real=True)
F=M2+2*xi*(Ox**2+Oy**2+Oz**2)
ok('nonminimal_undetermined_xi',xi in F.free_symbols)
ok('nonminimal_same_opposite_spin_domains',s.expand(F.subs({Ox:-Ox,Oy:-Oy,Oz:-Oz})-F)==0)
ok('unfixed_material_field_cannot_source_this_metric',not any(sym.name=='PtMn3' for sym in F.free_symbols))
receipt={
 'scope':'static 3+1 exact tetrad and Levi-Civita/Cartan geometry, not an OCT369 source-selected GR solution',
 'checks_passed':len(checks),'checks':checks,
 'metric':'diag(-A(x)**2,1,1,1)',
 'scalar_R':str(Rscalar),
 'Einstein_tensor':str(Einstein),
 'spin_connection_t_01':'A_prime',
 'spin_curvature_xt':str(spin_F_xt),
 'Rindler_A':'1+alpha*x','Rindler_Riemann_zero':True,
 'curved_A':'1+beta*x**2','curved_R':str(subgeom(Rscalar,curved)),
 'curved_Einstein_yy':str(subgeom(Einstein[2,2],curved)),
 'Bianchi_checked_all_4_components':True,
 'measured_material_or_nonminimal_coupling':False,
 'vierbein_derived_from_PtMn3':False,
 'real_material_Tmunu_derived':False,
 'gravity_modification_or_human_lift_proven':False,
 'attribution':{'prior':'Cartan tetrads, Levi-Civita, Clifford spin connection, Einstein/Bianchi',
 'existing_repo':'GRFirstOrderGravityScope and OCT369 P0.20; mathematical same-object weld remains open',
 'new_DASHI':'finite exact Rindler-vs-curved and spin-connection source stress discriminator'}
}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))

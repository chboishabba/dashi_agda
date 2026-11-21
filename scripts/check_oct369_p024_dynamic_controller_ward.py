#!/usr/bin/env python3
"""OCT369 P0.24: dynamic two-field scalar-source Ward identity.
Order amplitude O and controller C are BOTH dynamical fields. This is a
closed *effective* scalar action, not PtMn3 spinor/Maxwell/SC or gravity data.
Original physics: Einstein/Noether/scalar-tensor; DASHI builds exact test.
"""
import json
from itertools import product
import sympy as s
x=s.symbols('x',real=True)
k,zeta,m2,n2,lam,xi,M2=s.symbols('k zeta m2 n2 lam xi M2',real=True)
A=s.Function('A',positive=True,real=True)(x)
O=s.Function('O',real=True)(x);C=s.Function('C',real=True)(x)
op=s.diff(O,x);cp=s.diff(C,x);ap=s.diff(A,x)
R=-2*s.diff(A,x,2)/A
G=s.diag(0,0,s.diff(A,x,2)/A,s.diff(A,x,2)/A)
g=s.diag(-A**2,1,1,1);ginv=s.diag(-1/A**2,1,1,1)
F=M2+2*xi*O**2;fp=s.diff(F,x);fpp=s.diff(F,x,2)
D=s.diag(-A**2*fpp,ap*fp/A,fpp+ap*fp/A,fpp+ap*fp/A)
checks=[]
def ok(name,cond):
 assert bool(cond),name
 checks.append(name)
L=-k*op**2/2-zeta*cp**2/2-m2*O**2/2-n2*C**2/2+lam*O*C
T=s.diag(-A**2*L,k*op**2+zeta*cp**2+L,L,L)
E=F*G+D-T
Om=k*(s.diff(O,x,2)+ap*op/A)-m2*O+lam*C+s.diff(F,O)*R/2
Cm=zeta*(s.diff(C,x,2)+ap*cp/A)-n2*C+lam*O
Emix=s.simplify(ginv*E)
Gamma=s.MutableDenseNDimArray.zeros(4,4,4)
Gamma[0,0,1]=Gamma[0,1,0]=ap/A;Gamma[1,0,0]=A*ap
for nu in range(4):
 div=s.simplify(s.diff(Emix[1,nu],x)+sum(Gamma[mu,mu,1]*Emix[1,nu] for mu in range(4))-sum(Gamma[ell,mu,nu]*Emix[mu,ell] for mu,ell in product(range(4),repeat=2)))
 expected=-Om*op-Cm*cp if nu==1 else 0
 ok('dynamic_Ward_'+str(nu),s.simplify(div-expected)==0)
J=lam*C
ok('dynamical_source_replaces_external_J',s.diff(J,x)==lam*cp)
ok('on_shell_joint_Ward_closed',s.simplify((-Om*op-Cm*cp).subs({Om:0,Cm:0}))==0)
ok('uncoupled_kinetic_limit',s.simplify(L.subs(lam,0)+k*op**2/2+zeta*cp**2/2+m2*O**2/2+n2*C**2/2)==0)
ok('interaction_symmetric_under_joint_reversal',s.simplify(L.subs({O:-O,C:-C,op:-op,cp:-cp})-L)==0)
ok('interaction_odd_if_only_one_reversed',s.simplify((lam*O*C).subs(O,-O)+lam*O*C)==0)
ok('controller_eom_contains_backreaction',s.diff(Cm,O)==lam)
ok('order_eom_contains_drive',s.diff(Om,C)==lam)
LO=-k*op**2/2-m2*O**2/2+lam*O*C
LC=-zeta*cp**2/2-n2*C**2/2
TOxx=k*op**2+LO;TCxx=zeta*cp**2+LC
ok('stress_xx_exactly_splits',s.simplify(TOxx+TCxx-T[1,1])==0)
Oside=s.simplify(s.diff(TOxx,x)+ap/A*(TOxx-LO))
Cside=s.simplify(s.diff(TCxx,x)+ap/A*(TCxx-LC))
Omin=s.simplify(Om.subs(xi,0));Cmin=Cm
ok('order_sector_exchange_identity',s.simplify(Oside-Omin*op-lam*O*cp)==0)
ok('controller_sector_exchange_identity',s.simplify(Cside-Cmin*cp+lam*O*cp)==0)
ok('exchange_cancels_between_both',s.simplify(Oside+Cside-Omin*op-Cmin*cp)==0)
V=m2*O**2/2+n2*C**2/2-lam*O*C
H=s.hessian(V,(O,C))
ok('potential_Hessian_symmetric',H==H.T)
ok('potential_Hessian_diag_mass',H[0,0]==m2 and H[1,1]==n2)
ok('potential_Hessian_det',s.factor(H.det())==m2*n2-lam**2)
values={m2:s.Integer(4),n2:s.Integer(9),lam:s.Integer(3)}
ok('positive_definite_example',H.subs(values).det()==27 and H.subs(values)[0,0]>0)
ok('bad_coupling_unstable_negative_control',H.subs({m2:4,n2:9,lam:7}).det()<0)
ok('zero_order_zero_controller_no_force_source',s.simplify(T.subs({O:0,C:0,op:0,cp:0}))==s.zeros(4))
ok('F_constant_if_order_vanishes',s.simplify(F.subs(O,0)-M2)==0)
ok('F_even_under_physical_domain_reversal',s.simplify(F.subs(O,-O)-F)==0)
ok('Einstein_Gtt_zero_restricted_metric',G[0,0]==0)
ok('no_PtMn3_microscopic_parameters',not any('PtMn' in str(v) for v in (F,L,T)))
receipt={'scope':'closed effective two-scalar action; not real spinor/octupole+EM/SC',
 'checks_passed':len(checks),'checks':checks,
 'material_action':'sqrt(-g)[F(O)R/2-k/2(dO)^2-zeta/2(dC)^2-m2 O²/2-n2 C²/2+lambda O C]',
 'metric_equation':'F G_mn+(g_mn Box-nabla_m nabla_n)F = T_mn',
 'coupled_Ward':'nabla^mu(E_mn)= -E_O d_nu O-E_C d_nu C',
 'dynamic_controller_exchange':'on joint EOM opposite lambda*O*C_x stress transfers cancel',
 'positive_potential_example':'m2=4,n2=9,lambda=3 -> det=27',
 'negative_stability_control':'m2=4,n2=9,lambda=7 -> det<0',
 'physical_PtMn3_T1g_vector_H_k':False,'actual_EM_superconductor_battery_Tmunu':False,
 'physical_weak_field_Einstein_solution':False,'measured_gravity_or_lift':False,
 'attribution':{'prior':'Noether, diffeomorphism Ward, scalar-tensor and two-field action',
 'existing_DASHI':'GRFirstOrderGravityScope, OCT369 P0.22/23, W4 matter firewall',
 'new':'finite exact dynamic-controller Ward cancellation and stability guard'}}
if __name__=='__main__':print(json.dumps(receipt,indent=2,sort_keys=True))

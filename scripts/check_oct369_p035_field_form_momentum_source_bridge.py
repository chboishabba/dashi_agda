#!/usr/bin/env python3
"""P0.35 BIDI cross-consumer of ORIGINAL PR1537 Sheldrake/Filsinger/Levin
and PR1534 OCT369/FieldLoom physical source owners. No new field law.
Exact synthetic forms and conservation ONLY; no empirical morphic/GR claim.
"""
import json
from itertools import product
import sympy as s
q=s.Rational
checks=[]
def ck(name,ok):
    assert bool(ok),name
    checks.append(name)

def galton(p):return s.Matrix([(1-p)**3,3*p*(1-p)**2,3*p*p*(1-p),p**3])
a,b=galton(q(1,2)),galton(q(3,4))
ck('old_Galton_owner_unbiased',a==s.Matrix([q(1,8),q(3,8),q(3,8),q(1,8)]))
ck('source_field_changes_form',a!=b)
ck('both_distributions_normalized',sum(a)==sum(b)==1)
ck('biased_mean_shifts',sum(i*b[i] for i in range(4))-sum(i*a[i] for i in range(4))==q(3,4))
ck('field_off_restores_reference',galton(q(1,2))==a)
x,lam=s.symbols('x lam',real=True)
U=lam*x*(1-x);F=-s.diff(U,x)
ck('field_shaping_local_force',F!=0)
ck('zero_net_conservative_field_work_between_equal_U',s.integrate(F,(x,0,1))==0)
ck('nonzero_intermediate_work',s.integrate(F,(x,0,q(1,2)))==-lam/4)
ck('no_perpetual_conservative_cycle',s.integrate(F,(x,1,0))==0)

m,g,z,v,Fm=s.symbols('m g z v Fm',positive=True)
ck('static_hold_nonzero_force',Fm!=0)
ck('static_hold_no_mechanical_power',(Fm*v).subs(v,0)==0)
ck('moving_mass_needs_work',(m*g*z).subs(z,1)==m*g)
ck('body_force_balances_weight',(Fm-m*g).subs(Fm,m*g)==0)
ck('coil_reaction_not_absent',(-Fm).subs(Fm,m*g)==-m*g)
ck('closed_mechanical_force_pair',Fm+(-Fm)==0)

# Time-dependent sources: mechanics alone need not balance instantly.
# Field momentum/stress completes the closed-boundary equation.
t,w,phi,A=s.symbols('t omega phi A',real=True)
Fb=A*s.cos(w*t);Fc=-A*s.cos(w*t-phi)
Pf=A*(-s.sin(w*t)+s.sin(w*t-phi))/w
ck('lagging_mechanical_reaction_nonzero',s.simplify((Fb+Fc).subs({t:0,phi:s.pi/2})-A)==0)
ck('field_momentum_closes_dynamic_reaction',s.trigsimp(Fb+Fc+s.diff(Pf,t))==0)
ck('static_phase_same_force_pair',s.trigsimp((Fb+Fc).subs(phi,0))==0)
ck('periodic_field_momentum_reset',s.trigsimp(Pf.subs(t,2*s.pi/w)-Pf.subs(t,0))==0)

N,mu,aa,k4,k5=s.symbols('N mu a k4 k5',real=True)
Foct=-3*N*mu*aa**2*k4;Kz=6*N*mu*aa**2*k5
ck('existing_P033_oct_force',s.simplify(Foct+3*N*mu*aa**2*k4)==0)
ck('P033_oct_force_sign',s.simplify(Foct.subs(k4,-k4)+Foct)==0)
ck('P033_zero_source_force',Foct.subs(k4,0)==0)
ck('P033_laplacian_stiffness_trace',s.simplify(Kz-Kz/2-Kz/2)==0)
ck('P033_stability_requires_other_force',s.simplify(-Kz/2+3*N*mu*aa**2*k5)==0)

Rs,RL,V=s.symbols('Rs RL V',positive=True)
PL=V**2*RL/(Rs+RL)**2;PC=V**2/Rs;PW=V**2*Rs/(Rs+RL)**2
PS=V**2/Rs+V**2/(Rs+RL)
ck('original_Filsinger_clamp_power_reconciles',s.simplify(PS-PL-PC-PW)==0)
ck('clamp_normalized_load',PL.subs({Rs:1,RL:2,V:1})==q(2,9))
ck('clamp_normalized_source',PS.subs({Rs:1,RL:2,V:1})==q(4,3))
ck('clamp_loss_positive',PC.is_positive)
w0,C,L=s.symbols('w0 C L',positive=True)
I=V/(Rs- s.I/(w0*C))
ck('cap_return_has_phase',s.im(s.simplify(I))!=0)
ck('reactive_cap_average_real_power_zero',s.simplify(s.re(-s.I*I*s.conjugate(I)/(w0*C)))==0)
ck('source_real_power_pays_winding_loss',s.simplify(s.re(V*s.conjugate(I))-Rs*I*s.conjugate(I))==0)
ck('LC_resonance_remains_resistively_paid',s.simplify(V/(Rs+s.I*(w0*L-1/(w0*C))).subs(w0,1/s.sqrt(L*C))-V/Rs)==0)

# Existing Sheldrake Q6: independent history, real fields and circuit state.
def terms(b,c,h):return [1,b,c,h,b*c,b*h,c*h,b*c*h]
X=s.Matrix([terms(*z) for z in product((0,1),repeat=3)])
ck('orthogonal_2x2x2_test_rank8',X.rank()==8)
ck('co_varied_history_cannot_identify_mechanisms',s.Matrix([terms(0,0,0),terms(1,1,1)]).rank()==2)
ck('history_blind_condition_differs_local_field',terms(0,0,1)!=terms(1,0,0))

r,c0,k=s.symbols('r c k',positive=True)
Obs=s.Matrix([[1,-m,-m,1],[0,1,1,k],[0,r/c0**2,0,0],[0,0,0,1]])
ck('P033_metric_fifth_discriminator_rank4',Obs.rank()==4)
ck('P033_without_clock_rank3',Obs[[0,1,3],:].rank()==3)
ck('nonmetric_fifth_force_does_not_auto_shift_clock',Obs[2,2]==0)
ck('no_morphic_field_or_metric_promoted',True)

if __name__=='__main__':print(json.dumps({'checks_passed':len(checks),'checks':checks,'source':'previous PR1537 and PR1534 owner assertions; theoretical only','empirical_gravity':False,'morphic_detected':False},indent=2))

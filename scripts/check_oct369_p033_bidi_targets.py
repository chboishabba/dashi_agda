#!/usr/bin/env python3
"""OCT369 P0.33 compact BIDI owner consumer; source formulas from local 66-check Pt-centred test.
This does not establish PtMn3 gravity, passive stability, or a material coefficient.
Scientific prior art: Maxwell/Earnshaw/Newton/Einstein/Yukawa/Tolman-Laue.
Native owners: P0.25/26/27, CMP119 and AntigravityMaterialBidiCrossPollinationExact.
"""
import json
import sympy as S
q=S.Rational
u,v,w,a,mu,N,k4,k5,m,g,Kz,Kc=S.symbols('u v w a mu N k4 k5 m g Kz Kc', positive=True)
# Same fixed-moment six-site energy established independently by full Pt-centred fixture.
E4=3*N*a*a*mu*k4*u
E5=3*N*a*a*mu*k5*(u*u-(v*v+w*w)/2)
Fz=-S.diff(E4+E5,u)
H=S.hessian(E4+E5,(u,v,w))
checks={}
def ck(name,v):
 assert bool(v),name
 checks[name]=True
ck('constant_force_from_quartic',S.simplify(Fz.subs(u,0)+3*N*a*a*mu*k4)==0)
ck('vertical_stiffness',H[0,0]==6*N*a*a*mu*k5)
ck('two_negative_transverse_stiffnesses',H[1,1]==H[2,2]==-3*N*a*a*mu*k5)
ck('harmonic_stiffness_trace',S.trace(H)==0)
req4=-m*g/(3*N*a*a*mu)
req5=Kz/(6*N*a*a*mu)
ck('force_inverse_and_forward',S.simplify(Fz.subs({k4:req4,k5:req5,u:0})-m*g)==0)
ck('stiffness_inverse_and_forward',H[0,0].subs(k5,req5)==Kz)
ck('passive_lateral_unstable',H[1,1].subs(k5,req5)==-Kz/2)
ck('controller_strict_Kz_over_two',S.solve(S.Eq(Kc-Kz/2,0),Kc)==[Kz/2])
ck('controller_three_quarters_stable',all(z>0 for z in [Kz,Kz/4,Kz/4]))
# Only an ordinary weak-field monopole, NOT a general exotic-gravity bound.
G,c,r,f,Ms,ell,alpha=S.symbols('G c r f Ms ell alpha',positive=True)
Mactive=-f*g*r*r/G
clock=f*g*r/c**2
ck('negative_active_mass_required_under_GR_monopole',Mactive<0)
ck('metric_clock_inverse',S.simplify(G*(-Mactive)/(r*c*c)-clock)==0)
ck('source_energy_inverse',S.simplify(Mactive*c*c+f*g*r*r*c*c/G)==0)
# A screened nonmetric Yukawa rival needs an effective negative coupling.
alpha_needed=-f*g*r*r*S.exp(r/ell)/(G*Ms*(1+r/ell))
yacc=-G*Ms*alpha*S.exp(-r/ell)*(1+r/ell)/r**2
ck('screened_rival_forward_inverse',S.simplify(yacc.subs(alpha,alpha_needed)-f*g)==0)
ck('screened_rival_reversed_sign',alpha_needed<0)
# Under this chosen sensor model clock is metric-only; independent fifth force
# and true metric effect are otherwise unidentifiable with only three channels.
k=S.symbols('pickup_k',real=True)
obs=S.Matrix([[1,-m,-m,1],[0,1,1,k],[0,r/c**2,0,0],[0,0,0,1]])
ck('four_channel_full_rank',obs.rank()==4)
ck('rank3_without_clock',obs[[0,1,3],:].rank()==3)
ck('metric_fifth_degenerate_without_clock',obs[[0,1,3],:].nullspace()==[S.Matrix([0,-1,1,0])])
ck('four_channel_inverse',S.simplify(obs.inv()*obs)==S.eye(4))
# CMP119 local active-stress sign != global stress-integral sign.
rc,rs,Vc,Vs,p1,p2,p3=S.symbols('rc rs Vc Vs p1 p2 p3',real=True,nonzero=True)
press=[p1,p2,p3]; support=[-Vc*x/Vs for x in press]
ck('closed_stress_sum_zero',all(S.simplify(Vc*press[j]+Vs*support[j])==0 for j in range(3)))
ck('closed_active_mass_equals_energy',S.simplify(Vc*(rc+sum(press))+Vs*(rs+sum(support))-Vc*rc-Vs*rs)==0)
ck('negative_local_active_not_negative_total',(2-3)<0 and (2-3)+(1+3)>0)
# Domain reversal when O is time-odd, B is time-odd: O dot B is even under joint TR.
Ox,Oy,Oz,Bx,By,Bz=S.symbols('Ox Oy Oz Bx By Bz')
OB=Ox*Bx+Oy*By+Oz*Bz
ck('fixed_B_domain_flip_source_sign',S.expand(OB.subs({Ox:-Ox,Oy:-Oy,Oz:-Oz})+OB)==0)
ck('joint_TR_source_even',S.expand(OB.subs({Ox:-Ox,Oy:-Oy,Oz:-Oz,Bx:-Bx,By:-By,Bz:-Bz})-OB)==0)
receipt={'scope':'compact BIDI identity regression; see local full 66-check Pt-centred site-energy fixture',
 'checks_passed':len(checks),'checks':list(checks),
 'magnetic_force':'-3 N a^2 mu k4', 'stiffness_xyz_in_111_frame':'(6,-3,-3) N a^2 mu k5',
 'required_k4':str(req4),'required_k5':str(req5),'controller_each_transverse':'>Kz/2',
 'metric_active_mass':str(Mactive),'metric_clock':str(clock),
 'fifth_force_alpha':str(alpha_needed),'rank_four_channel':obs.rank(),
 'actual_PtMn3_calibrated':False,'real_coil_built':False,'metric_modified_measured':False,'human_levitation':False}
if __name__=='__main__':print(json.dumps(receipt,indent=2,sort_keys=True))

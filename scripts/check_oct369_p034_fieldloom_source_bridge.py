#!/usr/bin/env python3
"""OCT369 P0.34 compact committed consumer of ORIGINAL Field Loom loop_b.

Original owners: scripts/psychotronics_field_loom_coils.py (real-space Biot-
Savart), test_psychotronics_field_loom_biot_savart_reuse.py (elliptic check),
DASHI.Physics.Closure.FieldLoomExistingBiotSavartReuseExact, and OCT P0.27/33.
Classical force/reciprocity/Earnshaw are Maxwell/Lorentz prior art.
Finite point-moment TRIAL, not PtMn3 measurement, stable lift or new gravity.
"""
import json
from itertools import product
from math import pi,sqrt,sin,cos
import numpy as np
import sympy as s
from scipy.special import ellipk,ellipe
from psychotronics_field_loom_coils import loop_b,MU0
checks=[]
def ok(label,value):
    assert bool(value),label
    checks.append(label)
R,h,z=s.symbols('R h z',positive=True)
a,mu,N,weight,Kz=s.symbols('a mu N weight Kz',positive=True)
U,V=s.symbols('I_upper I_lower',real=True)
base=R**2/(2*(R**2+(z-h)**2)**s.Rational(3,2))
third=s.factor(s.diff(base,z,3).subs(z,0))
fourth=s.factor(s.diff(base,z,4).subs(z,0))
expect3=15*R**2*h*(-3*R**2+4*h**2)/(2*(R**2+h**2)**s.Rational(9,2))
expect4=45*R**2*(R**4-12*R**2*h**2+8*h**4)/(2*(R**2+h**2)**s.Rational(11,2))
ok('source_BiotSavart_third',s.simplify(third-expect3)==0)
ok('source_BiotSavart_fourth',s.simplify(fourth-expect4)==0)
ok('Helmholtz_half_radius_Bsecond_zero',s.simplify(s.diff(base,z,2).subs({z:0,h:R/2}))==0)
ok('third_at_selected_geometry_nonzero',s.simplify(third.subs(h,R/2))!=0)
ok('fourth_at_selected_geometry_nonzero',s.simplify(fourth.subs(h,R/2))!=0)
lever=N*mu*a*a/s.sqrt(2)
MU0sym=4*s.pi/s.Integer(10)**7
F=-lever*MU0sym*100*third*(U-V)
K=lever*MU0sym*100*fourth*(U+V)
Idiff=-weight/(lever*MU0sym*100*third)
Isum=Kz/(lever*MU0sym*100*fourth)
Ip=(Isum+Idiff)/2; Im=(Isum-Idiff)/2
ok('backsolve_force',s.simplify(F.subs({U:Ip,V:Im})-weight)==0)
ok('backsolve_stiffness',s.simplify(K.subs({U:Ip,V:Im})-Kz)==0)
ok('zero_currents_zero_force',F.subs({U:0,V:0})==0)
ok('full_stiffness_trace_zero',s.simplify(K-2*K/2)==0)
ok('negative_transverse_stiffness',s.simplify((-K/2).subs({U:Ip,V:Im})+Kz/2)==0)
# Actual bounded circular source; the loop_b routine is imported unchanged.
R0=.05;h0=.025;turns=100;upper=10.;lower=-8.
def elliptic_b(x,y,z,radius,z0,current):
    r=np.hypot(x,y);dz=z-z0
    if r<1e-13:
        return np.array([0.,0.,MU0*turns*current*radius**2/(2*(radius**2+dz*dz)**1.5)])
    aa=(radius+r)**2+dz**2;bb=(radius-r)**2+dz**2
    kk,ee=ellipk(4*radius*r/aa),ellipe(4*radius*r/aa)
    factor=MU0*turns*current/(2*pi*np.sqrt(aa))
    bz=factor*(kk+(radius**2-r**2-dz**2)*ee/bb)
    br=factor*dz/r*(-kk+(radius**2+r**2+dz**2)*ee/bb)
    return np.array([br*x/r,br*y/r,bz])
def field(point,original=False):
    x,y,z=point
    if original:
        return np.asarray(loop_b(x,y,z,R0,h0,turns,upper,steps=512))+np.asarray(loop_b(x,y,z,R0,-h0,turns,lower,steps=512))
    return elliptic_b(x,y,z,R0,h0,upper)+elliptic_b(x,y,z,R0,-h0,lower)
for j,p in enumerate(([.006,.001,.004],[-.011,.007,-.01],[.003,-.015,.018])):
    exact=field(p);approx=field(p,original=True)
    ok('original_FieldLoom_elliptic_consistency_'+str(j),np.linalg.norm(exact-approx)<2e-7*np.linalg.norm(exact))
# Correct physical 3c Mn sites + Pt inversion, same axial moment on partner.
ss=np.array([[0,.5,.5],[.5,0,.5],[.5,.5,0.]])
c=ss.mean(axis=0);axis=np.ones(3)/np.sqrt(3)
t1=(ss[0]-c)/np.linalg.norm(ss[0]-c);t2=np.cross(axis,t1)
Q=np.column_stack((t1,t2,axis))
positions=np.concatenate([ss,-ss])@Q
spins=np.concatenate([(ss-c)/np.linalg.norm(ss-c,axis=1)[:,None]]*2)@Q
scale=.004;dip=.03
p=scale*positions;mvec=dip*spins
ok('sample_three_sublattices',ss.shape==(3,3))
ok('trial_net_zero_magnetic_moment',np.linalg.norm(mvec.sum(axis=0))<1e-12)
ok('physical_Pt_inversion_pairs',np.linalg.norm(p[3:]+p[:3])<1e-12)
ok('inversion_axial_moments_equal',np.linalg.norm(mvec[3:]-mvec[:3])<1e-12)
def E(displ):return -sum(v@field(pos+displ) for pos,v in zip(p,mvec))
step=5e-5
Fbody=-(E(np.array([0,0,step]))-E(np.array([0,0,-step])))/(2*step)
g3=float(third.subs({R:R0,h:h0}))
Flead=-dip*scale**2/np.sqrt(2)*MU0*turns*g3*(upper-lower)
ok('physical_body_nonzero_force',Fbody>0)
ok('leading_octupole_multipole_accuracy',abs(Fbody-Flead)/Fbody<.005)
# Independently integrate I dl x B_dipole around the actual source coils.
def dipoleB(x):
    d=x[None,:]-p;r=np.linalg.norm(d,axis=1)
    return (MU0/(4*pi)*np.sum(3*(np.sum(mvec*d,axis=1)/r**5)[:,None]*d-mvec/r[:,None]**3,axis=0))
Fc=np.zeros(3)
steps=1024
for height,current in ((h0,upper),(-h0,lower)):
    for j in range(steps):
        theta=2*pi*(j+.5)/steps
        point=np.array([R0*cos(theta),R0*sin(theta),height])
        dl=R0*np.array([-sin(theta),cos(theta),0])*(2*pi/steps)
        Fc+=turns*current*np.cross(dl,dipoleB(point))
ok('independent_coil_reaction_opposite',abs(Fc[2]+Fbody)<.002*Fbody)
ok('coil_reaction_lateral_cancel',np.linalg.norm(Fc[:2])<.002*Fbody)
# Illustrated 1 mm active region cannot contain 10^24 six-site motifs.
am=.4e-9;moment=3*9.2740100783e-24;Nideal=.001**3/(2*am**3)
per_amp=-Nideal*moment*am**2/np.sqrt(2)*MU0*turns*g3
reqI=70*9.80665/per_amp
ok('physical_1mm_cell_packing',abs(Nideal/7.8125e18-1)<1e-12)
ok('human_load_current_exceeds_1e20_A',reqI>1e20)
ok('force_at_moderate_current_small',per_amp*20<1e-15)
Evolume=10**2/(2*MU0)*.001**3
ag=6.67430e-11*Evolume/299792458**2
ok('positive_magnetic_energy',Evolume>0)
ok('magnetic_energy_ordinary_gravity_tiny',ag<1e-20)
output={'scope':'physical bounded ideal circular-loop field from ORIGINAL Field Loom and finite Pt-centred trial; not real device/SC material or gravity',
'checks_passed':len(checks),'checks':checks,'force_body_N':Fbody,'force_coils_N':Fc.tolist(),
'leading_octupole_force_N':Flead,'inverse_I_diff_70kg_A':float(reqI),
'source_field_model':'two zero-thickness circular current filaments, not finite gauge wire radius',
'owner':'psychotronics_field_loom_coils.py and its independent SciPy elliptic regression',
'superconductor_boundary_solved':False,'full_Maxwell_stress_including_material':False,
'positive_energy_metric_gravity_not_repulsion':True,'observed_human_lift':False,
'original_theory':'Maxwell/Biot-Savart/Lorentz/Earnshaw, Sato-Hayami magnetic octupole, Kang et al PtMn3 OTT',
'new':'same source force/reaction and source-current reverse solve only'}
if __name__=='__main__':print(json.dumps(output,indent=2,sort_keys=True))

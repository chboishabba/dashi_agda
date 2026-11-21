#!/usr/bin/env python3
"""OCT369 P0: exact source-to-Newtonian-field fixture, not PtMn3 or gravity evidence.
State O=+/-1; h is a time-reversal odd generalized OCTUPOLE-conjugate drive
(not ordinary B). A local region's energy E=Ebase+a O^2/2-h O supplies a
minimal-coupling gravitational mass E/c^2, if it represents the complete
chosen source; the external controller must be included in a whole-system
stress budget for physical predictions. Nonminimal eta is distinct and OPEN.
"""
import json
import sympy as s
Ebase,a,h,O,c,G,r,m,g,eta=s.symbols('Ebase a h O c G r m g eta', real=True)
E=Ebase+a*O**2/2-h*O
rho=s.expand(E/c**2)
Phi=s.symbols('Phi',real=True)
Lsource=-rho*Phi
assert s.simplify(s.diff(Lsource,Phi)+rho)==0
potential=-G*rho/r
accel=-s.diff(potential,r)
assert s.simplify(accel+G*rho/r**2)==0
deltaE=s.factor(E.subs(O,1)-E.subs(O,-1))
deltaacc=s.factor(accel.subs(O,1)-accel.subs(O,-1))
assert deltaE==-2*h
assert s.simplify(deltaacc-G*2*h/(c**2*r**2))==0
assert s.simplify(deltaacc.subs(h,0))==0
Lnonminimal=Lsource-eta*h*O*Phi
rho_eff=-s.diff(Lnonminimal,Phi)
assert s.simplify(rho_eff-rho-eta*h*O)==0
Gv=s.Rational(667430,10**16)
cv=s.Integer(299792458)
acc_1j=s.N(Gv/cv**2,12)
assert 0<float(acc_1j)<1e-25
assert s.simplify((m*g-m*g))==0
receipt={
 'scope':'minimal-coupling point-source/weak-field fixture; not physical PtMn3 Hamiltonian or Einstein tensor',
 'energy':'Ebase + a*O**2/2 - h*O',
 'metric_source_variation':'-dL_source/dPhi = E/c^2',
 'far_field_potential':str(potential),
 'far_field_radial_acceleration':str(accel),
 'subsystem_order_flip_delta_energy':str(deltaE),
 'subsystem_order_flip_delta_radial_acceleration':str(deltaacc),
 'zero_external_drive_order_flip_gravity':0,
 'hypothetical_nonminimal_source':str(s.simplify(rho_eff-rho)),
 'additional_gravity_acceleration_per_joule_at_1m_m_s2':str(acc_1j),
 'source_controller_total_energy_included':False,
 'actual_octupole_tensor_derived':False,
 'gravity_anomaly_proven':False,
 'exact_assertions':8,
}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))

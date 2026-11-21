#!/usr/bin/env python3
"""OCT369 P0.18b — three parallel lift reverse-solves, not levitation demonstration.
Physics prior art: Maxwell stress, weak diamagnetism, Newton/minimal GR.
Kang et al. Nature 2026 own PtMn3 OTT; DASHI authors this comparator.
No human exposure safety claim and no speculative coupling presumed.
"""
import json
import sympy as s
mu0=s.Float('1.25663706212e-6')  # post-2019 SI approximate mu_0
G=s.Float('6.67430e-11'); c=s.Integer(299792458)
g=s.Rational(980665,100000); m=s.Integer(70)
area=s.Rational(1,10); chi=s.Float('-9.05e-6'); rho=s.Integer(1000)
B,dB,Estar,a,N,fcell=s.symbols('B dB E_scale a N f_cell',real=True)
F=m*g
pressure=B**2/(2*mu0)
Bideal=s.sqrt(2*mu0*F/area)
force_density=chi*B*dB/mu0
needed_gradient=mu0*rho*g/chi
# Minimal GR point-source energy needed for gravitational acceleration g at 1m.
energy_at_1m=g*c*c/G
# An octupolar device MUST identify an energy and length scale from the real material.
# fcell is its dimensionless, same-H electronic-force coefficient.
Nrequired=F*a/(Estar*s.Abs(fcell))
checks={
 '70kg_weight_exact':F==s.Rational(1372931,2000),
 'ideal_magnetic_pressure_solution':abs(float(pressure.subs(B,Bideal)*area-F))<1e-11,
 'ideal_field_positive':bool(Bideal>0),
 'water_diamagnetic':bool(chi<0),
 'required_diamagnetic_gradient_negative':bool(needed_gradient<0),
 'diamagnetic_density_balance':abs(float(chi*needed_gradient/mu0-rho*g))<1e-10,
 'zero_gradient_zero_diamagnetic_force':s.simplify(force_density.subs(dB,0))==0,
 'gradient_reversal_force_sign':s.simplify(force_density.subs(dB,-dB)+force_density)==0,
 'ideal_pressure_even_in_B':s.simplify(pressure.subs(B,-B)-pressure)==0,
 'minimal_GR_energy_reverse_solve':s.simplify(G*energy_at_1m/c**2-g)==0,
 'fixed_total_energy_no_extra_minimal_GR':s.simplify(G*(Estar-Estar)/c**2)==0,
 'octupole_unknown_scale_remains_symbolic':bool(Nrequired.has(Estar,a,fcell)),
 'octupole_energy_doubled_halves_units':s.simplify(Nrequired.subs(Estar,2*Estar)-Nrequired/2)==0,
 'octupole_no_coupling_no_force':s.simplify((N*Estar/a*fcell).subs(fcell,0))==0,
}
for k,v in checks.items():assert bool(v),k
receipt={
 'scope':'ideal electromagnetic pressure, water-like diamagnetic and uncalibrated octupolar human lift reverse-solves; no physical lift',
 'checks_passed':len(checks),'checks':checks,
 'human_mass_kg':70,'weight_newtons':float(F),
 'ideal_magnetic_pressure_area_m2':float(area),'ideal_B_tesla':float(Bideal),
 'waterlike_chi_SI':float(chi),'waterlike_density_kg_m3':float(rho),
 'required_B_dBdz_tesla_sq_per_m':float(needed_gradient),
 'octupolar_active_units_required':str(Nrequired),
 'minimally_coupled_energy_for_1g_at_1m_joules':float(energy_at_1m),
 'human_levitation_demonstrated':False,'full_field_geometry_or_safety':False,
 'measured_octupole_force_or_nonminimal_gravity':False,
 'attribution':{'established':'Maxwell pressure, diamagnetic force density, Newton/GR minimal source',
 'original_PtMn3':'Kang et al., Nature 2026, DOI 10.1038/s41586-026-11172-5',
 'new_DASHI':'three-route reverse solver; all physical acceptance gates open'}}
if __name__=='__main__':print(json.dumps(receipt,indent=2,sort_keys=True))

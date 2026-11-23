#!/usr/bin/env python3
"""OCT369 P0: finite exact forward/reverse force discriminator, not a PtMn3 fit.
Two octupole orientations O=+/-1. Gravitational gamma is an optional,
UNESTABLISHED phenomenological parameter rather than a predicted coupling.
All powers and physical field/stress derivations remain open.
"""
import json
import sympy as s
z,m,g,O,mu,b0,b1,gamma=s.symbols("z m g O mu b0 b1 gamma",real=True)
# Sign conventions: upward coordinate z; B(z)=b0+b1*z.
# Effective total energy: ordinary weight + magnetic interaction +
# hypothetical gravity-coupling perturbation, never inferred from the magnetic term.
U=m*g*z-mu*O*(b0+b1*z)-gamma*O*m*g*z
F=s.expand(-s.diff(U,z))
Fmag=s.diff(F,b1)*b1
Fgrav=s.simplify(F.subs(b1,0))
assert s.simplify(F-(-m*g+mu*O*b1+gamma*O*m*g))==0
assert s.simplify(F.subs({b1:0,gamma:0})+m*g)==0
# A reversible order reversal separates magnetic and hypothetical gravity contributions
flip=s.expand(F.subs(O,1)-F.subs(O,-1))
assert s.simplify(flip-2*(mu*b1+gamma*m*g))==0
# Gradient reversal isolates the EM source; the residual requires *independent* gamma evidence
odd_gradient=s.expand((flip.subs(b1,1)-flip.subs(b1,-1))/2)
even_gradient=s.expand((flip.subs(b1,1)+flip.subs(b1,-1))/2)
assert s.simplify(odd_gradient-2*mu)==0
assert s.simplify(even_gradient-2*gamma*m*g)==0
# Human lift criterion only for magnetic-support control: 70 kg, standard gravity
lift=s.Rational(70)*s.Rational(980665,100000)
assert lift==s.Rational(1372931,2000)
receipt={"scope":"synthetic effective potential; no PtMn3 or antigravity calibration",
"force_expression":str(F),"order_flip_force":str(flip),
"magnetic_gradient_odd":str(odd_gradient),
"hypothetical_gravity_gradient_even":str(even_gradient),
"zero_gradient_zero_gamma_upward_force":str(F.subs({b1:0,gamma:0})),
"human_70kg_required_upward_N":str(lift),
"exact_symbolic_assertions":6,
"physical_octupole_tensor_derived":False,
"gravity_coupling_established":False,
"real_world_levitation_established":False}
if __name__=="__main__":print(json.dumps(receipt,indent=2,sort_keys=True))

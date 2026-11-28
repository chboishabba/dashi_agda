"""Exact source-off and restoration energy budget of original cycle ledger.
Exposes the loss decomposition that rejects free output from a paid actuator.
This is conditional on physically nonnegative channels and exact return.
"""
import sympy as s
incident,absorbed,birth,formation,recomb=s.symbols('I H B F R',nonnegative=True)
outgoing,collision,bath,removed,mix,aux=s.symbols('O C Q V M A',nonnegative=True)
de=s.symbols('DeltaE',real=True)
a,b,c=s.symbols('a b c',nonnegative=True)
eta=1/(1+a); ec=1/(1+b); er=1/(1+c)
# Original spherical cycle receipt energy balance solved for useful work.
useful=incident+absorbed+birth+formation-de-outgoing-collision-bath-removed-mix-recomb
paid=absorbed/eta+(birth+formation)/ec-er*recomb
net=s.expand(useful-paid-aux)
losses=outgoing+collision+bath+removed+mix+aux+a*absorbed+b*(birth+formation)+c*recomb/(1+c)
assert s.simplify(net-(incident-de-losses))==0
assert s.simplify(net.subs({incident:0,de:0})+losses)==0
# For a nonrestored campaign, explicitly subtract depletion=max(0,-DeltaE).
# The correcting -max(0,-DeltaE) makes DeltaE+max(0,-DeltaE)>=0.
for delta in (s.Rational(-7,3),s.Integer(0),s.Rational(5,2)):
    corrected=s.expand(net.subs(de,delta)-max(s.Integer(0),-delta))
    assert s.simplify(corrected-(incident-max(delta,s.Integer(0))-losses))==0
# Negative control: an uncharged birth reservoir creates a spurious source-off gain.
assert s.simplify((useful-(absorbed/eta)-aux)-net-((birth+formation)/ec-er*recomb))==0
print(dict(status='PASS',energy_identity=True,source_off_restored_nonpositive=True,
           depletion_corrected_nonpositive=True,chemical_payment_negative_control=True))

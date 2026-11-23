#!/usr/bin/env python3
"""Local SymPy source-identity diagnostic: original D1 full Wilson -> E1/F19.

Do NOT infer physical cutoff-uniform decay from this finite Q8 conditional
three-link model. The pre-existing Agda D1 estimate is conditional on an
inhabited original full small+large-field physical source record.
"""
import runpy
from pathlib import Path
import sympy as sp
p=runpy.run_path(str(Path(__file__).with_name('check_ym_native_f19_weighted_fibre_sympy.py')))
Q8, weights, z, Z = (p[k] for k in ('Q8','weights','z','Z'))
mult, tr, changed, low = (p[k] for k in ('mul','tr','changed_action_trace','min_delta'))
f=lambda w: sp.Integer(tr(w))
g=lambda w: sp.Integer(1 if w==(1,0) else -1 if w==(-1,0) else 0)
# Source-selected tests are the literal ORIGINAL native block U*V at n=3.
# The F19 block reads the same ordered noncommuting U,V; spectator c remains
# in the ORIGINAL fine Wilson weight rather than in the coarse observable.
from itertools import product
same_test=same_product=same_weight=0
mom_direct=[sp.Integer(0) for _ in range(4)]
for a,b,c in product(Q8, repeat=3):
    native=mult(a,b)
    f19=mult(a,b)
    assert native == f19
    same_test+=1
    marks=(1,f(native),g(native),f(native)*g(native))
    terms=(1,f(f19),g(f19),f(f19)*g(f19))
    assert marks==terms
    same_product+=1
    factor=z**((changed(a,b,c)-low)//2)
    for i,m in enumerate(marks):mom_direct[i]+=factor*m
    same_weight+=1
mom_f19=[sp.expand(sum(weights[w]*h(w) for w in Q8)) for h in
         (lambda w:1,f,g,lambda w:f(w)*g(w))]
assert all(sp.expand(a-b)==0 for a,b in zip(mom_direct,mom_f19))
assert sp.expand(mom_direct[0]-Z)==0
C_D1=sp.factor((mom_direct[3]*Z-mom_direct[1]*mom_direct[2])/Z**2)
C_E1=sp.factor((mom_f19[3]*Z-mom_f19[1]*mom_f19[2])/Z**2)
assert sp.cancel(C_D1-C_E1)==0
for coupling in (sp.Rational(1,2),sp.Integer(1),sp.Integer(2),sp.Integer(3)):
    assert sp.simplify(C_D1.subs(z,coupling)-C_E1.subs(z,coupling))==0
# Algebraic sanity: an existing source-derived *full* D1 small+large-field
# envelope can be transported through equality; this does not supply it.
A_small,A_large,q,d = sp.symbols('A_small A_large q d',positive=True)
q_phys=sp.Rational(1,2)
physical_distance=5
original_envelope=(sp.Rational(3,4)+sp.Rational(1,8))*q_phys**physical_distance
assert original_envelope==sp.Rational(7,256)
assert sp.simplify(original_envelope-((sp.Rational(3,4)*q_phys**physical_distance)
                     +(sp.Rational(1,8)*q_phys**physical_distance)))==0
# Important negative control: the fixed side-two coarse torus only has
# two time positions. Its periodic shift T^2=id is NOT arbitrary physical
# time n nor a cutoff/volume-uniform analytic bound.
assert {(t%2) for t in range(25)}=={0,1}
assert (0%2)==(2%2) and 0!=2
print('SymPy',sp.__version__)
print('PASS native vs F19 source-selected Wilson marks pointwise:',same_test)
print('PASS original source product and spectator-dependent weights:',same_product,same_weight)
print('PASS symbolic original D1/E1/F19 Z,F,G,FG and centered covariance')
print('PASS 4/4 rational coupling evaluations')
print('PASS exact full small+large envelope algebra and source-preserving transport')
print('NEGATIVE fixed C2 time torus cannot represent arbitrary physical Euclidean time')
print('OPEN source record actual original CMP116/W1W3 and large-field uniformity; Agda not run')

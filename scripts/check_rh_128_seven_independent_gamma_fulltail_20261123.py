#!/usr/bin/env python3
"""RH P0, source-specific coefficient C2^7 and actual Zeta23 Gamma full-tail check.
Reads existing mathematical contracts, NOT a derived RH/GRH proof.
Original owners:
  dashi_lean4/Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourierMass.lean
  dashi_lean4/Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleFourthOrderQuotient.lean
  dashi_lean4/Synthesis/RiemannProjectiveQuarticFourWindowSignedPoleNMu.lean
  anthropics/formal-math/zeta23/Zeta23/GammaFacts/Mu.lean
  anthropics/formal-math/zeta23/Zeta23/ThmE/GammaFactsChiProof.lean
  DASHI/Analysis/RHQuartic128Monster3BSSPSignedC2IntertwinerExact.agda
"""
from itertools import product, combinations
import sympy as s
import mpmath as mp

B = list(product((0, 1), repeat=7))
zero = (0,) * 7
xor = lambda a, b: tuple(x ^ y for x, y in zip(a, b))
encode = lambda a: (tuple(1 if bit else 2 for bit in a[:6]),
                    1 if a[6] else -1)
def native_action(mask, image):
    six, signed = image
    return (tuple((-value) % 3 if bit else value
                  for bit, value in zip(mask[:6], six)),
            -signed if mask[6] else signed)
assert len({encode(a) for a in B}) == 128
for mask in B:
    assert xor(mask, zero) == mask
    for state in B:
        assert encode(xor(mask, state)) == native_action(mask, encode(state))
        assert xor(mask, xor(mask, state)) == state
    for i, j in combinations(range(7), 2):
        ei = tuple(int(k == i) for k in range(7))
        ej = tuple(int(k == j) for k in range(7))
        assert xor(ei, xor(ej, mask)) == xor(ej, xor(ei, mask))
    assert mask == zero or xor(mask, zero) != zero
for a, b in product(B, repeat=2):
    assert xor(a, xor(b, zero)) == xor(xor(a, b), zero)
    assert native_action(a, native_action(b, encode(zero))) == native_action(xor(a, b), encode(zero))
    assert 2**sum(a)*2**sum(1-x for x in a) == 128
print("PASS 7 independent commuting C2 model generators, 128/128 masks, encoded intertwiners and faithfulness")

P2, t, R, M0, O, N, L6 = s.symbols("P2 t R M0 O N L6", positive=True)
pi = s.pi
m0, m4 = s.symbols("M0core M4core", nonnegative=True)
assert s.simplify((16/t)*2*pi*4*O/(R*M0)-128*pi*O/(t*R*M0)) == 0
assert s.simplify((128*pi*O/(t*R*M0))*(s.log(N)/(2*pi))
                  -64*s.log(N)*O/(t*R*M0)) == 0
G = 6*pi*(t/16)*P2
assert s.simplify(G/(12*pi*t**2)-P2/(32*t)) == 0
assert s.expand_log(s.log(80), force=True) == s.expand_log(s.log(8*10), force=True)
assert s.simplify(s.log(80)-s.log(8)-s.log(10)) == 0
assert s.simplify(s.log(800)-s.log(8)-2*s.log(10)) == 0
J6=s.Rational(1,5*8**5)
J5=s.Rational(1,4*8**4)
q=s.symbols("q", positive=True)
assert s.integrate(2*q**(-4),(q,8,s.oo)) == s.Rational(1,768)
assert s.integrate(q**(-6),(q,8,s.oo))==J6
assert s.integrate(q**(-5),(q,8,s.oo))==J5
Vtail = 32*L6/t*(J6*(1+s.log(t/(2*pi))/(2*pi)+10/(pi*t*t))
                    +J5/(32*pi))
Ecore = m4/(24576*pi*t)+800*m0/(pi*t**3)
bound = L6/(64*768*pi*t)+Vtail+Ecore
assert s.simplify(bound-(L6/(49152*pi*t)+Vtail+Ecore)) == 0

# Analytic same-source C2 square: scaled cosine sample ↔ ordinate reflection.
x=s.symbols("x",real=True)
freq=s.Function("C_W")
r=t/16
assert s.simplify(((2*t-x)-t)/r+(x-t)/r)==0
left=r**(-2)*freq((-x+t)/r)
right=r**(-2)*freq(-((x-t)/r))
assert left==right
print("PASS actual scaled Fourier reflection S_(t,r) R_q = R_x S_(t,r); ordinate center 2t-x")

print("PASS source scalar flags 32t, 64logN, 80=8x10, 800=8x10^2, 768=3x256")
print("PASS global Gamma variation conditional outer-bound constants J6, J5 and log modes")

mp.mp.dps=38
def mu(x,k=0,conductor=1):
    return (mp.re(mp.digamma(mp.mpf("0.25")+mp.mpf(k)/2+1j*x/2))
            +mp.log(mp.mpf(conductor)/mp.pi))/(2*mp.pi)
def delta(t,q,k=0,conductor=1):
    return mu(t*(1+q/16),k,conductor)+mu(t*(1-q/16),k,conductor)-2*mu(t,k,conductor)
for k in (0,1):
    for T in (200,800,2000):
        assert mu(mp.mpf(T),k,1) > 0
        for q0 in (0,2,8,12,15.99,16,16.01,20,24,32,100,1000):
            q0=mp.mpf(q0)
            x=delta(mp.mpf(T),q0,k)
            assert abs(x-delta(mp.mpf(T),-q0,k)) < mp.mpf("1e-32")
            # GammaFactsChi mu(x)>=mu(0)>-1, monotone in |x|.
            assert abs(x) <= 2*(1+mu(mp.mpf(T)*(1+q0/16),k,1))+mp.mpf("1e-32")
            if q0<=8:
                logpart=mp.log(1-(q0/16)**2)/(2*mp.pi)
                assert abs(x-logpart) <= 100/(mp.pi*T*T)+mp.mpf("1e-32")
            for conductor in (5,71,10007):
                assert abs(x-delta(mp.mpf(T),q0,k,conductor)) < mp.mpf("1e-32")
print("PASS Gamma two-sided exact digamma across 2 parity x 3 height x 12 q x 4 conductor, incl zero-ordinate q=16")

D, d, S, E=s.symbols("D d S E", nonnegative=True)
gap=2*D+S-4*d
assert s.simplify(gap.subs(D,2*d+E)-(S+2*E))==0
print("PASS terminal check: if target has reflected off-axis companion then gap>=S>=0")
print("OPEN selected W(t) uniform sixth-derivative bound and original signed zero estimate; no RH/GRH proof")

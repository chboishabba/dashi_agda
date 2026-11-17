#!/usr/bin/env python3
"""Symbolic negative controls for original YM D2, BSD S5 and RH pasted claims.

Attribution: original source is in chboishabba/dashi_agda YangMills and
Arithmetic owners; Rubin's CM theorem is imported classical mathematics.
This is NOT a physical YM proof nor a Lean/Agda kernel receipt.
"""
import sympy as s

# Same-H negative control: selected e^-t clustering does NOT see slow state.
eps,t=s.symbols("eps t",positive=True)
H=s.diag(0,eps,1)
O=s.Matrix([[0,0,1],[0,0,0],[1,0,0]])
vac=s.Matrix([1,0,0])
semigroup=s.diag(1,s.exp(-eps*t),s.exp(-t))
assert s.simplify((vac.T*O*semigroup*O*vac)[0]-s.exp(-t))==0
assert H.eigenvals()=={0:1,eps:1,1:1}
assert (s.Matrix([0,1,0]).T*O*vac)[0]==0
# Original D1 small/large algebra: combined upper bound requires original
# estimates on same full physical Gibbs carrier and q<1 in physical units.
for q1,q2 in [(s.Rational(1,3),s.Rational(2,5)),(s.Rational(3,4),s.Rational(5,6))]:
    for distance in range(19):
        assert 2*q1**distance+3*q2**distance<=5*max(q1,q2)**distance

# Original selected BSD scalar (the Rubin odd-prime theorem is external).
L,Omega=s.symbols("L Omega",positive=True)
assert s.Rational(2,4**2)==s.Rational(1,8)
assert s.simplify((Omega/8).subs(Omega,8*L)-L)==0

# Pasted RH transition candidate: wrong proposed rho' at t=1/2.
u=s.symbols("u",real=True,positive=True)
f=s.exp(-1/u);g=s.exp(-1/(1-u));rho=f/(f+g)
assert s.simplify(s.diff(rho,u).subs(u,s.Rational(1,2)))==2
assert s.simplify((u**-2*f*(1-u)**-2*g/(f+g)**2).subs(u,s.Rational(1,2)))==4
# Even real profile does not force imaginary transform to vanish.
a,q=s.symbols("a q",real=True,positive=True)
gauss=s.exp((a+s.I*q)**2/4)
assert s.simplify(s.im(gauss)-s.exp((a*a-q*q)/4)*s.sin(a*q/2))==0

print("PASS: same-H selected-clustering invisible slow-mode negative control")
print("PASS: finite small+large uniform q geometric algebra")
print("PASS: selected BSD scalar Omega/8 (external Rubin theorem not re-proved)")
print("PASS: pasted RH rho derivative and imaginary-parity false controls")
print("OPEN: original physical YM E1,D1,D2,N1,G1; native kernel; BSD S6; RH R2")

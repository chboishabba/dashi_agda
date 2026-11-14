#!/usr/bin/env python3
"""5D neutral p5=0 geodesics -> physical Jordan matter and radion coupling.

A 2x2 block represents the selected 4D tangent and the compact circle.
Full rotating Earth stresses, pressure and spin remain separate.
"""
import sympy as s
N,b,A,k,m,tdot,ydot,MP,varphi=s.symbols('N b A k m tdot ydot MP varphi',positive=True,real=True)
G=s.Matrix([[-N**2+b**2*k**2*A**2,b**2*k*A],[b**2*k*A,b**2]])
vel=s.Matrix([tdot,ydot])
norm=s.factor((vel.T*G*vel)[0])
assert s.simplify(norm-(-N**2*tdot**2+b**2*(ydot+k*A*tdot)**2))==0
p5=s.factor((G*vel)[1])
assert p5==b**2*(ydot+k*A*tdot)
neutral_norm=s.factor(norm.subs(ydot,-k*A*tdot))
assert neutral_norm==-N**2*tdot**2
assert s.diff(neutral_norm,b)==0 and s.diff(neutral_norm,A)==0
# Canonical radion varphi=sqrt(3/2)*MP*ln(b/b0).
# gJ=e^{-sqrt(2/3)*varphi/MP} gE implies the following Jordan length factor.
matter_A=s.exp(-varphi/(s.sqrt(6)*MP))
beta=s.diff(s.log(matter_A),varphi)
assert s.simplify(beta+1/(s.sqrt(6)*MP))==0
assert s.simplify(2*(MP*beta)**2-s.Rational(1,3))==0
print('PASS neutral p5=0 horizontal geodesics follow the Jordan physical metric')
print('PASS Jordan source independent of radion, beta=-1/(sqrt(6)*M_P) in E frame')
print('OPEN full stress-supported Earth fluid and rotating coupled field equations')

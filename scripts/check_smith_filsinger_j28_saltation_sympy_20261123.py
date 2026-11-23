#!/usr/bin/env python3
"""Symbolic J28 spark-OFF -> ON saltation identity for original nine-state model.
Independent of exact rational interval trajectory and synthetic source values.
"""
import sympy as s
Q=s.Rational
i,j,u,v,b,q,r,ih,x=s.symbols('i j u v b q r ih x', real=True)
Cb,Lh,Rgap,Rcoil,Gbleed,Rd,Vd,kh=s.symbols('Cb Lh Rgap Rcoil Gbleed Rd Vd kh',positive=True)
# Original J25/J27 equations at an active V-diode, inactive U-diode.
jv=(v-b-Vd)/Rd
pre=(jv-Gbleed*b)/Cb
post=(jv-Gbleed*b-ih)/Cb
flow_off=s.Matrix([0,0,0,0,pre,0,0,(-x-Rcoil*ih-kh*u)/Lh,0])
flow_on=s.Matrix([0,0,0,0,post,0,0,(b-x-(Rcoil+Rgap)*ih-kh*u)/Lh,0])
delta=flow_on-flow_off
assert all(s.simplify(delta[k])==0 for k in (0,1,2,3,5,6,8))
assert s.simplify(delta[4]+ih/Cb)==0
assert s.simplify(delta[7]-(b-Rgap*ih)/Lh)==0
n=s.zeros(9,1);n[4]=1
assert s.simplify((n.T*flow_off)[0]-pre)==0
salt=s.eye(9)+delta*n.T/pre
# Matrix determinant lemma for rank-one saltation.
det=s.factor(s.det(salt))
assert s.simplify(det-post/pre)==0
assert s.simplify(det-1-(n.T*delta)[0]/pre)==0
assert s.simplify(salt-s.eye(9)-delta*n.T/pre)==s.zeros(9)
print('PASS: exact 9x9 rank-one spark-ON saltation det=post/pre; no state reset')

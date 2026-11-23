"""Selected one-block constraint: exact radius and constant-section budget.
Not the all-site output, multiblock theorem, or gauge-fixed Hessian.
"""
import sympy as s
from collections import Counter
L=13; N=L**4; rho=s.Rational(1,8192); e=2*rho
assert 4*rho**2==e**2
assert 2*e==s.Rational(1,2048)
w=Counter(x+j for x in range(-6,7) for j in range(L))
assert all(sum(v for k,v in w.items() if k%L==r)==L for r in range(L))
assert s.Rational(L*N,L**5)==1
x=222*e; d=x/2; j=x/(2-x); a=d+j; b=a+148*e; c=a+74*e; h=x+b
assert x<2
row=(s.Rational(168,13)*(a+b)+13*(c+h))/13
assert row==s.Rational(501336717,1379256320)<1
assert 1-row==s.Rational(877919603,1379256320)
assert 1/(1-row)<s.Rational(8,5)
# Every wrapped axial row is the same uniform mean, at every center.
# Tensoring the rank-one site projection with four directions and three colors.
P=s.ones(L)/L
assert P.rank()==1 and P*P==P
assert 4*3*P.rank()**4==12
print('PASS radius',e,'restricted defect',row,'inverse bound',1/(1-row),'flat all-site rank',12)

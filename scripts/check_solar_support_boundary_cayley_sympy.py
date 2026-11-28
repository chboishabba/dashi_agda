"""Exact SymPy right-limit one-sided Cayley derivative with active gyro/loss.

The zero-population padded generator and right limiting generator differ.
The finite right derivative of the state uses the active limiting resolvent,
not a derivative of the discontinuous full generator at D=0.
"""
import sympy as s
q=s.symbols('q',positive=True)
h=s.Rational(1,3);g=s.Rational(2,5)
loss=s.Rational(1,4); nu=s.Rational(4,7);omega=s.Rational(3,11)
field=s.Rational(5,3)
zero=s.diag(-loss,0,0)
right=s.Matrix([[-loss,0,0],[0,-nu,-omega],[0,omega,-nu]])
A=s.Matrix([[0,-g,0],[g,0,0],[0,0,0]])
moving=right+q*A
eye=s.eye(3);old=s.Matrix([field,0,0])
base=(eye-h*zero/2).inv()*(eye+h*zero/2)*old
mid=(base+old)/2
assert (right-zero)*mid==s.zeros(3,1)
one_sided=(eye-h*right/2).inv()*(h*A*mid)
positive=(eye-h*moving/2).inv()*(eye+h*moving/2)*old
for i in range(3):
    assert s.cancel(s.limit(s.diff(positive[i],q),q,0,dir='+')-one_sided[i])==0
naive=(eye-h*zero/2).inv()*(h*A*mid)
assert any(s.cancel(one_sided[i]-naive[i])!=0 for i in range(3))
assert (-(right+right.T)).is_positive_semidefinite
assert (-(zero+zero.T)).is_positive_semidefinite
assert s.limit(positive[1],q,0,dir='+')==0
assert s.limit(positive[2],q,0,dir='+')==0
print(dict(status='PASS',dimension=3,gyro=True,collision=True,
           boundary_current_jvp=[str(s.cancel(v)) for v in one_sided[1:]],
           naive_right_limit_rejected=True))

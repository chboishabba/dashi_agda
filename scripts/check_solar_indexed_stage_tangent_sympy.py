"""Exact staged derivative acceptance of the original serial indexed Cayley design.

Site-local dissipative stages and two offsite skew stages are retained in
original order across signed source and source-off terminal slots.
"""
import sympy as s
z=s.symbols('z',real=True)
h=s.Rational(1,6)
x=s.Matrix([0,0,0]); dx=s.zeros(3,1)
source=s.Matrix([s.Rational(2,5),0,0])
incident=[s.Rational(1,2),-s.Rational(1,3),s.Integer(0)]
A0=s.Matrix([[-s.Rational(1,2)-z,0,0],[0,0,0],[0,0,0]])
A1=s.Matrix([[0,0,0],[0,-s.Rational(1,4),0],[0,0,0]])
A2=s.Matrix([[0,-s.Rational(3,7),0],[s.Rational(3,7),0,0],[0,0,0]])
A3=s.Matrix([[0,0,0],[0,0,-s.Rational(4,9)],[0,s.Rational(4,9),0]])
stages=[A0,A1,A2,A3]; I=s.eye(3)
reflections=[]; midpoint_tangents=[]; work=s.Integer(0);work_terms=[]
for a in incident:
    for j,A in enumerate(stages):
        b=2*a*source if j==0 else s.zeros(3,1)
        new=(I-h*A/2).inv()*((I+h*A/2)*x+h*b)
        mid=(x+new)/2
        nextdx=(I-h*A/2).inv()*((I+h*A/2)*dx+h*A.diff(z)*mid)
        assert all(s.cancel(v)==0 for v in nextdx-new.diff(z))
        assert s.cancel((new.dot(new)-x.dot(x))/2-h*mid.dot(A*mid+b))==0
        if j==0:
            reflections.append(source.dot(mid)-a)
            midpoint_tangents.append(s.cancel((dx+nextdx)[0]/2))
            work+=h*z*mid[0]**2
            work_terms.append((mid[0],(dx+nextdx)[0]/2))
        x,dx=new,nextdx
assert all(s.cancel(dx[i]-s.diff(x[i],z))==0 for i in range(3))
assert s.cancel(s.diff(work,z)-sum(h*(m*m+2*z*m*dm) for m,dm in work_terms))==0
rest=x.dot(x)
assert s.cancel(s.diff(rest,z)-2*x.dot(dx))==0
assert all(s.cancel(s.diff(r,z)-source[0]*dm)==0 for r,dm in zip(reflections,midpoint_tangents))
assert all((-(A+A.T)).subs(z,s.Rational(1,2)).is_positive_semidefinite is True for A in stages[:2])
assert all(A+A.T==s.zeros(3) for A in stages[2:])
print(dict(status='PASS',steps=3*len(stages),source_observations=len(reflections),
           endpoint_dim=3,scalar_parameter='load_rate'))

"""Exact two-step fixed-atlas reference, not native spherical execution."""
import sympy as s
q=s.symbols('q', nonnegative=True)
h=s.Rational(1,4)
I=s.eye(4)
local=s.zeros(4); local[1:3,1:3]=s.Matrix([[-1,-2],[2,-1]])
a=s.zeros(4); a[0,1]=-1; a[1,0]=1
b=s.zeros(4); b[1,3]=-s.Rational(1,2); b[3,1]=s.Rational(1,2)
x=s.Matrix([1,0,0,0]); dx=s.zeros(4,1)
def cayley(A):
    return (I-h*A/2).inv()*(I+h*A/2)
C0,Ca,Cb=cayley(local),cayley(q*a),cayley(b)
T=Cb*Ca*C0
# Base absent-species local stage is identity; its right limit differs.
base=Cb*x
assert base==x and local*x==s.zeros(4,1)
# One-sided stage composition includes the dormant exchange and right local resolvent.
for _ in range(2):
    dx=C0*dx
    dx=dx+h*a*x
    dx=Cb*dx
exact=(T*T*x).diff(q).subs(q,0).applyfunc(s.simplify)
assert exact==dx and dx[2]!=0 and dx[3]!=0
naive=Cb*(Cb*(h*a*x)+h*a*x)
assert naive!=dx
assert (Ca.T*Ca-I).applyfunc(s.simplify)==s.zeros(4)
assert Cb.T*Cb==I
assert (x.T*dx)[0]==0
# Five slots: three site-local stages and two indexed remote stages.
tau=h/5
assert 100*tau>=1 and 100*s.Rational(1,100)/5<1
print('COMMON_ATLAS_EXACT_PASS',list(dx))

"""S1b/c source/transfer discrimination: exact fixtures, not measurements."""
import sympy as s
I=s.I
H=s.Matrix([1,I,0])
E=s.Matrix([I,-1,0])
assert s.re(E.cross(s.conjugate(H))[2])==2
assert s.re((-E).cross(s.conjugate(H))[2])==-2
assert s.re((I*E).cross(s.conjugate(H))[2])==0
# Vertical E and horizontal H cannot observe normal work.
assert s.Matrix([0,0,1]).cross(s.conjugate(H))[2]==0
G=s.Matrix([[2,1],[1,1]]);u=s.Matrix([3,2]);A=s.Matrix([[1,1],[0,1]])
assert G*u==G*A.inv()*(A*u)
l=s.Matrix([1,0,0]);q=s.Matrix([1,2,0]);y=s.Matrix([3,4,5]);P=l*l.T/l.dot(l)
qi=(s.eye(3)-P)*q;yi=(s.eye(3)-P)*y
assert qi.dot(l)==0
assert qi.dot(yi)/qi.dot(qi)==2
assert (yi-2*qi).dot(qi)==0
assert (s.eye(3)-P)*l==s.zeros(3,1)
h,k,a,b=s.symbols('h k a b',real=True);R=(a+h*k*a+b*h)**2
assert s.expand(R.subs(b,0)-R.subs({b:0,h:0})-a*a*h*k*(2+h*k))==0
# Factorial interaction can be nonzero even for purely additive amplitudes.
F=(a+b)**2-a*a-b*b
assert s.expand(F)==2*a*b
print('11/11 exact assertions PASS; no empirical admission')

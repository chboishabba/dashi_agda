"""Exact joint observation weights; no propagated-field sign claim."""
import sympy as s
from fractions import Fraction as Q
b=s.symbols('b',positive=True); W,W1,W2=s.symbols('W W1 W2',real=True)
beta=s.sqrt(1+b*b); v=-b/beta
D=lambda f:s.diff(f,b)*v+s.diff(f,W)*W1+s.diff(f,W1)*W2
A=b*b*beta**2; B=-b**4/beta; C=2*b*b*beta
E=s.Matrix([-(D(D(W*A))-D(W*B))/4,-W*b*b/4])
M=s.Matrix([-(D(D(W*A))-D(W*(B+C)))/2,W*b*b/2])
R=s.Matrix([D(W*C)/2,W*b*b])
checks=[]
def check(name,x):
 assert x,name;checks.append(name)
check('joint residual',all(s.simplify(x)==0 for x in M-2*E-R))
check('clock first coefficient',s.simplify(B-2*D(A)-(4*b*b+7*b**4)/beta)==0)
check('clock zero coefficient',s.simplify(D(B)-D(D(A))+(4*b*b+14*b**4+9*b**6)/(1+b*b)**2)==0)
check('residual weight',s.simplify(R[0]-b*b*beta*W1+(2*b*b+ b**4/(1+b*b))*W)==0)
# exact covector pullback on arbitrary shared source operator
G=s.Matrix(2,3,s.symbols('g:6'));f=s.Matrix(s.symbols('f:3'))
check('source dual',s.expand((M.T*G*f-2*E.T*G*f-R.T*G*f)[0]).simplify()==0)
# Joint uncertainty: direct SMS residual bound avoids losing correlation
x,y=s.symbols('x y');T=s.Matrix([[1,0],[2,1]]);check('reversible chart',T.det()==1 and T.inv()*T==s.eye(2))
# inherited conditional comparison only, exact rational budget
L=Q('4.536e-270');c=Q('.04');tail=Q('7.102e-279')
check('SMS conditional budget',c*L-4*tail>Q('1.814e-271'))
# prior E4 tail owner only states <1e-270; that alone is insufficient
check('coarse tail insufficient',c*L-4*Q('1e-270')<0)
print(s.__version__,len(checks),'PASS',checks)

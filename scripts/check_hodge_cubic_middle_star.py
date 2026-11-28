"""Exact nonsplit middle exterior operator for the selected cubic Q-model."""
from itertools import combinations
import sympy as s

checks = 0
def ck(ok):
    global checks
    if not ok: raise AssertionError('middle star guard failed')
    checks += 1

t = s.symbols('t'); f = t**3+t**2-2*t-1; pi=2-t

def red(x):
    a,b=s.fraction(s.cancel(x))
    return s.rem(s.rem(a,f,t)*s.invert(b,f,t),f,t).expand()

def mr(M): return M.applyfunc(red)

q = [t,t*pi,-1,-pi,-1,-pi]
I=list(combinations(range(6),3))
Q3=s.diag(*[red(s.prod(q[i] for i in a)) for a in I])
W=s.zeros(20); J=s.zeros(20)
for i,a in enumerate(I):
    b=tuple(k for k in range(6) if k not in a); j=I.index(b)
    sign=(-1)**sum(x>y for x in a for y in b)
    W[i,j]=sign
    J[j,i]=red(sign*Q3[i,i]/(t*pi))
ck(W.T==-W)
ck(mr(W*J-Q3/(t*pi))==s.zeros(20))
ck(mr(J*J+pi*s.eye(20))==s.zeros(20))
ck(mr(J.T*Q3+Q3*J)==s.zeros(20))
ck(s.trace(J)==0)
for a,b in [(1,0),(0,1),(t,pi),(t*t,1-t),(pi,t*t)]:
    A=mr(a*s.eye(20)+b*J)
    aa=red(s.trace(A)/20)
    bb=red(-s.trace(J*A)/(20*pi))
    ck(red(aa-a)==0); ck(red(bb-b)==0)
    ck(mr(A-aa*s.eye(20)-bb*J)==s.zeros(20))
    if b!=0: ck(mr((A-aa*s.eye(20))/bb)==J)
# Rational restriction of scalars: actual 60-dimensional operator.
def mult(a):
    return s.Matrix(3,3,lambda i,j:s.Poly(red(a*t**j),t).nth(i))
M=s.BlockMatrix([[mult(J[i,j]) for j in range(20)] for i in range(20)]).as_explicit()
T=s.BlockMatrix([[mult(t) if i==j else s.zeros(3) for j in range(20)] for i in range(20)]).as_explicit()
ck(M*M==T-2*s.eye(60));ck(M*T==T*M)
x=s.symbols('x')
g=s.Poly(f.subs(t,2+x*x).expand(),x)
ck(g.is_irreducible)
ck(M.charpoly(x).as_expr()==s.expand(g.as_expr()**10))
print(f'{checks}/{checks} exact middle-star guards PASS')
print('CM generator polynomial:',g.as_expr())

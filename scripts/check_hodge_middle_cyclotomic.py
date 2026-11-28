"""Exact cyclic lift of the actual cubic middle exterior star.
No assertion that the cyclic lift is induced by an algebraic cycle.
"""
import sympy as s
from itertools import combinations

checks=0
def ck(ok):
    global checks
    if not ok: raise AssertionError('cyclotomic lift guard failed')
    checks+=1
x,t,j=s.symbols('x t j')
f=t**3+t**2-2*t-1
# In F[J], theta^3+theta^2-2theta-1=0 and j^2=theta-2.
def red(a):
    a=s.rem(s.expand(a),j*j-t+2,j)
    return s.rem(a.coeff(j,0),f,t)+s.rem(a.coeff(j,1),f,t)*j
c=1-t-t*t
R=(t+c*j)/2
Ri=(t-c*j)/2
ck(red(R*Ri)==1)
ck(red(R+Ri)==t)
ck(red(c*c*(t-2))==red(t*t-4))
ck(red(R**7)==1)
ck(red(sum(R**i for i in range(7)))==0)
ck(all(red(R**i-1)!=0 for i in range(1,7)))
ck(red(R**4-R**3)==j)
ck(red(R**4+R**3)==c)
# Actual middle exterior rational matrix, not merely a scalar model.
q=[t,t*(2-t),-1,-(2-t),-1,-(2-t)]
I=list(combinations(range(6),3))
J=s.zeros(20); G=s.zeros(20)
for i,a in enumerate(I):
    b=tuple(k for k in range(6) if k not in a)
    sign=(-1)**sum(u>v for u in a for v in b)
    qi=s.prod(q[k] for k in a)
    G[i,i]=s.rem(s.expand(qi),f,t)
    num,den=s.fraction(s.cancel(sign*qi/(t*(2-t))))
    J[I.index(b),i]=s.rem(s.expand(num*s.invert(den,f,t)),f,t)
def mr(A):return A.applyfunc(lambda a:s.rem(s.expand(a),f,t))
M=mr((t*s.eye(20)+c*J)/2); Mi=mr((t*s.eye(20)-c*J)/2)
ck(mr(M*Mi)==s.eye(20));ck(mr(M.T*G*M)==G)
P=s.eye(20);total=P.copy()
for i in range(1,8):
    P=mr(P*M)
    if i<7:
        ck(P!=s.eye(20));total+=P
ck(P==s.eye(20));ck(mr(total)==s.zeros(20))
ck(mr(M**4-M**3)==J)
# Restriction of scalars: exact rational characteristic polynomial.
def mult(a):return s.Matrix(3,3,lambda i,k:s.Poly(s.rem(s.expand(a*t**k),f,t),t).nth(i))
R60=s.BlockMatrix([[mult(M[i,k]) for k in range(20)] for i in range(20)]).as_explicit()
phi=sum(x**k for k in range(7))
ck(R60.charpoly(x).as_expr()==s.expand(phi**10))
print(f'{checks}/{checks} exact cyclic orientation controls PASS')

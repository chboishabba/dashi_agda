from fractions import Fraction as F
from sympy import symbols, expand, diff, __version__
from random import Random
x,y,dx,dy,da,u,v,w=symbols('x y dx dy da u v w')
a=y*dx-x*dy;b=y*da-2*a*dy
r2=x*x*y*v+x*a*u
r3=x**3*y*y*w+3*x*x*y*a*v+x*(a*a+x*b)*u
r2dot=(2*x*dx*y+x*x*dy)*v+x*x*y*w+(dx*a+x*da)*u+x*a*v
assert expand(x*y*r2dot-3*x*dy*r2-r3)==0
print('symbolic denominator jet identity PASS')
N=25
one=[F(1)]+[F(0)]*(N-1);zero=[F(0)]*N
def add(a,b):return [x+y for x,y in zip(a,b)]
def scale(c,a):return [c*x for x in a]
def sub(a,b):return add(a,scale(-1,b))
def mul(a,b):return [sum(a[i]*b[n-i] for i in range(n+1)) for n in range(N)]
def D(a):return [n*x for n,x in enumerate(a)]
def sigma(n,k):return sum(d**k for d in range(1,n+1) if n%d==0)
def power(a,k):
    p=one
    for _ in range(k):p=mul(a,p)
    return p
def comp(c,b):
    p=one;out=zero
    for k in range(N):out=add(out,scale(c[k],p));p=mul(b,p)
    return out
rng=Random(369);checks=0
for _ in range(8):
    b=[F(0)]+[F(rng.randrange(-3,4),11) for i in range(N-1)]
    c=[F(rng.randrange(-7,8),13) for i in range(N)]
    inv=comp([F(1)]*N,b)
    assert mul(sub(one,b),inv)==one;checks+=N
    # x D b = y b for x=b,y=D b, including signed and zero terms.
    assert mul(b,D(comp(c,b)))==mul(D(b),comp([k*t for k,t in enumerate(c)],b));checks+=N
    assert comp(c,b)==add(scale(c[0],one),mul(b,comp(c[1:]+[F(0)],b)));checks+=N
print(f'{checks} signed exact inverse, finite chain and shifted-composition coefficients PASS')
X=[F(1)]+[F(240*sigma(n,3)) for n in range(1,N)]
Y=[F(1)]+[F(-504*sigma(n,5)) for n in range(1,N)]
E=[F(1)]+[F(-24*sigma(n,1)) for n in range(1,N)]
assert scale(12,D(E))==sub(mul(E,E),X)
assert scale(3,D(X))==sub(mul(E,X),Y)
assert scale(2,D(Y))==sub(mul(E,Y),mul(X,X))
X3=power(X,3);Y2=power(Y,2);Y3=power(Y,3);Y5=power(Y,5);disc=sub(X3,Y2)
I=comp([F(1)]*N,sub(one,X3));Z=mul(disc,I)
assert mul(X3,I)==one and mul(X3,Z)==disc
assert D(disc)==mul(E,disc) and mul(X,D(Z))==mul(Y,Z)
outer=[F(1)]
for n in range(N-1):outer.append(outer[-1]*F((6*n+1)*(2*n+1)*(6*n+5),72*(n+1)**3))
C=[comp([n**d*t for n,t in enumerate(outer)],Z) for d in range(4)]
for d in range(3):assert mul(X,D(C[d]))==mul(Y,C[d+1])
rhs=add(add(scale(F(3,2),C[2]),scale(F(23,36),C[1])),scale(F(5,72),C[0]))
assert C[3]==mul(Z,add(C[3],rhs));assert mul(Y2,C[3])==mul(disc,rhs)
f=C[0];f1=D(f);f2=D(f1);f3=D(f2)
A=sub(mul(Y,D(X)),mul(X,D(Y)));B=sub(mul(Y,D(A)),scale(2,mul(A,D(Y))))
R2=add(mul(mul(power(X,2),Y),f2),mul(mul(X,A),f1))
R3=add(add(mul(mul(X3,Y2),f3),scale(3,mul(mul(mul(power(X,2),Y),A),f2))),mul(mul(X,add(mul(A,A),mul(X,B))),f1))
assert mul(Y3,C[2])==R2 and mul(Y5,C[3])==R3
assert scale(72,R3)==add(add(scale(108,mul(disc,R2)),scale(46,mul(mul(mul(disc,X),Y2),f1))),scale(5,mul(mul(disc,Y3),f)))
assert mul(f,f)==X
assert scale(6,mul(mul(f,Y),C[1]))==scale(3,mul(X,D(X)))
print(f'{N} original q-degrees, Ramanujan, actual Z inverse/flow, 3 chains, recurrence, denominator jets, square and cleared jet PASS; SymPy {__version__}')

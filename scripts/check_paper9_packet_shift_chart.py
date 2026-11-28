"""Exact independent geometry checks; does not certify analytic modularity."""
from sympy import Matrix, symbols, expand, I, sqrt, simplify, __version__
from fractions import Fraction
p=41
S=Matrix([[0,-1],[1,0]])
T=Matrix([[1,1],[0,1]])
E=Matrix.eye(2)
A=lambda i: Matrix([[p,0],[0,1]]) if i==p else Matrix([[1,i],[0,p]])
s=lambda i: 0 if i==p else p if i==0 else (-pow(i,-1,p))%p
t=lambda i: p if i==p else (i+1)%p
tb=lambda i: p if i==p else (i-1)%p
C=lambda i: S if i in (0,p) else Matrix([[i,(-i*s(i)-1)//p],[p,-s(i)]])
D=lambda i: Matrix([[1,p],[0,1]]) if i==p else T if i==p-1 else E
count=0
for i in range(42):
    assert A(i).det()==p
    assert C(i).det()==D(i).det()==1
    assert A(i)*S==C(i)*A(s(i))
    assert A(i)*T==D(i)*A(t(i))
    assert s(s(i))==i and tb(t(i))==t(tb(i))==i
    count+=8
M=S*A(1); B=Matrix([[-1,-p],[1,0]])
assert M*B==-p*E and B*M==-p*E
assert B==T.inv()*S*A(0)
z=(-1+I*sqrt(163))/2
assert simplify(z*z+z+41)==0
alpha=simplify(41/(z+1)**2); beta=simplify(41/z**2)
assert simplify(alpha*beta-1)==0 and simplify(alpha+beta+Fraction(81,41))==0
u,k,c,a0,a1,a2=symbols('u k c a0 a1 a2')
def step(c,acc):
    if not acc: return [c]
    return [c+k*acc[0]]+step(acc[0],acc[1:])
def horner(cs,x): return sum(a*x**i for i,a in enumerate(cs))
assert expand(horner(step(c,[a0,a1,a2]),u)-c-(k+u)*horner([a0,a1,a2],u))==0
for n in range(1,12):
    cs=symbols(f'c0:{n}'); acc=[]
    for a in cs: acc=step(a,acc)
    assert expand(horner(acc,u)-sum(a*(k+u)**(n-1-i) for i,a in enumerate(cs)))==0
print(f'SymPy {__version__}; {count} exact chart assertions; 6 CM matrix/trace identities; 12 symbolic Horner identities PASS')

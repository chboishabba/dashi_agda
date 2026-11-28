"""Exact relative-field orientation for the explicit CM seed, not a generic cycle proof."""
from itertools import product
import sympy as s

n = 0
def ck(v):
    global n
    if not v:
        raise RuntimeError('relative orientation guard failed')
    n += 1

t = s.symbols('t')
f = t**3+t**2-2*t-1
def red(a):
    return s.rem(s.expand(a), f, t)
def mat(a):
    return s.Matrix(3,3,lambda i,j:s.Poly(red(a*t**j),t).nth(i))
def trace(a):
    return s.trace(mat(a))
basis = [1,t,t*t]
G = s.Matrix(3,3,lambda i,j:trace(basis[i]*basis[j]))
ck(G.det()==49)
dual = [sum(G.inv()[i,j]*basis[j] for j in range(3)) for i in range(3)]
for i,j in product(range(3), repeat=2):
    ck(trace(basis[i]*dual[j])==int(i==j))
ck(red(sum(a*b for a,b in zip(basis,dual)))==1)
# Multiplication by the separability idempotent on F tensor_Q F.
P = sum((s.kronecker_product(mat(a),mat(b)) for a,b in zip(basis,dual)),s.zeros(9))
L = s.kronecker_product(mat(t),s.eye(3)); R=s.kronecker_product(s.eye(3),mat(t))
ck(P*P==P); ck(P.rank()==3); ck((L-R)*P==s.zeros(9)); ck(P*(L-R)==s.zeros(9))
# Relative multiplication and its actual inverse on the projected summand.
m = s.Matrix(3,9,lambda i,j:s.Poly(red(t**(j//3+j%3)),t).nth(i))
J = P[:,[0,3,6]]
ck(m*J==s.eye(3)); ck(J*m==P)
# Literal skew numerator of the previous seed.
pi=2-t; D=s.Integer(130001)
E=s.Matrix([[0,-1,-4,0,4,-6],[1,0,-5,2,-5,-1],[4,5,0,3,-6,2],[0,-2,-3,0,-3,-6],[-4,5,6,3,0,-5],[6,1,-2,6,5,0]])
S=s.zeros(6)
for i,u in enumerate([t,-1,-1]):
    S[2*i,2*i+1]=-(i+1)*u*pi
    S[2*i+1,2*i]=-S[2*i,2*i+1]
S=D*S+E

def pf(M):
    if not M.rows:return s.Integer(1)
    return red(sum((-1)**(j+1)*M[0,j]*pf(M.extract([i for i in range(1,M.rows) if i!=j],[i for i in range(1,M.rows) if i!=j])) for j in range(1,M.rows)))
p=pf(S)
ck(S.T==-S); ck(p!=0); ck(int(p.subs(t,7))%13!=0)
ck(red(S.det(method='domain-ge')-p*p)==0)
# Triple wedge of the actual alternating form has coefficient 6 pf(S)/D^3.
v=red(6*p/D**3)
M=mat(v)
ck(M.det()!=0)
ck(M.T*G==G*M)
ck((M.T*G*M).det()==49*M.det()**2)
ck(M.rank()==3)
print(f'{n}/{n} exact relative orientation guards PASS')
print('trace Gram',G.tolist(),'dual',dual)
print('scaled Pfaffian',p,'mod13',int(p.subs(t,7))%13)

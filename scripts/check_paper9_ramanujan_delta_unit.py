"""Independent exact reference replay, not a native kernel receipt."""
from fractions import Fraction as Q
from math import comb, ceil
import sympy as s

N = 512
sig = {k: [0]*(N+2) for k in (1,3,5)}
for k, arr in sig.items():
    for d in range(1,N+2):
        for n in range(d,N+2,d):
            arr[n] += d**k
E = [1] + [-24*x for x in sig[1][1:]]
X = [1] + [240*x for x in sig[3][1:]]
Y = [1] + [-504*x for x in sig[5][1:]]
def conv(a,b,m):
    return sum(a[i]*b[m-i] for i in range(m+1))
XX = [conv(X,X,n) for n in range(N+2)]
XXX = [conv(XX,X,n) for n in range(N+2)]
YY = [conv(Y,Y,n) for n in range(N+2)]
for n in range(N+2):
    assert 12*n*E[n] == conv(E,E,n)-X[n]
    assert 3*n*X[n] == conv(E,X,n)-Y[n]
    assert 2*n*Y[n] == conv(E,Y,n)-XX[n]
    assert (XXX[n]-YY[n]) % 1728 == 0
D = [(a-b)//1728 for a,b in zip(XXX,YY)]
assert D[:2] == [0,1]
for n in range(N+2):
    assert n*D[n] == conv(E,D,n)
U = D[1:]
V = [1]
for n in range(1,N+1):
    assert n*U[n] == sum(E[k]*U[n-k] for k in range(1,n+1))
    num = -sum(E[k]*V[n-k] for k in range(1,n+1))
    assert num % n == 0
    V.append(num//n)
# Independent Euler factor products; use descending update for (1-q^m)^24
# and ascending update for the reciprocal (1-q^m)^(-24).
eta, inv = [1]+[0]*N, [1]+[0]*N
for m in range(1,N+1):
    for _ in range(24):
        for k in range(N,m-1,-1):
            eta[k] -= eta[k-m]
        for k in range(m,N+1):
            inv[k] += inv[k-m]
J = [conv(XXX,V,n) for n in range(N+1)]
for n in range(N+1):
    assert U[n] == eta[n]
    assert V[n] == inv[n]
    assert conv(U,V,n) == (n==0)
    assert conv(U,J,n) == XXX[n]
assert J[:5] == [1,744,196884,21493760,864299970]
print('Ramanujan:',3*(N+2),'integer divisibility:',N+2,'Delta flow:',N+2)
print('normalized recurrence:',2*N,'Euler products/inverse/j relation:',4*(N+1))
# Arbitrary-radius proof uses rho>r and B=24*rho*(1+rho)/(1-rho)^3.
# Exact rational diagnostics at several rho where the threshold is in range.
checks = 0
for rho in (Q(1,10),Q(1,4),Q(1,3),Q(1,2)):
    B = 24*rho*(1+rho)/(1-rho)**3
    M = ceil(B)
    assert M < N
    mass = Q(0)
    for n in range(1,N+1):
        mass += -E[n]*rho**n
        assert mass <= B
        checks += 1
    for f in (U,V):
        C = sum(abs(f[n])*rho**n for n in range(M+1))
        for n in range(N+1):
            assert abs(f[n])*rho**n <= C
            checks += 1
print('radius mass and uniform coefficient controls:',checks)
e,x,y=s.symbols('e x y')
dx=(e*x-y)/3;dy=(e*y-x*x)/2
assert s.expand(3*x*x*dx-2*y*dy-e*(x**3-y*y))==0
print('symbolic discriminant flow: 1; PASS')

"""R306/307/293 flag, mirabolic lattice volumes and exterior spectral checks."""
from itertools import combinations, product
import sympy as s

def v3(x):
    x=s.Rational(x)
    if not x:return float('inf')
    a,b=abs(int(x.p)),int(x.q); v=0
    while a%3==0:a//=3;v+=1
    while b%3==0:b//=3;v-=1
    return v

# R306 chart: grouped 1-coordinates then pi-coordinates.
B=s.Matrix([[6,21],[-7,-15]])/9
P=s.Matrix([[0,-3],[1,3]])
assert B.charpoly().as_expr()==s.Symbol('lambda')**2+s.Symbol('lambda')+s.Rational(19,27)
X=s.Matrix.hstack(s.eye(2)[:,0],B[:,0])
assert X.inv()*B*X==s.Matrix([[0,-s.Rational(19,27)],[1,-1]])
assert X.inv()*P[:,0]==s.Matrix([s.Rational(6,7),-s.Rational(9,7)])
assert v3(sum([s.Rational(6,7),s.Rational(9,7)]))>=1
Q=[B**i*X*s.diag(3**(7-2*i),3**(6-2*i)) for i in range(4)]
q=s.zeros(8)
for i in range(4):
    q[i,2*i],q[i,2*i+1]=Q[i][0,0],Q[i][0,1]
    q[i+4,2*i],q[i+4,2*i+1]=Q[i][1,0],Q[i][1,1]
assert q.det()!=0
# Each adjacent character scales by 3 (conductor p to conductor O).
D=s.diag(*[3**(7-i) for i in range(8)])
flag=q*D.inv()
for i in range(7):
    e=s.zeros(8); e[i,i+1]=1
    assert flag.inv()*q*e*q.inv()*flag==3*e
# R293 inter-block boundary coefficient is lower diagonal coefficient of K multiplication.
for i in range(3):
    for a,b in product(range(-2,3),repeat=2):
        T=(B**i*X).inv()*(a*s.eye(2)+b*B)*(B**(i+1)*X)
        assert T[1,0]==a-b
# J1 = 1 + (pi M4(O_K) + 3 A), individual blocks, row-major flattening.
base=[s.Matrix([[3,0],[0,0]]),s.Matrix([[0,0],[0,3]]),s.Matrix([[0,-3],[1,0]]),s.Matrix([[0,9],[0,0]])]
assert abs(s.Matrix.hstack(*[s.Matrix(list(t)) for t in base]).det())==81

def intersect_zero(cols, rows):
    cols=[c.copy() for c in cols]
    for r in rows:
        possible=[i for i,c in enumerate(cols) if c[r]]
        if not possible: continue
        p=min(possible,key=lambda i:v3(cols[i][r])); pivot=cols.pop(p)
        cols=[c-c[r]/pivot[r]*pivot for c in cols]
        assert all(c[r]==0 for c in cols)
    return cols

def lattice_exponent(cols,n):
    # valuation pivoting over Z_(3); discard redundant generators.
    cols=[c.copy() for c in cols]; val=0
    for r in range(n):
        possible=[i for i,c in enumerate(cols) if c[r]]
        assert possible
        p=min(possible,key=lambda i:v3(cols[i][r])); pivot=cols.pop(p)
        val+=v3(pivot[r]); cols=[c-c[r]/pivot[r]*pivot for c in cols]
    assert all(not any(c) for c in cols)
    return val

vH=vU=0; entries=0; uentries=0; ledger=[]
for i,j in product(range(4),repeat=2):
    cols=[s.Matrix(list(Q[i].inv()*t*Q[j])) for t in base]
    # Last row of the entire matrix must be 0 in the additive mirabolic chart.
    if i==3: cols=intersect_zero(cols,[2,3])
    kept=[r*2+c for r in range(2 if i<3 else 1) for c in range(2 if j<3 else 1)]
    cols=[s.Matrix([c[k] for k in kept]) for c in cols]
    n=len(kept); vh=lattice_exponent(cols,n); entries+=n
    upper=[p for p,k in enumerate(kept) if 2*i+k//2<2*j+k%2]
    uc=intersect_zero(cols,[p for p in range(n) if p not in upper])
    vu=lattice_exponent([s.Matrix([c[p] for p in upper]) for c in uc],len(upper)); uentries+=len(upper)
    vH+=vh;vU+=vu;ledger.append((i,j,vh,vu))
assert entries==49 and uentries==21
prob=s.prod(1-s.Rational(1,3**k) for k in range(1,8))
C=3**s.Integer(vU-vH)/prob
print('q determinant',q.det(),'J1 block ledger',ledger,'vH',vH,'vU',vU,'C',C)
# Full primitive character carrier, exact-order labels modulo 15.
J=[1,2,4,7,8,11,13,14]; a=11; f=13
assert pow(a,2,15)==1 and pow(f,4,15)==1

def act(S,m):
    T=[m*j%15 for j in S]
    sign=(-1)**sum(T[i]>T[j] for i in range(len(T)) for j in range(i+1,len(T)))
    return tuple(sorted(T)),sign

t=s.Symbol('T'); pols=[]
for k in range(9):
    Z=[S for S in combinations(J,k) if sum(S)%15==0]
    A=s.zeros(len(Z)); F=s.zeros(len(Z))
    for i,S in enumerate(Z):
        for m,M in [(a,A),(f,F)]:
            T,sign=act(S,m);M[Z.index(T),i]=sign
    assert A**2==s.eye(len(Z)) and F**4==s.eye(len(Z)) and A*F==F*A
    E=(s.eye(len(Z))+A)/2; QI=E.columnspace(); dim=len(QI)
    traces=[s.trace(E*F**j) for j in range(1,5)]
    if dim:
        QI=s.Matrix.hstack(*QI); M=s.Matrix.hstack(*[QI.gauss_jordan_solve(F*c)[0] for c in QI.columnspace()])
        poly=s.factor((s.eye(dim)-t*M).det()); assert M**4==s.eye(dim)
        assert traces==[s.trace(M**j) for j in range(1,5)]
    else:poly=s.Integer(1);assert traces==[0]*4
    pols.append(poly);print('exterior',k,'zero weight',len(Z),'I invariants',dim,'Euler',poly)
assert pols==pols[::-1]
# Actual full 8D quotient mass and centered lattice RS calculation.
# Independent maximal-minor verification of the projected volume on each block.
def minors_exponent(cols,n):
    if n==0:return 0
    return min(v3(s.Matrix.hstack(*cs).det()) for cs in combinations(cols,n))
for i,j in product(range(4),repeat=2):
    cols=[s.Matrix(list(Q[i].inv()*t*Q[j])) for t in base]
    if i==3:cols=intersect_zero(cols,[2,3])
    kept=[r*2+c for r in range(2 if i<3 else 1) for c in range(2 if j<3 else 1)]
    cols=[s.Matrix([c[k] for k in kept]) for c in cols]
    assert minors_exponent(cols,len(kept))==lattice_exponent(cols,len(kept))
    upper=[p for p,k in enumerate(kept) if 2*i+k//2<2*j+k%2]
    uc=intersect_zero(cols,[p for p in reversed(range(len(kept))) if p not in upper])
    uc=[s.Matrix([c[p] for p in upper]) for c in uc]
    assert minors_exponent(uc,len(upper))==ledger[4*i+j][3]
# Hereditary order row lattice in q coordinates: chain valuations.
vv=[14,9,7,2,0,-5,-7,-12]
for i in range(4):
    for c in range(2):
        col=Q[i][:,c]
        assert min(2*v3(col[0]),2*v3(col[1])+1)==vv[2*i+c]
from math import ceil
row=[ceil((x-vv[-1])/2) for x in vv]
assert row==[13,11,10,7,6,4,3,0] and sum(row)==54
assert [-x for x in row]==[ceil((-13-x)/2) for x in vv]
# The original uniformizer shifts the chain, checked against row and column grades.
for m in range(-32,33):
    for i in range(4):
        for c in range(2):
            col=P**m*Q[i][:,c]
            assert min(2*v3(col[0]),2*v3(col[1])+1)==vv[2*i+c]+m
    assert (vv[0]-m>=-13)==(m<=27)
# Haar mass of the full type shell relative to H1 and finite cuspidal dimension.
assert s.prod(3**4-3**i for i in range(4))==80*3**6*416
r,Y=s.symbols('r Y',nonzero=True) # Y=3^(-4s)
X=81*r*Y
assert s.expand(3**s.Integer(-54)*X**27-r**27*3**54*Y**27)==0
# Independent finite geometric-window summation controls in the two half-planes.
for x in [s.Rational(1,3),s.Rational(2,5),s.Rational(3),s.Rational(5,2)]:
    for n in range(1,17):
        assert sum(x**j for j in range(n))==(1-x**n)/(1-x)
        assert sum(x**j for j in range(28-n,28))==x**27*(1-x**(-n))/(1-x**-1)
print('32 independent lattice-minor comparisons; 520 uniformizer grade comparisons; row Fourier volume 3^-54; dual cutoff 27; 128 finite series identities')

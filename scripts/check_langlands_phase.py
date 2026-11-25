"""R346-R349: original cyclic support covector and Eisenstein phase bound."""
import sympy as s
from itertools import product, combinations
from math import prod

def v3(x):
    x=s.Rational(x)
    if not x:return 10**6
    a,b=abs(int(x.p)),int(x.q);v=0
    while a%3==0:a//=3;v+=1
    while b%3==0:b//=3;v-=1
    return v

def res(x,m=3):
    x=s.Rational(x);return int(x.p)*pow(int(x.q),-1,m)%m

B=s.Matrix([[6,21],[-7,-15]])/9;P=s.Matrix([[0,-3],[1,3]])
beta=s.diag(B,B,B,B);X=s.Matrix.hstack(s.eye(2)[:,0],B[:,0])
Q=[B**i*X*s.diag(3**(7-2*i),3**(6-2*i)) for i in range(4)];q=s.diag(*Q)
T=beta/3
for i in range(3):T[2*i+2:2*i+4,2*i:2*i+2]=s.eye(2)/3
b=s.Matrix.hstack(*[T**i*s.eye(8)[:,0] for i in range(8)]);bi=b.inv()
assert v3(b.det())==-54 and v3(q.det())==2
m=-(v3(b.det())-v3(q.det()))//4;assert m==14
R=q.inv()*s.diag(*[P**m]*4);r=R[7,:];c=bi[7,:]
assert min(map(v3,R))==0 and min(map(v3,b))==-18
assert all(r[i]==0 for i in range(6)) and (v3(r[6]),v3(r[7]))==(13,16)
assert [20+min(map(v3,bi[:,j])) for j in range(8)]==[20,21,20,19,18,20,17,16]
assert [res(c[j]/r[6]) for j in range(0,8,2)]==[0,0,0,1]
# Every contribution u=R j b k has e8 u=e8, e8 k^-1=e8 mod 3^20.
# Thus last row of Cbar is e4 in GL4(F3), by the previous exact covector bounds.
# The diagonal unit transport preserves J, and has scalar type action 1.
z=s.symbols('z'); a=1+3*z; phase=0
for i in range(4):
    E=Q[i]*s.diag(1,0)*Q[i].inv()
    assert all(v3(E[k,l])>=int(k==0 and l==1) for k,l in product(range(2),repeat=2))
    assert s.trace(B*E)==0 and s.trace(B*(s.eye(2)-E))==-1
    phase-=(a**(6-2*i)-1)/3
assert all(int(x)%3==0 for x in s.Poly(s.expand(phase),z).all_coeffs())
# Independently compute R327 pairing volumes in actual q coordinates.
def eliminate_zero(cols,rows):
    for r in rows:
        p=min(range(len(cols)),key=lambda i:v3(cols[i][r])) if cols else None
        if p is None or not cols[p][r]:continue
        c=cols.pop(p);cols=[x-c*x[r]/c[r] for x in cols]
    return cols

def vol(cols,n):
    if not n:return 0
    return min(v3(s.Matrix.hstack(*cs).det()) for cs in combinations(cols,n))
base=[s.Matrix([[3,0],[0,0]]),s.Matrix([[0,0],[0,3]]),s.Matrix([[0,-3],[1,0]]),s.Matrix([[0,9],[0,0]])]
vH=vU=0
for i,j in product(range(4),repeat=2):
    cols=[s.Matrix(list(Q[i].inv()*x*Q[j])) for x in base]
    if i==3:cols=eliminate_zero(cols,[3,2])
    kept=[2*k+l for k in range(2 if i<3 else 1) for l in range(2 if j<3 else 1)]
    cols=[s.Matrix([x[k] for k in kept]) for x in cols]
    vH+=vol(cols,len(kept))
    up=[p for p,k in enumerate(kept) if 2*i+k//2<2*j+k%2]
    uc=eliminate_zero(cols,[p for p in reversed(range(len(kept))) if p not in up])
    vU+=vol([s.Matrix([x[p] for p in up]) for x in uc],len(up))
assert (vH,vU)==(49,-77)
p7=s.prod(1-s.Rational(1,3**i) for i in range(1,8))
assert 3**222*p7*(s.Integer(3)**(vU-vH)/p7)==3**96
# Exact norm arithmetic in Z[zeta3], prime 1-zeta3 has norm 3.
# (A+B*zeta)/(1-zeta) = ((2A-B)+(A+B)*zeta)/3.
for A,B in product(range(-12,13),repeat=2):
    assert ((A*A-A*B+B*B)%3==0)==((A+B)%3==0)
    if (A+B)%3==0:
        C,D=(2*A-B)//3,(A+B)//3
        assert C*C-C*D+D*D==(A*A-A*B+B*B)//3
units={(A,B) for A,B in product(range(-2,3),repeat=2) if A*A-A*B+B*B==1}
assert units=={(1,0),(-1,0),(0,1),(0,-1),(1,1),(-1,-1)}
# Normalized newvector-specific translated-row test function.
p8=p7*(1-s.Rational(1,3**8)); mass=s.Integer(3)**(-160)/(1-s.Rational(1,3**8))
assert mass==s.Rational(1,3**(8*20)-3**(8*19))
print('m=14; additive denominator <=3^18; last residue row e4; diagonal phase zero; 32 lattice-minor volumes; Eisenstein norm controls 625; six units; K1 mass',mass)

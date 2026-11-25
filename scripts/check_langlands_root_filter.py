"""R351-R353: original unipotent witness and seven-ratio phase filter."""
from itertools import product
import sympy as s

def v3(x):
    x=s.Rational(x)
    if not x:return 10**6
    a,b=abs(int(x.p)),int(x.q);v=0
    while a%3==0:a//=3;v+=1
    while b%3==0:b//=3;v-=1
    return v

def res(x,m=3):
    x=s.Rational(x);return int(x.p)*pow(int(x.q),-1,m)%m

B=s.Matrix([[6,21],[-7,-15]])/9
P=s.Matrix([[0,-3],[1,3]])
X=s.Matrix.hstack(s.eye(2)[:,0],B[:,0])
Q=[B**i*X*s.diag(3**(7-2*i),3**(6-2*i)) for i in range(4)]
q=s.diag(*Q);beta=s.diag(*[B]*4)
T=beta/3
for i in range(3):T[2*i+2:2*i+4,2*i:2*i+2]=s.eye(2)/3
b=s.Matrix.hstack(*[T**i*s.eye(8)[:,0] for i in range(8)])
R=q.inv()*s.diag(*[P**14]*4)
u=s.Matrix([
[1,4,"4994/243","3661/729","418366/59049","4029958/177147","115597610/14348907","129140108/4782969"],
[0,1,"56/3","4130/243","8735/729","178552/59049","632990/59049","287189225/14348907"],
[0,0,1,"26/3","6559/243","16459/729","310582/19683","33164/2187"],
[0,0,0,1,"70/3","4912/243","3965/243","338203/19683"],
[0,0,0,0,1,"14/3","320/81","16483/729"],
[0,0,0,0,0,1,"71/3","797/81"],
[0,0,0,0,0,0,1,0],
[0,0,0,0,0,0,0,1]])
j=R.inv()*u*b.inv()
assert R*j*b==u and v3(j.det())==0
assert all(v3(x)>=0 for x in j)
for a,c in product(range(4),repeat=2):
    assert v3(j[2*a,2*c]-j[2*a+1,2*c+1])>=1
    assert v3(j[2*a,2*c+1]+3*j[2*a+1,2*c])>=2
C=s.Matrix(4,4,lambda a,c:res(j[2*a,2*c]))
assert C==s.Matrix([[2,0,2,2],[0,1,0,0],[0,0,2,2],[0,0,0,1]])
assert sum(u[i,i+1] for i in range(7))==83
m=[i//2 for i in range(1,8)]
assert [v3(3*u[i,i+1]+s.Rational(m[i],3)) for i in range(7)]==[1,-1,-1,-1,-1,2,0]
# The actual block projectors lie in A and give the diagonal scalar character.
for Q_i in Q:
    E=Q_i*s.diag(1,0)*Q_i.inv()
    assert all(v3(E[a,c])>=int(a==0 and c==1) for a,c in product(range(2),repeat=2))
    assert s.trace(B*E)==0 and s.trace(B*(s.eye(2)-E))==-1
for z in product(range(3),repeat=7):
    a=[1]*8
    for i in reversed(range(7)):a[i]=(1+3*z[i])*a[i+1]%9
    assert (-sum((a[i]-1)//3 for i in [1,3,5,7])+sum(m_i*z_i for m_i,z_i in zip(m,z)))%3==0
# Exact finite Fourier filters; residues root=r/27 modulo 1/3.
x=s.Symbol("x");phi=s.cyclotomic_poly(9,x)
for m_i in m:
    for r in range(9):
        c=(r+3*m_i)%9
        S=sum(x**((-c*z)%9) for z in range(9))
        assert s.rem(S,phi,x)==(9 if c==0 else 0)
assert sum(m)==12
for z in product(range(3),repeat=7):
    roots=[-s.Rational(m_i,9)+s.Rational(z_i,3) for m_i,z_i in zip(m,z)]
    assert 3*sum(roots)==sum(z)-4
print("R351 original unipotent lift; 2187 diagonal residues; 63 exact Fourier filters; 2187 signed root reconstructions PASS")

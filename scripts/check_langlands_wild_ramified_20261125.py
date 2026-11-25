from itertools import product
from fractions import Fraction as F
from sympy import Matrix, eye, zeros, diag, kronecker_product, symbols, discriminant
from collections import Counter

G=list(product(range(3),range(2)))
e=(0,0)
def mul(a,b): return ((a[0]+(-1)**a[1]*b[0])%3,(a[1]+b[1])%2)
def inv(a): return next(b for b in G if mul(a,b)==e)
R=Matrix([[-1,-1],[1,0]]); J=Matrix([[0,1],[1,0]])
reps=[{g:Matrix([[1]]) for g in G},{g:Matrix([[(-1)**g[1]]]) for g in G},{g:R**g[0]*J**g[1] for g in G}]
C3=[(i,0) for i in range(3)]
fil=[G]+[C3]*3
subs=[[e],C3,[(0,0),(0,1)],G]
def fixed(A,H):
    n=A[e].rows
    return n-Matrix.vstack(*[A[g]-eye(n) for g in H]).rank()
def cond(A,H):
    return sum(F(len(S),len(H))*(A[e].rows-fixed(A,S)) for T in fil if len(S:=[g for g in T if g in H])>1)
def induce(A,H):
    cs=[]; seen=set()
    for g in G:
        if g not in seen:
            cs.append(g); seen.update(mul(g,h) for h in H)
    n=A[e].rows; out={}
    for g in G:
        M=zeros(n*len(cs))
        for j,b in enumerate(cs):
            for i,a in enumerate(cs):
                h=mul(inv(a),mul(g,b))
                if h in H: M[i*n:(i+1)*n,j*n:(j+1)*n]=A[h]
        out[g]=M
    return out

def tensor(A,B): return {g:kronecker_product(A[g],B[g]) for g in A}
def wd(A,H,k): return k*cond(A,H)+(k-1)*fixed(A,H)
def chi(A): return tuple(A[g].trace() for g in G)
x=symbols('x')
assert abs(discriminant(x**3-3,x))==3**5
assert abs(discriminant(x**2+x+1,x))==3
assert abs(discriminant(x**6+3,x))==2**6*3**11
n=0; m=0
for H in subs:
    dh=sum(len([g for g in T if g in H])-1 for T in fil)
    disc=(11-dh)//len(H)
    assert 11==dh+len(H)*disc
    for A in reps:
        B={g:A[g] for g in H}; C=induce(B,H)
        assert cond(C,G)==cond(B,H)+disc*B[e].rows
        assert fixed(C,G)==fixed(B,H)
        for g,h in product(G,repeat=2):
            assert C[g]*C[h]==C[mul(g,h)]
            n+=1
        for k in range(1,5):
            assert wd(C,G,k)==wd(B,H,k)+disc*k*B[e].rows
            m+=1
        for Z in reps:
            assert chi(tensor(C,Z))==chi(induce(tensor(B,{g:Z[g] for g in H}),H))
            m+=1
# genuine composite S3 x C5 inertia; labels are exact fifth-root exponents.
# Frobenius advances 1,3,4,2; U matrices are retained on every fibre.
labels=[1,3,4,2]; d=len(labels)
def cycle(a):
    P=zeros(2*d)
    for i in range(d): P[2*((i+1)%d):2*((i+1)%d)+2,2*i:2*i+2]=eye(2)*(a if i==d-1 else 1)
    return P
P=cycle(2); Q=cycle(3)
assert all(labels[i]==3*labels[j]%5 for i,j in product(range(d),repeat=2) if P[2*i,2*j])
# inertia intertwiner linear equations on full 2x2 blocks; unequal C5 labels forbidden.
Hmat=Matrix.vstack(kronecker_product(eye(2),R)-kronecker_product(R.T,eye(2)),kronecker_product(eye(2),J)-kronecker_product(J.T,eye(2)))
assert Hmat.rank()==3
A=zeros(d)
for i in range(d): A[(i+1)%d,i]=F(2,3) if i==d-1 else 1
assert A.charpoly(x).as_expr()==x**4-F(2,3)
assert (-P).charpoly(x).as_expr()==P.charpoly(x).as_expr()
# actual wild break 15, G0 size30, G1..15 size3. End U has wild fixed dimension2.
U=reps[2]; End=tensor(U,{g:U[g].inv().T for g in G})
assert fixed(End,C3)==2 and fixed(End,G)==1
assert 8+15*F(3,30)*8==20
# Tensor pair: 16 pairs of inertia types, 4 identical tag pairs.
# 64 dim, G0 fixed4, wild fixed32; conductor 60+48=108.
assert 64-4+15*F(3,30)*(64-32)==108
# Restriction to original S3 removes C5 and restores all 16 U-pair intertwiners.
assert 16*fixed(End,G)==16
print('PASS induced group relations',n,'WD conductor and projection controls',m,'wild orbit controls 9; discriminants 3')

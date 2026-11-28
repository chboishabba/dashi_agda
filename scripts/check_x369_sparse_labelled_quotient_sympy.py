import sympy as s
from itertools import product

E=4
I=s.eye(3)
tags=[s.zeros(3,1)]+[I[:,j] for j in range(3)]
R=s.Matrix([[0,1,0],[0,0,1],[1,0,0]])
a,b=s.symbols('a b', positive=True)
rows=[]
for j in range(1,4):
    x=R.T*tags[j]
    assert sum(x)==1
    scores=[(2 if e==0 else 0)+(R*x).dot(tags[e]) for e in range(E)]
    assert sorted(range(E),key=lambda e:scores[e],reverse=True)[:2]==[0,j]
    assert scores[0]==2 and scores[j]==1 and all(scores[e]==0 for e in range(1,E) if e!=j)
    row=s.zeros(1,E);row[0]=a;row[j]=b;rows.append(row)
C=s.Matrix.vstack(*rows)
assert C.rank()==3
assert C*s.Matrix([b,-a,-a,-a])==s.zeros(3,1)
D=s.diag(0,1,1,1)
M=s.Matrix.vstack(C[0,:],C[0,:]*D,C[1,:]*D,C[2,:]*D)
assert s.factor(M.det())==a*b**3
assert M.rank()==4
assert s.simplify(M.inv()*M)==s.eye(4)
for v in product(range(2),repeat=4):
    assert s.simplify(M.inv()*(M*s.Matrix(v)))==s.Matrix(v)
print('X369_SPARSE_QUOTIENT_PASS: 3 strict probes; static rank 3; recurrent rank 4; 16 exact inverse cases; determinant', M.det())

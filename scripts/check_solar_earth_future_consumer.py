"""Exact abstract future-work quotient; not a geospace plant or control design."""
import sympy as s
# Same rational history A as check_solar_earth_endpoint_weld.py.
A=s.Matrix([[1,1,0,0],[0,1,1,0],[0,0,1,0],[0,0,0,1]])
B=s.diag(1,-1,1,1)
O=s.Matrix([[1,0,0,0]])
Q=O.T*O
# Symmetric real covariance coordinate carrier, with all cross terms retained.
ix=[(i,j) for i in range(4) for j in range(i,4)]
def row(q):return s.Matrix([[q[i,j]*(1 if i==j else 2) for i,j in ix]])
def closure(maps):
    basis=[Q]; ranks=[1]
    while True:
        new=list(basis); rank=len(new)
        for a in maps:
            for h in basis:
                g=a.T*h*a
                if s.Matrix.vstack(*(row(x) for x in new+[g])).rank()>rank:
                    new.append(g);rank+=1
        if len(new)==len(basis):break
        basis=new;ranks.append(rank)
    R=s.Matrix.vstack(*(row(h) for h in basis)); transforms=[]
    for a in maps:
        P=s.Matrix.vstack(*(row(a.T*h*a) for h in basis));D=P*R.pinv()
        assert D*R==P;transforms.append(D)
    return R,ranks,transforms
R,ranks,_=closure([A]); T,tranks,D=closure([A,B]);print('ranks',ranks,tranks)
assert R.rank()==5 and T.rank()==6
# Equal present output, different future quadratic work.
x=s.Matrix([0,1,0,0]);y=s.zeros(4,1)
assert O*x==O*y and (O*A*x)[0]**2!=(O*A*y)[0]**2
# Same sufficient reduced covariance, different hidden fourth coordinate.
C=s.diag(1,2,3,4);E=s.diag(1,2,3,9)
vec=lambda c:s.Matrix([c[i,j] for i,j in ix])
assert T*vec(C)==T*vec(E)
for a,d in zip([A,B],D):
    assert T*vec(a*C*a.T)==d*T*vec(C)
    assert T*vec(a*E*a.T)==d*T*vec(E)
# Backward adjoint error telescope, same input transitions; abstract residual.
maps=[A,B,A];xs=[s.Matrix([1,2,3,4])];ys=[s.Matrix([1,1,3,4])]
for k,a in enumerate(maps):
    xs.append(a*xs[-1]);ys.append(a*ys[-1]+s.eye(4)[:,k])
zs=[None]*4;zs[-1]=O.T
for k in range(2,-1,-1):zs[k]=maps[k].T*zs[k+1]
res=[maps[k]*ys[k]-ys[k+1] for k in range(3)]
assert (O*(xs[-1]-ys[-1]))[0]==(zs[0].T*(xs[0]-ys[0]))[0]+sum((zs[k+1].T*res[k])[0] for k in range(3))
print('exact covariance closure, hidden-state witness, future separation and adjoint telescope PASS; SymPy',s.__version__)

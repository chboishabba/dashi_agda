"""Integer image membership via SymPy Smith multipliers, independently replayed.
Backend coefficient growth/time not metered; admission is a size guard only.
"""
from sympy import Matrix, eye, zeros, ZZ
from sympy.matrices.normalforms import smith_normal_decomp


def matrix(A,n):
    if n<0 or any(len(row)!=n or any(type(x)!=int for x in row) for row in A):raise ValueError('matrix')
    return Matrix(len(A),n,[x for row in A for x in row])


def verify(A,b,n,R):
    M=matrix(A,n);m=len(A);B=Matrix(m,1,b)
    D,U,V,Ui,Vi=(R[k] for k in ('D','U','V','Ui','Vi'))
    if any(x.is_Integer is not True for X in (D,U,V,Ui,Vi) for x in X):return False
    if D.shape!=(m,n) or U.shape!=Ui.shape or U.shape!=(m,m) or V.shape!=Vi.shape or V.shape!=(n,n):return False
    if U*Ui!=eye(m) or Ui*U!=eye(m) or V*Vi!=eye(n) or Vi*V!=eye(n) or U*M*V!=D:return False
    if any(D[i,j] for i in range(m) for j in range(n) if i!=j):return False
    ds=[D[i,i] for i in range(min(m,n))];nz=[d for d in ds if d]
    if ds[:len(nz)]!=nz or any(d<=0 for d in nz) or any(b%a for a,b in zip(nz,nz[1:])):return False
    if R['status']=='EMPTY':
        y=R['covector'];return y.shape==(1,m) and all(v.is_Rational is True for v in y) and all(v.is_Integer for v in y*M) and (y*B)[0].is_Integer is False
    if R['status']!='INTEGER':return False
    x,K=R['particular'],R['kernel'];r=len(nz)
    return x.shape==(n,1) and all(v.is_Integer for v in x) and M*x==B and K==V[:,r:] and M*K==zeros(m,n-r)


def solve(A,b,n,max_entries=4096,max_bits=256):
    if len(A)!=len(b) or any(type(t)!=int for t in b):raise ValueError('target')
    m=len(A)
    if n<0 or any(len(row)!=n or any(type(x)!=int for x in row) for row in A):raise ValueError('matrix')
    if m*m+n*n+m*n>max_entries or max((abs(v).bit_length() for v in b),default=0)>max_bits or any(abs(v).bit_length()>max_bits for row in A for v in row):return dict(status='UNKNOWN')
    M=matrix(A,n);B=Matrix(m,1,b)
    if m*n:D,U,V=smith_normal_decomp(M,domain=ZZ)
    else:D,U,V=zeros(m,n),eye(m),eye(n)
    for i in range(min(m,n)):
        if D[i,i]<0:D.row_op(i,lambda v,j:-v);U.row_op(i,lambda v,j:-v)
    R=dict(D=D,U=U,V=V,Ui=U.inv(),Vi=V.inv());c=U*B;r=sum(D[i,i]!=0 for i in range(min(m,n)));z=zeros(n,1)
    for i in range(m):
        d=D[i,i] if i<r else 0
        if (d and c[i]%d) or (not d and c[i]):
            R.update(status='EMPTY',covector=U[i,:]/(d if d else abs(c[i])+1));break
        if d:z[i]=c[i]//d
    else:R.update(status='INTEGER',particular=V*z,kernel=V[:,r:])
    assert verify(A,b,n,R);return R


def main():
    from random import Random
    from sympy.matrices.normalforms import hermite_normal_form
    rng=Random(3693401);C={}
    for m in range(5):
        for n in range(5):
            for _ in range(16):
                A=tuple(tuple(rng.randrange(-5,6) for j in range(n)) for i in range(m));b=tuple(rng.randrange(-8,9) for i in range(m));R=solve(A,b,n)
                M=matrix(A,n);B=Matrix(m,1,b)
                # Independent column-lattice membership by canonical HNF.
                assert (R['status']=='INTEGER')==(hermite_normal_form(M)==hermite_normal_form(M.row_join(B)))
                C[R['status']]=C.get(R['status'],0)+1
                if R['status']=='INTEGER':
                    K=R['kernel'];t=Matrix(K.cols,1,[rng.randrange(-8,9) for j in range(K.cols)]);x=R['particular']+K*t
                    z=R['Vi']*x;assert R['V']*z==x and M*x==B
    for d in (11,49,2**80,3**40*5):
        R=solve(((d,),),(1,),1);assert R['status']=='EMPTY';assert not verify(((d,),),(1,),1,dict(R,covector=zeros(1,1)))
    assert solve(((1,),),(1,),1,max_entries=0)['status']=='UNKNOWN'
    print(C,'large torsion 4, tamper and refusal PASS')
if __name__=='__main__':main()

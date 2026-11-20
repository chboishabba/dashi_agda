"""Open Cartesian ternary reference complex, not a physical Maxwell mesh."""
from itertools import product, combinations
import sympy as s


def cells(d,k):
    for axes in combinations(range(d),k):
        for p in product(*(range(2 if j in axes else 3) for j in range(d))):
            yield p,axes


def boundary(d,k):
    low=list(cells(d,k-1)); high=list(cells(d,k))
    ix={c:i for i,c in enumerate(low)}
    B=s.MutableSparseMatrix(len(low),len(high),{})
    for col,(p,axes) in enumerate(high):
        for j,a in enumerate(axes):
            rest=axes[:j]+axes[j+1:]
            q=list(p); q[a]+=1
            B[ix[(tuple(q),rest)],col]=(-1)**j
            B[ix[(p,rest)],col]=-(-1)**j
    return B


def run():
    count=0
    D=s.Matrix([[-1,0],[1,-1],[0,1]])
    for d,expected in [(1,[3,2]),(2,[9,12,4]),(3,[27,54,36,8])]:
        assert [len(list(cells(d,k))) for k in range(d+1)]==expected; count+=1
        B=boundary(d,1)
        blocks=[s.kronecker_product(*(D if j==a else s.eye(3) for j in range(d))) for a in range(d)]
        assert B==s.Matrix.hstack(*blocks); count+=1
        assert s.ones(1,B.rows)*B==s.zeros(1,B.cols); count+=1
        for k in range(2,d+1):
            assert boundary(d,k-1)*boundary(d,k)==s.zeros(expected[k-2],expected[k]); count+=1
        E=s.Matrix(range(1,B.rows+1)); H=s.Matrix(range(1,B.cols+1))
        assert (E.T*B*H-H.T*B.T*E)[0]==0; count+=1
        assert B.rank()==B.rows-1; count+=1
        print(f'{d}D: {expected}, rank {B.rank()}')
    print(f'{count}/{count} PASS; SymPy {s.__version__}')


if __name__=='__main__':
    run()

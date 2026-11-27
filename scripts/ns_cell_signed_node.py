"""Alpoge--Buckmaster cell-layer finite real-node producer (DASHI extension).
Source: ad53419de079eb8f95f60313473374624a348546, StatementDefs.lean.
Conditional on actual assembled form and admissible constraint rows; not a profile.
Uses exact SymPy rational LDL, no numerical positive-definiteness oracle.
"""
from math import isqrt
from itertools import product
import unittest
import sympy as S


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def rational_matrix(A):
    A = S.Matrix(A)
    require(all(x.is_Rational for x in A), 'exact rational entries required')
    return A


def positive_ldl(A):
    if not A.rows:
        return S.zeros(0), S.zeros(0)
    require(A == A.T, 'symmetric form required')
    try:
        L, D = A.LDLdecomposition(hermitian=False)
    except (ValueError, ZeroDivisionError):
        raise ValueError('LDL failed') from None
    require(all(x.is_Rational for x in L) and all(D[i,i].is_Rational and D[i,i] > 0 for i in range(A.rows)), 'nonpositive or singular form')
    require(L*D*L.T == A, 'LDL reconstruction')
    return L, D


def row_abs(A):
    return [sum(abs(A[i,j]) for j in range(A.cols)) for i in range(A.rows)]


def source_label(m, pair):
    a,b = pair
    require(type(m) is int and m >= 3 and type(a) is int and type(b) is int, 'source lattice')
    return 2*b-a, m*a


def source_inverse(m, harmonic):
    t,n = harmonic
    require(type(m) is int and m >= 3 and type(t) is int and type(n) is int, 'source lattice')
    require(n % m == 0 and (t+n//m)%2 == 0, 'outside original lattice')
    return n//m, (t+n//m)//2


def source_flip(pair):
    a,b = pair
    return -a,b-a


def produce(M,C,free_count,E=None):
    """One real root: all coordinates pivot, base/front=0, F=0, weight=1.
    C rows must be allowed negatives on the actual original constraint kernel.
    E symmetric entrywise nonnegative bounds input discrepancies.
    Require positivity on ker C AFTER charging E's row diagonal.
    """
    M,C = rational_matrix(M),rational_matrix(C)
    n=M.rows
    require(n>0 and M==M.T and C.cols==n,'shape or symmetry')
    require(type(free_count) is int and 0<=free_count<=n and C.rows<=free_count,'negative column cap')
    require(C.rank()==C.rows,'independent constraint rows required')
    E=S.zeros(n) if E is None else rational_matrix(E)
    require(E.shape==M.shape and E==E.T and all(x>=0 for x in E),'invalid error matrix')
    charge=row_abs(E); A=M-S.diag(*charge)
    Z=S.Matrix.hstack(*C.nullspace()) if C.nullspace() else S.zeros(n,0)
    H=Z.T*A*Z
    positive_ldl(H)
    if C.rows:
        Y=C.T*(C*C.T).inv()
        J=Z.T*A*Y
        Schur=Y.T*A*Y-(J.T*H.inv()*J if H.rows else S.zeros(C.rows))
        # Integer scale keeps the negative columns rational.
        s=isqrt(int(S.ceiling(max(row_abs(Schur)))))+1
    else:
        s=1
    Fm=s*C.T
    G=A+Fm*Fm.T
    positive_ldl(G)
    delta=1/(2*S.trace(G.inv()))
    L,D=positive_ldl(G-delta*S.eye(n))
    # Directed dyadic square root; charge actual residual entrywise.
    # An explicit sufficient precision from ||L||_infty,||L^T||_infty.
    K=2*max([S.Integer(1)]+[D[i,i] for i in range(n)])*max(row_abs(L))*max(row_abs(L.T))
    bits=max(1,int(S.ceiling(K/delta)).bit_length()+1)
    scale=2**bits
    roots=[S.Rational(isqrt(int(D[i,i]*scale**2)),scale) for i in range(n)]
    Fp=L*S.diag(*roots)
    piv=S.diag(*[delta+x for x in charge])
    rem=M-piv-Fp*Fp.T+Fm*Fm.T
    radius=[a+b for a,b in zip(row_abs(rem),charge)]
    slack=[piv[i,i]-radius[i] for i in range(n)]
    require(all(x>0 for x in slack),'insufficient strict slack')
    out={'input':M,'E':E,'F':S.zeros(n),'base':S.zeros(n),'front':S.zeros(n),'pivots':tuple(range(n)),
         'weight':[S.Integer(1)]*n,'pivotValue':[piv[i,i] for i in range(n)],'posColumns':Fp,
         'negColumns':Fm,'radius':radius,'slack':slack,'free_count':free_count}
    verify(out,C)
    return out


def verify(d,C):
    M=d['input'];n=M.rows;E=d['E'];F=d['F'];Fp=d['posColumns'];Fm=d['negColumns']
    require(M==M.T and d['base']==d['front']==F==S.zeros(n),'root form')
    require(E==E.T and all(x>=0 for x in E),'error symmetry')
    require(d['pivots']==tuple(range(n)) and d['weight']==[1]*n,'pivot or weights')
    require(Fm.cols<=d['free_count'],'column cap')
    for z in C.nullspace():
        require(Fm.T*z==S.zeros(Fm.cols,1),'column ownership')
    R=M-S.diag(*d['pivotValue'])-Fp*Fp.T+Fm*Fm.T
    require(all(a+b<=r for a,b,r in zip(row_abs(R),row_abs(E),d['radius'])),'row bound')
    require(all(0<s<=p-r for s,p,r in zip(d['slack'],d['pivotValue'],d['radius'])),'pivot slack')


class Tests(unittest.TestCase):
    def test_lattice(self):
        for m in range(3,10):
            for a,b in product(range(-8,9),repeat=2):
                i=(a,b);t,n=source_label(m,i)
                self.assertEqual(source_inverse(m,(t,n)),i)
                self.assertEqual(source_label(m,source_flip(i)),(t,-n))
                self.assertEqual(source_flip(source_flip(i)),i)
                self.assertEqual(source_label(m,(-a,-b)),(-t,-n))
                for j in [(0,0),(1,-2),(-3,4)]:
                    self.assertEqual(source_label(m,(a+j[0],b+j[1])),tuple(x+y for x,y in zip((t,n),source_label(m,j))))
            with self.assertRaises(ValueError):source_inverse(m,(1,0))
            with self.assertRaises(ValueError):source_inverse(m,(0,1))
    def test_real_root(self):
        for n in range(2,8):
            for k in range(n+1):
                P=S.eye(n)
                for i in range(n-1):P[i,i+1]=S.Rational(i+1,3)
                M=P.T*S.diag(*([-2]*k+[3]*(n-k)))*P
                C=P[:k,:]
                d=produce(M,C,k,S.ones(n)/100000)
                self.assertEqual(d['negColumns'].cols,k)
                self.assertGreater(min(d['slack']),0)
    def test_fail_closed(self):
        M=S.diag(-1,2)
        for C,b,E in [(S.Matrix([[0,1]]),1,None),(S.Matrix([[1,0]]),0,None),(S.Matrix([[1,0]]),1,S.eye(2)*3),(S.Matrix([[1,0],[1,0]]),2,None)]:
            with self.assertRaises(ValueError):produce(M,C,b,E)
        d=produce(M,S.Matrix([[1,0]]),1)
        d['slack'][0]=0
        with self.assertRaises(ValueError):verify(d,S.Matrix([[1,0]]))

if __name__=='__main__':unittest.main()

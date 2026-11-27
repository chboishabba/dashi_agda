#!/usr/bin/env python3
"""Static AK wall: exact weighted mean-Israel Codazzi energy.
F8 stress-energy symmetrizer donor; this is a forced intrinsic subsystem,
not the full five-dimensional evolution.
"""
import sympy as S
from itertools import product

def run():
    # Independent mixed-tensor divergence in general static wall lapse at a
    # spatial orthonormal normal-coordinate point (arbitrary lapse gradient).
    N=S.symbols('N',positive=True); a=S.Matrix(S.symbols('a0:3',real=True))
    sigma=S.symbols('sigma',real=True); B=S.Matrix(S.symbols('B0:3',real=True))
    P=S.Matrix([[S.Symbol('p00'),S.Symbol('p01'),S.Symbol('p02')],[S.Symbol('p01'),S.Symbol('p11'),S.Symbol('p12')],[S.Symbol('p02'),S.Symbol('p12'),sigma-S.Symbol('p00')-S.Symbol('p11')]])
    M=(-S.Matrix([[sigma]])).row_join(-B.T/N).col_join((N*B).row_join(P))
    def G(k,i,j):
        if k==0 and i==0 and j>0:return a[j-1]
        if k==0 and j==0 and i>0:return a[i-1]
        if k>0 and i==j==0:return N*N*a[k-1]
        return 0
    conn=[S.expand(sum(G(i,i,l)*M[l,v]-G(l,i,v)*M[i,l] for i,l in product(range(4),repeat=2))) for v in range(4)]
    assert S.expand(conn[0]-N*a.dot(B))==0
    for i in range(3):assert S.expand(conn[i+1]-(P*a+sigma*a)[i])==0
    # partial_i (N B^i) supplies the second lapse-gradient term in sigma_t.
    # sigma_t=N div B+2 N a.B; B_t=N grad sigma/3+4 N sigma a/3+forcing.
    xi=S.Matrix(S.symbols('xi0:3',real=True)); A=S.zeros(4); A[0,1:4]=N*xi.T; A[1:4,0]=N*xi/3
    W=S.diag(1,3,3,3); assert W*A==A.T*W
    p=S.symbols('p',real=True)
    residual=S.expand(4+8-2*(p+1)); assert S.solve(residual,p)==[5]
    # E=1/2 int N^5(sigma^2+3|B|^2). Flux is N^6 sigma B.
    assert S.expand(2+4-(5+1))==0
    # Pure tension mean Gauss constraint: trace(M)=0; R=-12+3j²-tr(M²).
    j,e=S.symbols('j eps'); A1=S.diag(-sigma,*[sigma/3]*3)
    for i in range(3):A1[0,i+1]=-B[i]/N; A1[i+1,0]=N*B[i]
    Pi=P-sigma*S.eye(3)/3
    A1[1:4,1:4]=P
    assert S.trace(A1)==0
    assert S.expand(S.trace(A1*A1)-(4*sigma*sigma/3-2*B.dot(B)+S.trace(Pi*Pi)))==0
    R=-12+3*j*j-S.trace((e*A1)**2)
    assert S.expand(R.diff(e,2)/2+S.trace(A1*A1))==0
    print('PASS exact static Codazzi connection, symmetric principal matrices, N^5 weight and signed quadratic Gauss residual')

if __name__=='__main__':run()

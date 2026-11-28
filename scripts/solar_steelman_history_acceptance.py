"""Exact section geometry, independent of floating orthogonal leaf bases.
The finite section norm is max(current ambient infinity, history knots,
compatible ratio endpoint). Certificate inputs must be independently paid.
"""
import sympy as S
from solar_steelman_history_smoothing import contraction

def inf(M):
    return max((sum(abs(v) for v in M.row(i)) for i in range(M.rows)),default=S.Integer(0))

def leaf(m,a):
    n=len(a['models']);b0=m['d']['M'].rows;b1=b0+m['d']['N'].rows
    nc=b1+m['H'].rows+32;d=nc+5*n+4
    C=m['d']['C'];U=S.Matrix.hstack(*C.columnspace())
    I=S.eye(d);cols=[I[:,j] for j in list(range(b0))+list(range(b1,nc))]
    for j in range(U.cols):
        v=S.zeros(d,1);v[b0:b1,0]=U[:,j];cols.append(v)
    for j in range(n):cols.append(I[:,nc+j]+I[:,nc+n+j])
    for k,tail in ((3,d-4),(4,d-3)):
        for j in range(n):cols.append(2*I[:,nc+k*n+j]-I[:,tail])
    cols.append(I[:,d-2])
    Q=S.Matrix.hstack(*cols)
    # Rational left inverse from independent rows, not a numerical SVD.
    rows=list(Q.T.rref()[1]);L=S.zeros(Q.cols,d)
    inv=Q[rows,:].inv()
    for j,r in enumerate(rows):L[:,r]=inv[:,j]
    assert L*Q==S.eye(Q.cols)
    return Q,L

def section(Q,L,n,knots,R0):
    d,k=Q.shape;h=n*knots
    U=S.diag(Q,S.eye(h));V=S.diag(L,S.eye(h))
    # J maps leaf coordinates to the full norm readback including endpoint.
    J=U.col_join((R0*Q).row_join(S.zeros(n,h)))
    assert V*U==S.eye(k+h)
    return U,V,J

def finite_bound(M,U,V,J,endpoint_error=0,p=1):
    """Exact induced-norm upper bounds on projected finite approximation.
    ||z||_leaf=||Jz||inf, so ||z||inf<=||V||inf ||Jz||inf.
    R0 endpoint polynomial approximation uncertainty charged separately.
    """
    assert p>=1 and M.rows==M.cols==U.rows
    assert all(v.is_Rational for X in (M,U,V,J) for v in X)
    A=V*M*U
    # Norm of a projected return power, conservative left-inverse factor.
    e=S.Rational(endpoint_error);assert e>=0
    def bound(P):
        return (inf(J*P)+e*inf(U*P))*inf(V)
    return dict(A=A,norm=bound(A),power=bound(A**p),projection=inf(U*V))

def projected_error(U,V,r,state_error,history_error,clock_state=0,clock_history=0):
    # Exact leaf preservation is a prerequisite: P T=U V P T.
    # Project only the numerical error, not the actual exact return.
    r,state_error,history_error,clock_state,clock_history=map(S.Rational,(r,state_error,history_error,clock_state,clock_history))
    assert min(r,state_error,history_error,clock_state,clock_history)>=0
    state=inf(U*V)*(state_error+clock_state)
    return max(state,r*state,history_error+clock_history)

def accept(bounds,p):
    required={'section_power','section_norm','return_norm','output_error','step_error'}
    if set(bounds)!=required:raise ValueError('incomplete or unexpected bound fields')
    return contraction(p=p,**bounds)

def fixture():
    Q=S.Matrix([[1],[1]]);L=S.Matrix([[1,0]])
    U,V,J=section(Q,L,1,1,S.Matrix([[1,0]]))
    z=finite_bound(S.eye(3)/2,U,V,J,p=2)
    assert z['norm']==S.Rational(1,2) and z['power']==S.Rational(1,4)
    assert accept(dict(section_power=S.Rational(1,4),section_norm=S.Rational(1,2),return_norm=1,output_error=0,step_error=0),2)['contracting']
    print('PASS exact rational section norm fixture')
if __name__=='__main__':fixture()

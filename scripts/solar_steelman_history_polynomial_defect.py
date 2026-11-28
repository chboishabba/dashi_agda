"""Exact polynomial defect certificate on a normalized time slab.
Coefficients are rational approximants with independently certified uniform
errors; no floating integrator tolerance is interpreted as an enclosure.
"""
import sympy as S
from solar_steelman_history_residual import step

def exact(M):
    M=S.Matrix(M)
    if any(x.has(S.Float) for x in M):raise TypeError("rational coefficients required")
    return M

def bernstein_bound(M,s):
    M=exact(M);rows=[]
    for row in M.tolist():
        total=0
        for v in row:
            p=S.Poly(v,s,domain=S.QQ)
            n=max(0,int(p.degree())) if not p.is_zero else 0
            coeff=[sum(p.nth(j)*S.binomial(k,j)/S.binomial(n,j) for j in range(k+1)) for k in range(n+1)]
            total+=max(map(abs,coeff))
        rows.append(total)
    return max(rows,default=S.Integer(0))

def defect(s,h,X,A,B,C,H1,H2,errors):
    """Matrix columns represent all input directions, induced infinity norm.
    All polynomials use the same normalized slab variable s in [0,1].
    H1,H2 are delayed ratio approximants, not full state history.
    errors=(A,B,C,H1,H2) absolute induced norm coefficient/readback bounds.
    H1,H2 errors here are approximation errors relative to the represented
    approximate trajectory, not propagation error of the exact solution.
    """
    X,A,B,C,H1,H2=map(exact,(X,A,B,C,H1,H2))
    h=S.Rational(h);assert h>0
    ea,eb,ec,eh1,eh2=map(S.Rational,errors)
    assert min(ea,eb,ec,eh1,eh2)>=0
    norm=lambda M:bernstein_bound(M,s)
    D=X.diff(s)/h-A*X-B*H1-C*H2
    return norm(D)+ea*norm(X)+eb*norm(H1)+ec*norm(H2)+(norm(B)+eb)*eh1+(norm(C)+ec)*eh2

def logarithmic_norm(A,s,error=0):
    A=exact(A);assert A.rows==A.cols
    # Signed diagonal maximum, absolute off-diagonal Bernstein bounds.
    def upper(v):
        p=S.Poly(v,s,domain=S.QQ)
        n=max(0,int(p.degree())) if not p.is_zero else 0
        return max(sum(p.nth(j)*S.binomial(k,j)/S.binomial(n,j) for j in range(k+1)) for k in range(n+1))
    return max(upper(A[i,i])+sum(bernstein_bound(S.Matrix([[A[i,j]]]),s) for j in range(A.cols) if j!=i) for i in range(A.rows))+S.Rational(error)

def fixture():
    s=S.symbols("s");X=S.Matrix([[1-s]]);A=S.Matrix([[-1]]);Z=S.zeros(1)
    assert defect(s,1,X,A,Z,Z,Z,Z,[0]*5)==1
    assert logarithmic_norm(A,s)==-1
    assert bernstein_bound(S.Matrix([[s*(1-s)]]),s)==S.Rational(1,2)
    assert defect(s,1,X,A,Z,Z,Z,Z,[S.Rational(1,10),0,0,0,0])==S.Rational(11,10)
    print("PASS polynomial defect fixtures")
if __name__=="__main__":fixture()

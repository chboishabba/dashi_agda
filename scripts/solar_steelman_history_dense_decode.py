"""Read exact rational polynomials from exported binary64 dense coefficients.
No implicit claim that the represented trajectory solves the physical RHS.
"""
import numpy as np
import sympy as S
from solar_steelman_history_polynomial_defect import bernstein_bound

def q(x):
    if not np.isfinite(x):raise ValueError("nonfinite coefficient")
    a,b=float(x).as_integer_ratio();return S.Rational(a,b)

def polynomial(y0,F,s,d,k):
    if len(y0)!=d*k or F.shape!=(7,d*k):raise ValueError("unexpected DOP853 shape")
    M=S.zeros(d,k)
    for i,f in enumerate(F[::-1]):
        M=(M+S.Matrix(d,k,[q(x) for x in f]))*(s if i%2==0 else 1-s)
    return (M+S.Matrix(d,k,[q(x) for x in y0])).applyfunc(S.expand)

def read(path):
    with np.load(path,allow_pickle=False) as f:
        d,n,start,stop=map(lambda x:int(f[x]),("d","n","start","stop"))
        times,y0,F=f["times"],f["y0"],f["F"]
        assert len(times)==len(y0)==len(F)
        s=S.symbols("s");last=None;cursor=S.Integer(0)
        for t,y,v in zip(times,y0,F):
            lo,hi=map(q,t);assert lo==cursor and hi>lo
            X=polynomial(y,v,s,d,stop-start)
            jump=S.Integer(0) if last is None else bernstein_bound(X.subs(s,0)-last,s)
            yield lo,hi,X,jump
            last=X.subs(s,1);cursor=hi

def fixture():
    s=S.symbols('s');F=np.zeros((7,1));F[0]=2;F[1]=3
    X=polynomial(np.array([1.]),F,s,1,1)
    assert X[0]==1+5*s-3*s*s
    print("PASS exact dense polynomial decode fixture")
if __name__=="__main__":fixture()

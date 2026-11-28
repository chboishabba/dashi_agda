"""Original F8 characteristic R/L -> full GN PDE and normal hierarchy.
Algebraic exact equivalence of first-order characteristic and second-order
wave, with explicit off-shell defects and a differentiated normal energy.
"""
import sympy as s
from check_f8_normal_graph_hierarchy import normal_commutator

def exact():
    t,n,k=s.symbols('t n k',positive=True)
    a=s.sinh(s.asinh(t)-n);c=s.cosh(s.asinh(t)-n);N=c/s.sqrt(1+t*t)
    Nt=s.diff(N,t);Nn=s.diff(N,n)
    A=a**3/N;B=N*a**3;C=N*a*k*k
    H,W,V=[s.Function(x)(t,n) for x in ('H','W','V')]
    ht=N*W;hn=V
    Wt=N*s.diff(V,n)+(Nn-3*N*c/a)*V-3*N/a*W-N*k*k/a**2*H
    # F= -At Ht - A Htt+Bn Hn+B Hnn - C H
    Htt=Nt*W+N*Wt
    F=-s.diff(A,t)*ht-A*Htt+s.diff(B,n)*V+B*s.diff(V,n)-C*H
    assert s.simplify(s.expand(F))==0
    # Off-shell residuals: first-order scalar equations plus integrability.
    U,G,D=s.symbols('U G D')
    # W_t=Wt+U; H_t=NW+G; H_n=V+D, and
    # V_n=H_nn-D_n. Then L H = -A N U plus G,D terms.
    Gn,Dn=s.symbols('Gn Dn')
    # For an algebraic first-order defect, H_tt=NtW+NWt+G_t.
    Gt=s.symbols('Gt')
    Foff=-s.diff(A,t)*(ht+G)-A*(Htt+N*U+Gt)+s.diff(B,n)*(V+D)+B*(s.diff(V,n)+Dn)-C*H
    assert s.simplify(Foff-(-s.diff(A,t)*G-A*N*U-A*Gt+s.diff(B,n)*D+B*Dn))==0
    # Differentiated normal m receives nonzero commutator even if F=0.
    norm=normal_commutator(H,A,B,C,t,n,1)
    assert norm.has(s.diff(H,t,1))
    assert norm.has(s.diff(H,n,2))
    # Physical boundary prescribed V(t,0)=-6 Pi. This does NOT fix V_n.
    pi=s.Function('Pi')(t)
    v1=n*s.Function('c1')(t)-6*pi
    v2=n*s.Function('c2')(t)-6*pi
    assert s.simplify((v1-v2).subs(n,0))==0
    assert s.diff(v1-v2,n).subs(n,0)!=0
    print('PASS exact original characteristic-> GN PDE, offshell defect ledger, and independent normal trace')

if __name__=='__main__':exact()

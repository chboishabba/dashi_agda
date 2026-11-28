"""F8 normal Sobolev graph energy identities m=0..4.
Uses exact original differential operator and source commutator hierarchy;
no physical boundary dissipation or solution-jet bounds are inferred.
"""
import sympy as s
from check_f8_normal_graph_hierarchy import wave,normal_commutator


def energy_balance(u,A,B,C,t,n,m):
    v=s.diff(u,n,m)
    vt=s.diff(v,t);vn=s.diff(v,n)
    E=(A*vt**2+B*vn**2+C*v**2)/2
    flux=B*vt*vn
    F=s.diff(wave(u,A,B,C,t,n),n,m)+normal_commutator(u,A,B,C,t,n,m)
    work=(s.diff(A,t)*vt**2-s.diff(B,t)*vn**2-s.diff(C,t)*v**2)/2
    return s.expand(s.diff(E,t)-s.diff(flux,n)+F*vt+work),E,flux,F


def exact():
    t,n,k=s.symbols('t n k',positive=True)
    # Fully variable manufactured polynomial metric, with all normal and
    # time commutators nonzero; independent of exact F8 special identities.
    AA=2+t+n+t*n;BB=3+2*t+3*n+t*n;CC=k*k*(1+t+n*n)
    u=1+2*t+3*n+4*t*n+5*t*t*n*n+7*n**7+11*t*n**6
    for m in range(5):
        residual,E,J,F=energy_balance(u,AA,BB,CC,t,n,m)
        assert residual==0,(m,residual)
        assert s.expand(F-wave(s.diff(u,n,m),AA,BB,CC,t,n))==0
        assert s.expand(J-BB*s.diff(u,n,m,t)*s.diff(u,n,m+1))==0
    # Original F8 at wall has B=t³; flux keeps the higher normal trace.
    a=s.sinh(s.asinh(t)-n);N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    B=N*a**3
    assert s.simplify(B.subs(n,0)-t**3)==0
    H=s.Function('H')(t,n)
    for m in range(5):
        J=s.diff(H,n,m,t)*s.diff(H,n,m+1)*B
        assert s.simplify(J.subs(n,0)-t**3*s.diff(H,n,m,t).subs(n,0)*s.diff(H,n,m+1).subs(n,0))==0
    # The original Neumann H_n=-6Pi does not determine m>=1 wall flux.
    p=s.Function('P')(t)
    U1=-6*p*n;U2=-6*p*n+s.Function('G')(t)*n*n
    assert s.simplify(s.diff(U1,n).subs(n,0)-s.diff(U2,n).subs(n,0))==0
    assert s.simplify(s.diff(U2,n,2).subs(n,0)-2*s.Function('G')(t))==0
    print('PASS five original-form normal differentiated energy balances and independent signed boundary fluxes')
    print('Normal graph regularity remains conditional on higher source/initial/wall compatibility')

if __name__=='__main__':exact()

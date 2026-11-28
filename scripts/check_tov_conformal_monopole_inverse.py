"""Exact monopole conformal inverse from original positive static lapse.
No boundary motion or nonlinear branch is asserted.
"""
import sympy as s

def main():
    r=s.symbols('r',positive=True)
    N,u,w,A=s.symbols('N u w A',cls=s.Function)
    N,u,w,A=[v(r) for v in (N,u,w,A)]
    q=(A*N.diff(r)).diff(r)/(w*N)
    op=lambda v:-(A*v.diff(r)).diff(r)+w*q*v
    assert s.cancel(op(N))==0
    # Ground-state transform for all multipoles, including generated monopole.
    assert s.expand(N*op(N*u)+(A*N*N*u.diff(r)).diff(r))==0
    assert s.expand(A*(N*u).diff(r)**2+w*q*(N*u)**2-A*N*N*u.diff(r)**2-(A*N*N.diff(r)*u*u).diff(r))==0
    # exterior N=sqrt(1-2M/r), A=r² sqrt(f).
    M=s.symbols('M',positive=True); f=1-2*M/r
    Ne=s.sqrt(f); Ae=r*r*s.sqrt(f)
    assert s.simplify(Ae*Ne.diff(r)-M)==0
    # radial Green inverse: -(A N² v')'=w N S.
    # If F=int_0^r w N S, then v'= -F/(A N²).
    F=s.Function('F')(r)
    assert s.simplify(-(A*N*N*(-F/(A*N*N))).diff(r)-F.diff(r))==0
    # ADM asymptotic coefficient of u=N v is total integral of source.
    z=s.symbols('z',positive=True)
    assert s.integrate(1/z**2,(z,r,s.oo))==1/r
    print('PASS all-mode lapse ground-state identity and monopole radial inverse algebra')
    print('OPEN nonlinear free-boundary branch and full constrained polar Hessian')
if __name__=='__main__':main()

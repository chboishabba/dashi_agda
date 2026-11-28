#!/usr/bin/env python3
"""BR40e: variable-chart transport of BR29's REAL 35D zero-speed projector.

An exact conjugated-projector model with the original G-symmetric projector,
not a claim that its chosen chart generator equals the physical connection.
Run with --part small first; --part physical consumes BR29 carrier() and
may require a separate <=90s checkpoint. No GitHub CI required.
"""
import argparse
import sympy as s

def check(P0,G):
    n=P0.rows; E=s.eye(n); Q0=E-P0
    assert P0*P0==P0
    assert G*P0==P0.T*G
    # Use a rank-one NILPOTENT coordinate change mixing the existing
    # zero-speed fibre with its original active complement.
    ia=next(i for i in range(n) if P0[:,i]!=s.zeros(n,1))
    iz=next(i for i in range(n) if Q0[i,:]!=s.zeros(1,n))
    u=P0[:,ia]; v=Q0[iz,:]
    K=u*v
    assert K*K==s.zeros(n) and P0*K==K and K*P0==s.zeros(n)
    t=s.symbols('t',real=True)
    S=E+t*K; Si=E-t*K
    P=S*P0*Si; assert P==P0-t*K
    Pdot=-K; Om=K
    assert S*Si==E
    assert P*P==P
    assert Om*P-P*Om==Pdot
    Gt=Si.T*G*Si
    assert Gt*P==P.T*Gt
    # Actual BR29 positive G is transported; it is NOT held constant
    # while the chart projector is moving.
    z=Q0[:,iz]
    D=S*z
    assert P*D==s.zeros(n,1)
    assert D.diff(t)-Om*D==s.zeros(n,1)
    # For any source f with P f = 0, the covariant derivative of
    # the projected residual remains homogeneous.
    f=Q0[:,iz]
    assert P0*f==s.zeros(n,1)
    assert P*(S*f)==s.zeros(n,1)
    # Exact moving projector connection identity on an INDEPENDENT jet,
    # not only on a constrained residual that has already been set to zero.
    u0=Q0[:,iz]+P0[:,ia]
    u1=P0[:,ia]-Q0[:,iz]
    u=S*(u0+t*u1)
    nabla=lambda v:v.diff(t)-Om*v
    assert (nabla(P*u)-P*nabla(u)).applyfunc(s.expand)==s.zeros(n,1)
    assert (nabla(P*u)-S*P0*u1).applyfunc(s.expand)==s.zeros(n,1)
    # The exact *source* needed for preservation is P0*u1=0. This
    # deliberately fails for the independent unconstrained u1 above.
    assert P0*u1!=s.zeros(n,1)
    print('PASS variable projector rank',P0.rank(),'ambient',n,
          'nilpotent signed chart, covariant transport and positive-gram congruence')

def main():
    a=argparse.ArgumentParser();a.add_argument('--part',choices=['small','physical'],required=True)
    args=a.parse_args()
    if args.part=='small':
        check(s.diag(0,1),s.diag(3,5))
    else:
        from check_hopf369_br_curvature_energy import carrier
        C,V,X,G,Y,H,J,A,B,R,W,m=carrier()
        An=A[3]; P0=s.eye(35)-An*(5*An-4*An**3)
        assert P0.rank()==9 and P0*An==s.zeros(35)
        check(P0,G)

if __name__=='__main__':main()

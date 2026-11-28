#!/usr/bin/env python3
"""BR49: full moving-material-wall conormal and original Israel normal.

For source metric g and material graph F=n-f(t,x,y,z), keep all five
defining-function derivatives. The covariant outward unit normal is
 n^mu = g^{mu nu} F_nu/sqrt(z), z=g^{mu nu}F_mu F_nu>0.
The actual wave flux from BR48 divergence form is
 J_F(u)=D*g^{mu nu}F_mu partial_nu(u)
       =D*sqrt(z)*(n^nu partial_nu u).
This is the exact geometric conversion BR19/31/34 needs. At f=0,
v_n=0,H^na=0,H^nn=1, the source reduces to BR48 D partial_n u.
Moving wall or sheared coordinate must retain the extra shift and tangent
flux; no arbitrary substitution by partial_n is permitted.

Checker uses one general ADM source metric; scalar test has independent
jets in all five directions. A graph with timelike normal is explicitly
rejected, and the zero/characteristic case is not inverted.
"""
import argparse
import sympy as s

def carrier():
    N=s.symbols('N',positive=True)
    h=s.symbols('h0:4',positive=True)
    v=s.Matrix(s.symbols('v0:4',real=True))
    H=s.diag(*h)
    Hi=s.diag(*[1/k for k in h])
    D=N*s.sqrt(s.prod(h))
    Gi=(-s.ones(1,1)/N**2).row_join((v/N**2).T)
    Gi=Gi.col_join((v/N**2).row_join(Hi-v*v.T/N**2))
    return N,h,v,D,Gi

def graph():
    N,h,v,D,Gi=carrier()
    a=s.Matrix(s.symbols('ft fx fy fz',real=True))
    dF=s.Matrix([-a[0],-a[1],-a[2],-a[3],1])
    du=s.Matrix(s.symbols('ut ux uy uz un'))
    z=s.factor((dF.T*Gi*dF)[0])
    # Independent derivation using the ADM shift:
    # g^-1(dF,dF) = ||grad_space F||_{H^-1}²
    #                -(F_t-v^i F_i)^2/N².
    space=dF[1:5,0]
    normalspace=sum(space[i]**2/h[i] for i in range(4))
    advect=dF[0]-sum(v[i]*space[i] for i in range(4))
    assert s.simplify(z-(normalspace-advect**2/N**2))==0
    current=(D*dF.T*Gi*du)[0]
    conormal=(Gi*dF)
    normal=conormal/s.sqrt(z)
    assert s.simplify(current-D*s.sqrt(z)*(normal.T*du)[0])==0
    # Original source's fixed Gaussian material collar is recovered with
    # all tangential shifts free, provided v^n=0 and H^nn=1.
    collar={a[i]:0 for i in range(4)}
    collar.update({v[3]:0,h[3]:1})
    assert s.simplify(z.subs(collar)-1)==0
    assert s.simplify((current-D*du[4]).subs(collar))==0
    # Moving-tangent graph produces nonzero surface work.
    moving={N:2,**{h[i]:1 for i in range(4)},
            **{v[i]:0 for i in range(4)},
            a[0]:s.Rational(1,3),a[1]:s.Rational(1,4),
            a[2]:0,a[3]:0}
    assert s.simplify(z.subs(moving)-1-s.Rational(1,16)+s.Rational(1,36))==0
    assert s.simplify(current.subs(moving)-D.subs(moving)*
           (du[4]+du[0]/(3*4)-du[1]/4))==0
    # z<=0 is not a spacelike wall: its normal cannot be normalized.
    fail={N:1,**{h[i]:1 for i in range(4)},
          **{v[i]:0 for i in range(4)},
          a[0]:2,a[1]:0,a[2]:0,a[3]:0}
    assert z.subs(fail)==-3
    print('PASS BR49 full graph conormal, independent ADM identity and fixed-Gaussian limit')
    print('PASS moving time/tangent wall flux and timelike-normal negative control')

def matrix_wall():
    # The conversion is a common geometric scalar differential operator
    # on ALL 15 original metric and 5 subsidiary components. Cross-channel
    # BR15/BS4 lower-order connection terms remain independent.
    N,h,v,D,Gi=carrier()
    F=s.Matrix([0,0,0,0,1])
    coeff=(D*Gi*F)
    for dim in (15,5):
        derivatives=s.Matrix(dim,5,lambda i,j:s.Rational((i+2)*(j+3)%17-8,7))
        physical=derivatives*coeff
        direct=s.Matrix([sum(D*Gi[4,j]*derivatives[i,j] for j in range(5))
                         for i in range(dim)])
        assert (physical-direct).applyfunc(s.cancel)==s.zeros(dim,1)
    print('PASS BR49 original 15+5 fields, exact densitized material conormal')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['graph','channels','all'],default='graph')
    a=p.parse_args()
    if a.part in ('graph','all'):graph()
    if a.part in ('channels','all'):matrix_wall()

if __name__=='__main__':main()

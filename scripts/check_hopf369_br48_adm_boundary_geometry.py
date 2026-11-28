#!/usr/bin/env python3
"""BR48: actual ADM metric -> BR4 densitized wave and material wall flux.

This is an independent source-geometry bridge, NOT a scalar stand-in for
BR14/15 tensor first-order connections. Uses the original 4 spatial axes
(x,y,z,n), lapse N, four-vector ADM shift v and positive spatial H.

  g_tt=-N²+v^T H v, g_ti=(H v)_i, g_ij=H_ij
  D=N sqrt(det H), A=D/N², B^i=D v^i/N²,
  C^ij=D(H^{-1,ij}-v^i v^j/N²).
Then L=∂_μ(D g^{μν} ∂_ν) is precisely BR45's divergence operator.

Crucial: H>0,N>0 do NOT imply C>0 for arbitrarily large shift.
The invariant positive spatial Schur complement is C+B B^T/A = D H^-1.
BR4's positive-C symmetrizer requires |v|_H<N (sub-luminal shift
relative to normal slices). Do NOT silently identify the two conditions.

For a material Gaussian wall with v^n=0, H^{-1,na}=0 (a=x,y,z),
H^{-1,nn}=1, the coordinate normal conormal is exactly
   B^n u_t + C^{nj}u_j = D ∂_n u.
This is the explicit missing BR4 energy-flux -> BR34 Israel normal row
bridge. On a sheared/moving wall the other terms remain and must be paid
by BR19/31 material graph transport.

All checks are exact rational/SymPy and separate per --part.
No native kernel, continuum tame estimate, or nonlinear evolution asserted.
"""
import argparse
import sympy as s

def core():
    N=s.symbols('N', positive=True)
    h=s.symbols('h0:4', positive=True)
    v=s.Matrix(s.symbols('v0:4', real=True))
    H=s.diag(*h)
    Hi=s.diag(*[1/x for x in h])
    D=N*s.sqrt(s.prod(h))
    g=(-N*N+(v.T*H*v)[0])
    cov=s.Matrix([[g,*list((H*v))]])
    cov=cov.col_join((H*v).row_join(H))
    inverse=(-1/N**2)*s.ones(1,1)
    inverse=inverse.row_join((v/N**2).T)
    inverse=inverse.col_join((v/N**2).row_join(Hi-v*v.T/N**2))
    assert (cov*inverse-s.eye(5)).applyfunc(s.cancel)==s.zeros(5)
    assert s.simplify(cov.det()+N*N*s.prod(h))==0
    A=D/N**2
    B=D*v/N**2
    C=D*(Hi-v*v.T/N**2)
    dens=(-s.Matrix([[A]])).row_join(B.T).col_join(B.row_join(C))
    assert (dens-D*inverse).applyfunc(s.cancel)==s.zeros(5)
    assert (C+B*B.T/A-D*Hi).applyfunc(s.cancel)==s.zeros(4)
    return N,h,v,D,A,B,C

def conforming_wall():
    N,h,v,D,A,B,C=core()
    # Strong collar v_n=0,h_n=1. Tangential H is arbitrary positive.
    collar={v[3]:0,h[3]:1}
    assert s.simplify(B[3].subs(collar))==0
    for j in range(3):
        assert s.simplify(C[3,j].subs(collar))==0
    assert s.simplify((C[3,3]-D).subs(collar))==0
    # With nonzero normal shift, the physical wall operator has a
    # genuine time-velocity term that a simple Israel derivative lacks.
    assert B[3]!=0
    assert s.simplify(C[3,3]-D/h[3]+D*v[3]**2/N**2)==0
    print('PASS BR48 Gaussian material collar: exact 4+1 normal flux -> D*physical normal derivative')

def shift_boundary():
    N,h,v,D,A,B,C=core()
    # Positive C iff v^T H v<N², since C=D H^-1/2
    # [I - (H^1/2 v)(H^1/2 v)^T/N²] H^-1/2.
    hnorm=sum(h[i]*v[i]**2 for i in range(4))
    determinant=s.factor(C.det())
    assert s.simplify(determinant / (D**4/s.prod(h))-(1-hnorm/N**2))==0
    # Explicit superluminal normal shift counterexample.
    bad={N:1, **{x:1 for x in h}, **{v[i]:(2 if i==3 else 0) for i in range(4)}}
    assert C.subs(bad)[3,3]<0
    assert s.simplify((C+B*B.T/A).subs(bad)-s.eye(4))==s.zeros(4)
    # Also explicit safe positive shifted example.
    good={N:2, **{x:1 for x in h}, **{v[i]:s.Rational(i,10) for i in range(4)}}
    assert (hnorm/N**2).subs(good)<1
    assert all(z>0 for z in C.subs(good).eigenvals())
    print('PASS BR48 positive Schur complement, safe timelike shift and superluminal counterexample')

def source_full():
    # Independent 5D polynomial field and full 4 spatial axes, including
    # material normal shift. Use positive but nontrivial coefficient jets.
    t,x,y,z,n=s.symbols('t x y z n')
    coords=(t,x,y,z,n)
    H=s.diag(1+t/9,1+n/11,1+y/13,1+x/17)
    shift=s.Matrix([(i+1)*(t+n)/19 for i in range(4)])
    N=2+t/7
    Hi=s.diag(*[1/H[i,i] for i in range(4)])
    D=N*s.sqrt(H.det())
    A=D/N**2; B=D*shift/N**2
    C=D*(Hi-shift*shift.T/N**2)
    ginv=(-s.Matrix([[1/N**2]])).row_join((shift/N**2).T)
    ginv=ginv.col_join((shift/N**2).row_join(Hi-shift*shift.T/N**2))
    u=t*x+t*t*n+y*z+n*n*x
    d=s.Matrix([s.diff(u,a) for a in coords])
    lhs=sum(s.diff(D*sum(ginv[i,j]*d[j] for j in range(5)),coords[i])
            for i in range(5))
    rhs=-s.diff(A*s.diff(u,t),t)
    rhs+=s.diff(sum(B[i]*s.diff(u,coords[i+1]) for i in range(4)),t)
    rhs+=sum(s.diff(B[i]*s.diff(u,t),coords[i+1]) for i in range(4))
    rhs+=sum(s.diff(C[i,j]*s.diff(u,coords[j+1]),coords[i+1])
             for i in range(4) for j in range(4))
    assert s.simplify(lhs-rhs)==0
    print('PASS BR48 independently differentiated full variable 5D densitized wave identity')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['collar','shift','source','all'],default='collar')
    a=p.parse_args()
    d={'collar':conforming_wall,'shift':shift_boundary,'source':source_full}
    for name,fn in d.items():
        if a.part in ('all',name):fn()

if __name__=='__main__':main()

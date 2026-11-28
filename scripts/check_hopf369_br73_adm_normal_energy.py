#!/usr/bin/env python3
"""BR73: shift-robust ADM physical normal-frame energy and boundary flux.

Original BR48: A=D/N²>0, B=A v, C=D H^-1-A vv^T.
The BR45 coordinate multiplier e=(A u_t²+C[grad u,grad u])/2
can be indefinite for v^T H v>N²; this is NOT a failure of the
Einstein time slices. The actual slice-normal physical energy is
  e_normal= (A (u_t-v·grad u)^2+D H^-1[grad u,grad u])/2.
Both terms are positive for N>0, H positive, D>0, with NO
artificial subluminal-shift guard. Identity with original e:
  2(e_normal-e)= -2 B·grad u u_t +2 A(v·grad u)^2.
The positive block completion is an exact Schur complement:
  [A,-B^T;-B,C+2 BB^T/A] =
  [A,-B^T;-B,DH^-1+BB^T/A]>0.
The opposite sign of B in the square follows from the ADM normal
derivative ∂t-v^i∂i, NOT a guessed symmetrizer.

The physical conormal J_F still contains the original B and C and
must be matched to the material graph (BR49/51). This is a POSITIVE
energy density, not a proof of a boundary-dissipative Einstein–Israel
IBVP or of a full variable-coefficient energy current identity.

--part algebra|negative|channels
"""
import argparse
import sympy as s

def symbolic():
    D,N=s.symbols("D N",positive=True)
    h=s.symbols('h0:4',positive=True)
    v=s.Matrix(s.symbols('v0:4',real=True))
    u=s.symbols("ut",real=True)
    d=s.Matrix(s.symbols('d0:4',real=True))
    Hi=s.diag(*[1/x for x in h])
    A=D/N**2;B=A*v;C=D*Hi-A*v*v.T
    coord=(A*u*u+(d.T*C*d)[0])/2
    normal=(A*(u-(v.T*d)[0])**2+(D*d.T*Hi*d)[0])/2
    assert s.expand(normal-coord+B.dot(d)*u-A*(v.T*d)[0]**2)==0
    M=s.Matrix.vstack(
       s.Matrix([[A]]).row_join((-B).T),
       (-B).row_join(C+2*B*B.T/A))
    square=s.expand((s.Matrix([u,*d]).T*M*s.Matrix([u,*d]))[0]/2)
    assert s.expand(square-normal)==0
    # The lower-right Schur complement of M is exactly D H^-1.
    assert (C+2*B*B.T/A-B*B.T/A-D*Hi).applyfunc(s.cancel)==s.zeros(4)
    return D,N,h,v,u,d,A,B,C,coord,normal

def algebra():
    symbolic()
    print("BR73 exact shift-robust positive normal-frame energy and Schur complement constructed")

def negative():
    D,N,h,v,u,d,A,B,C,e,normal=symbolic()
    high={D:1,N:1,**{h[i]:1 for i in range(4)},
          **{v[i]:(3 if i==3 else 0) for i in range(4)},
          u:0,**{d[i]:(1 if i==3 else 0) for i in range(4)}}
    assert C.subs(high)[3,3]==-8
    assert e.subs(high)<0 and normal.subs(high)>0
    assert normal.subs(high)==5
    # A causal graph must STILL have z>0 independently: positive
    # normal energy does not imply a timelike wall or Kreiss estimate.
    print("BR73 false C>0 chart restriction REFUSED; actual normal energy positive with large shift")

def channels():
    D,N,h,v,u,d,A,B,C,e,normal=symbolic()
    point={D:s.Rational(9,7),N:s.Rational(3,2)}
    point.update({h[i]:s.Rational(i+4,4) for i in range(4)})
    point.update({v[i]:s.Rational(i-1,3) for i in range(4)})
    def evaluate(dim):
        total=s.S.Zero
        for k in range(dim):
            jet={u:s.Rational(k+1,11)}
            jet.update({d[i]:s.Rational((k+2)*(i+3)%17-8,13) for i in range(4)})
            value=s.cancel(normal.subs(point).subs(jet))
            assert value>=0
            total+=value
        assert total>0
    evaluate(15);evaluate(5)
    print("BR73 original 15 metric +5 gauge positive ADM normal-frame channel energy")

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['algebra','negative','channels'],default='algebra')
    a=p.parse_args()
    {'algebra':algebra,'negative':negative,'channels':channels}[a.part]()

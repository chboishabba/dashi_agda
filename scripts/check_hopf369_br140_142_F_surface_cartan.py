#!/usr/bin/env python3
"""BR140-142: wall Cartan source jump, shear commutator and surface transport.
Exact local algebra only; not a combined IBVP estimate."""
import argparse
from itertools import combinations
import sympy as s
Q=s.Rational
h=s.diag(-1,1,1,1)

def eq(a,b):
    assert (a-b).applyfunc(s.expand)==s.zeros(*a.shape)

def jump():
    # Tangent-normal connection columns k_i; common intrinsic connection
    # and coframe at a wall point, with independent torsion and shape jets.
    j=s.symbols('j', nonzero=True)
    M=s.Matrix(4,4,lambda a,b:s.Symbol(f'm{min(a,b)}{max(a,b)}'))
    M[0,0]=M[1,1]+M[2,2]+M[3,3]
    k=h*M;th=s.eye(4);kp=k+j*th/2;km=k-j*th/2
    shape=lambda a,i,l: -a[:,i]*(a[:,l].T*h)+a[:,l]*(a[:,i].T*h)
    for i,l in combinations(range(4),2):
        expected=-j*(k[:,i]*th[:,l].T*h+th[:,i]*k[:,l].T*h-k[:,l]*th[:,i].T*h-th[:,l]*k[:,i].T*h)
        eq(shape(kp,i,l)-shape(km,i,l),expected)
        # Arbitrary shared intrinsic curvature cancels, as does the
        # target tangential Riemann jump with this exact Gauss source.
        B=s.Matrix(4,4,lambda a,b:s.Symbol(f'b{a}{b}'))
        eq((B+shape(kp,i,l))-(B+shape(km,i,l))-expected,s.zeros(4))
    T=s.Matrix(1,4,s.symbols('t:4'));DM=s.Matrix(1,4,s.symbols('d:4'))
    eq(-(DM+j*T/2)+(DM-j*T/2),-j*T)
    print('PASS BR140 common-wall tangential Cartan jump cancels; mixed jump retains intrinsic torsion')

def shear():
    # Restricted algebraic sector: E_parallel has Riemann symmetries
    # and zero temporal form slots, so only the spatial 3D Riemann block.
    def sym(n):return s.Matrix(3,3,lambda a,b:s.Symbol(f'{n}{min(a,b)}{max(a,b)}'))
    M=sym('m');S=sym('s')
    def R(i,k,b,a):return sum(s.LeviCivita(i,k,l)*s.LeviCivita(b,a,r)*S[l,r] for l in range(3) for r in range(3))
    b=s.Matrix([-sum(M[i,c]*R(k,l,c,a) for i,k,l in ((0,1,2),(1,2,0),(2,0,1)) for c in range(3)) for a in range(3)])
    K=M*S-S*M
    eq(b,s.Matrix([K[1,2],K[2,0],K[0,1]]))
    # commuting sector, pure trace, and generic anisotropic rank-three
    eq(b.subs({M[i,k]:s.eye(3)[i,k] for i in range(3) for k in range(i,3)}),s.zeros(3,1))
    d=s.diag(1,2,4);bd=b.subs({M[i,k]:d[i,k] for i in range(3) for k in range(i,3)})
    assert bd.jacobian([S[0,1],S[0,2],S[1,2]]).rank()==3
    S0=s.zeros(3);S0[0,1]=S0[1,0]=1
    assert bd.subs({S[i,k]:S0[i,k] for i in range(3) for k in range(i,3)})!=s.zeros(3,1)
    print('PASS BR141 spatial algebraic Gauss defect work is axial commutator of mean shear and dual curvature; generic rank 3')

def transport():
    # Actual ambient covariant time derivative in an adapted wall frame,
    # not the temporal-gauge frame unless the two happen to agree.
    def mat(seed,n,m):return s.Matrix(n,m,lambda i,j:Q(((i+2)*(j+3)*(seed+1))%17-8,19+seed))
    w=mat(1,4,4);w=w-h*w.T*h;k=mat(2,4,1);kn=-k.T*h
    B=mat(3,4,4);B=B-h*B.T*h;q=mat(4,4,1);e=-q.T*h
    O=w.row_join(k).col_join(kn.row_join(s.zeros(1)))
    E=B.row_join(q).col_join(e.row_join(s.zeros(1)))
    C=mat(5,5,5);g=s.diag(h,1);C=C-g*C.T*g
    Et=-C-O*E+E*O
    eq(Et[:4,:4]+w*B-B*w,-C[:4,:4]-k*e+q*kn)
    eq(Et[4,:4]-e*w,-C[4,:4]-kn*B)
    # Positive component norm: commutator has no derivatives of E.
    # Source is actual C_tij at the wall, not an arbitrary bulk L2 readout.
    assert (k*e-q*kn)!=s.zeros(4)
    print('PASS BR142 adapted-frame surface Cartan ODE retains both normal connection exchange terms and electric Bianchi trace')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['jump','shear','transport'],required=True)
    {'jump':jump,'shear':shear,'transport':transport}[p.parse_args().part]()

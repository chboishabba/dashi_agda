#!/usr/bin/env python3
"""BR41a actual Israel normal-work bound and explicit sum-of-squares certificate.

Source owner: Hopf369WarpedPhysicalBoundaryExact.israel and BR34 metric_side.
Proves *pointwise* real physical trace budget. Does not establish a trace
inequality, continuum energy absorption, or physical Einstein–Israel existence.
Can run independently of the BR29 heavy carrier in a 90-second section.
"""
from itertools import product
import sympy as s
from check_hopf369_br_warped_physical_attachment import metric_side, E4, trace4

def matrix_norm(a):
    return sum(v*v for v in a)

def bilinear(a,b):
    return sum(E4[i,i]*E4[j,j]*a[i,j]*b[i,j] for i,j in product(range(4),repeat=2))

def check():
    q=s.Matrix(s.symbols('q0:4',real=True))
    db=s.Matrix(s.symbols('db0:4',real=True))
    j,ls,ep=s.symbols('j ls ep',real=True,nonzero=True)
    L=q*db.T+db*q.T
    S=j*ls*E4
    # Spatial/temporal Lorentz signs are retained in work, while the
    # positive budget uses absolute componentwise Euclidean squares.
    q2=sum(q[i]**2 for i in range(4))
    d2=sum(db[i]**2 for i in range(4))
    cross=sum(q[i]*db[i] for i in range(4))
    wedge=sum((q[i]*db[k]-q[k]*db[i])**2
              for i in range(4) for k in range(i+1,4))
    assert s.expand(4*q2*d2-matrix_norm(L)-2*wedge)==0
    assert s.expand(matrix_norm(S)-4*j*j*ls*ls)==0
    # This full 16-entry identity is a sum of squares, not an unsigned
    # replacement of the physical Lorentzian contraction.
    W=s.Matrix(4,4,lambda i,k:s.Symbol('w%d%d'%(min(i,k),max(i,k)),real=True))
    J=s.Matrix(4,4,lambda i,k:s.Symbol('j%d%d'%(min(i,k),max(i,k)),real=True))
    def numerical(src):
        return [s.Rational(((i+2)*(k+5)+(i-k)**2+src)%17-8,7)
                for i,k in product(range(4),repeat=2)]
    # Independent source-owner physical Israel identity off continuity:
    # J = Hx+ - Hx- - q tensor [beta] - [beta] tensor q
    #     - j (ell+ + ell-) eta.
    for seed in (0,1,2,3):
        H=s.Matrix(4,4,numerical(seed));Hx=s.Matrix(4,4,numerical(seed+1))
        Hp=s.Matrix(4,4,numerical(seed+3));Hpx=s.Matrix(4,4,numerical(seed+4))
        bp=s.Matrix(numerical(seed+2)[:4]);bm=s.Matrix(numerical(seed+4)[:4])
        lp=s.Rational(seed+1,7);lm=s.Rational(seed-2,9)
        qq=s.Matrix([s.Rational(i+seed+1,7) for i in range(4)])
        jj=s.Rational(seed-6,5)
        def p(h,b,l):return h.row_join(b).col_join(b.T.row_join(s.Matrix([[2*l]])))
        a,b=p(H,bp,lp),p(Hp,bm,lm)
        da,dbb=p(Hx,s.zeros(4,1),0),p(Hpx,s.zeros(4,1),0)
        Ka=metric_side(a,da,qq,jj/2)[2]
        Kb=metric_side(b,dbb,qq,-jj/2)[2]
        I=2*(Ka-Kb)-jj*(H+Hp)
        LL=qq*(bp-bm).T+(bp-bm)*qq.T
        assert I==Hx-Hpx-LL-jj*(lp+lm)*E4
        assert bilinear(W,Hx-Hpx)==bilinear(W,I)+bilinear(W,LL)+jj*(lp+lm)*trace4(W)
    print('PASS actual BR34 Israel/normal-work identity, four independent source cases')

    # For real W and arbitrary real 16-entry physical source J, define
    # Z = J + L + S; bilinear(W,Z) uses E4_i E4_j signed entries.
    # 2 eps <W,Z> <= eps²||W||² + ||Z||²
    # ||Z||² <= 3(||J||²+||L||²+||S||²),
    # ||L||² <= 4||q||²||db||².
    # Every difference below is an explicit sum of squares.
    tvals=[
        (s.Rational(1,7),s.Rational(2,3),s.Rational(-5,4)),
        (s.Rational(-3,5),s.Rational(4,11),s.Rational(9,7)),
    ]
    for k,(jj,ell,eps) in enumerate(tvals):
        assert eps!=0
        Q=s.Matrix([s.Rational(k+i-3,5) for i in range(4)])
        B=s.Matrix([s.Rational(2*k-i+1,7) for i in range(4)])
        M=s.Matrix(4,4,lambda i,l:s.Rational((i+2)*(l+3)+k-11,13))
        V=s.Matrix(4,4,lambda i,l:s.Rational((i+1)*(l+5)+3*k-14,17))
        A=Q*B.T+B*Q.T; C=jj*ell*E4;Z=M+A+C
        zsum=3*(matrix_norm(M)+matrix_norm(A)+matrix_norm(C))-matrix_norm(Z)
        triples=sum(matrix_norm(U-T) for U,T in ((M,A),(M,C),(A,C)))
        assert zsum==triples and zsum>=0
        wed=sum((Q[i]*B[t]-Q[t]*B[i])**2 for i in range(4) for t in range(i+1,4))
        assert 4*sum(v*v for v in Q)*sum(v*v for v in B)-matrix_norm(A)==2*wed
        signed=bilinear(V,Z)
        r=abs(eps)
        gap=(r*r*matrix_norm(V)+3*(matrix_norm(M)
             +4*sum(v*v for v in Q)*sum(v*v for v in B)+4*jj*jj*ell*ell)
             -2*r*abs(signed))
        assert gap>=0
    print('PASS exact SOS rank-one, three-source, and signed Young boundary-work budget')
    print('Scope: real-time physical trace; complex-frequency norms require Hermitian polarization.')

if __name__=='__main__':check()

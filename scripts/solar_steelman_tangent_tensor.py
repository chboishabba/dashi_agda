"""Unity target on original l<=2 TE/TM tangent geometry.
Local rank-one tensor on labelled modal/material fibres, not a measured law.
"""
from pathlib import Path
import hashlib
from itertools import product
import numpy as np
import sympy as S
from solar_steelman_unity import geometry, modal_cycle, recovery

x,y,z=S.symbols('x y z',real=True);n=S.Matrix([x,y,z]);I=S.eye(3)
r=n.dot(n);P=I-n*n.T;ez=I[:,2]

def sz(a):
    return S.simplify(S.rem(S.expand(a),z*z+x*x+y*y-1,z))==0

def matzero(a):return all(sz(v) for v in a)
def stack(xs):return S.Matrix.vstack(*xs)


def angular_frames():
    # Same symmetric traceless Frobenius basis as the original SI shell.
    Q=[S.diag(1,-1,0)/S.sqrt(2),S.diag(1,1,-2)/S.sqrt(6)]
    for i,j in ((0,1),(0,2),(1,2)):
        q=S.zeros(3);q[i,j]=q[j,i]=1/S.sqrt(2);Q.append(q)
    assert all(S.trace(a*b)==(1 if i==j else 0) for i,a in enumerate(Q) for j,b in enumerate(Q))
    A=stack([n.cross(I[:,i])/S.sqrt(2) for i in range(3)])
    B=stack([P[:,i]/S.sqrt(2) for i in range(3)])
    C=stack([P*q*n for q in Q])
    for u in (A,B,C):
        assert sz(u.dot(u)-1)
        assert all(sz(n.dot(u[i:i+3,:])) for i in range(0,u.rows,3))
    # Directly compare the exact frames with the actual pinned donor's
    # normalized 16-mode angular chart at all 26 original quadrature sites.
    raw=(Path(__file__).resolve().parent/'check_smith_filsinger_solar_si_covariance.py').read_bytes()
    prefix=raw.split(b'\nrows=[];maxledger=')[0]
    assert hashlib.sha1(prefix).hexdigest()=='ab105e28cf1abbd145d4fd7a02daecfea8d124cc'
    env={};exec(compile(prefix,'original_si_prefix','exec'),env)
    for p in product((-1,0,1),repeat=3):
        if not any(p):continue
        v=S.Matrix(p)/S.sqrt(sum(t*t for t in p));sub=dict(zip(n,v));M=env['angular'](np.array(v,dtype=float).ravel())
        for u,block in ((A,M[:,:3]/np.sqrt(3)),(B,M[:,3:6]/np.sqrt(3)),(C,M[:,11:16]/np.sqrt(5))):
            assert np.allclose(np.array(u.subs(sub),float).ravel(),block.T.ravel(),atol=1e-14,rtol=0)
    return A,B,C


def gradient_route():
    # Forward-pure local differential route, with backward residuals retained.
    p=stack([P[:,i]/S.sqrt(2) for i in range(3)])
    q=stack([S.sqrt(3)/2*(z*P[:,i]+n[i]*P[:,2]) for i in range(3)])
    a=S.sqrt(S.Rational(3,2))*P[:,2]
    assert sz(p.dot(q)-S.sqrt(S.Rational(3,2))*z)
    assert sz(p.dot(p)-1) and sz(q.dot(q)-S.Rational(3,4)*(1+z*z))
    # Surface gradient of sqrt(3/2)*z is exactly the donor TM_z column.
    assert matzero(P*S.Matrix([0,0,S.sqrt(S.Rational(3,2))])-a)
    # Adjoint of gradient is -div; div(a)=-sqrt(6)*z.
    gp=S.sqrt(6)*z*q;gq=S.sqrt(6)*z*p
    assert sz(gp.dot(gp)-S.Rational(9,2)*z*z*(1+z*z))
    assert sz(gq.dot(gq)-6*z*z)
    # Sphere moments <z²>=1/3, <z⁴>=1/5; unit family norms.
    assert S.Rational(3,4)*(1+S.Rational(1,3))==1
    assert S.sqrt(6)*S.sqrt(S.Rational(3,2))/3==1
    rp=S.Rational(9,2)*(S.Rational(1,3)+S.Rational(1,5))-1
    rq=6*S.Rational(1,3)-1
    assert (rp,rq)==(S.Rational(7,5),S.Integer(1))
    return rp,rq


def tensor_inverse(A,B,C,g):
    # T*=g A tensor B tensor C on separate labelled tangent fibres.
    # Pointwise unit frame norms make all three reciprocal contractions exact.
    assert matzero(g*A*B.dot(B)*C.dot(C)-g*A)
    assert matzero(g*B*A.dot(A)*C.dot(C)-g*B)
    assert matzero(g*C*A.dot(A)*B.dot(B)-g*C)
    assert sz(g*g*A.dot(A)*B.dot(B)*C.dot(C)-g*g)
    # For any admissible tensor T, <T,A⊗B⊗C>=g. Cauchy gives ||T||>=|g|.
    # All other tensors with same three contractions are T*+N, with
    # N orthogonal to T*. Equal norm of the three profiles is necessary
    # for identical conjugate coupling because their trilinear scalar agrees.
    u,v,w,k=S.symbols('u v w k',real=True)
    assert S.expand((g*u+v)**2+ w*w-(g*g*u*u+2*g*u*v+v*v+w*w))==0
    # A fully explicit exact tensor at an original sphere point, including
    # all 9x9x15 entries and every reciprocal contraction.
    aa,bb,cc=[t.subs({x:0,y:0,z:1}) for t in (A,B,C)]
    T=S.MutableDenseNDimArray([g*i*j*k for i in aa for j in bb for k in cc],(9,9,15))
    assert sum(t*t for t in T._array)==g*g
    assert S.Matrix([sum(T[i,j,k]*bb[j]*cc[k] for j in range(9) for k in range(15)) for i in range(9)])==g*aa
    assert S.Matrix([sum(T[i,j,k]*aa[i]*cc[k] for i in range(9) for k in range(15)) for j in range(9)])==g*bb
    assert S.Matrix([sum(T[i,j,k]*aa[i]*bb[j] for i in range(9) for j in range(9)) for k in range(15)])==g*cc
    return g*g


def run():
    A,B,C=angular_frames();rp,rq=gradient_route();norm2=tensor_inverse(A,B,C,S.sqrt(2))
    F,_=geometry();state,M=modal_cycle(F);w=recovery(state,M)
    assert norm2==2 and w==S.Rational(1,2)
    print('PASS original 16-mode chart, 26 sites, exact pointwise tangent and unit-frame identities')
    print('PASS forward pure differential target, backward residual squares',rp,rq)
    print('PASS reciprocal rank-one tensor target: norm squared',norm2,'all three contractions exact')
    print('PASS same modal unity and recovery replay; physical labelled-fibre tensor and Maxwell/radial realization remain unadmitted')
if __name__=='__main__':run()

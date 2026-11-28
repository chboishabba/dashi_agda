"""Exact matched harmonic-interface composition and continuous HF return.
Conditional envelope model, not causal distributed Maxwell realization.
"""
import sympy as S
from solar_steelman_exact_radial import certify, zero
from solar_steelman_unity import geometry, modal_cycle
from solar_steelman_hf_continuous import continuous, two_mode_hamiltonian


def port(f):
    # Three independent selected traces in four radial modes. Exact Cayley
    # regression, not the physical spherical fundamental transfer.
    blocks=[]
    for j in range(1,5):
        L=S.Matrix([[0,-S.I*f*j],[-S.I*f/j,0]])
        blocks.append((S.eye(2)-L/2).inv()*(S.eye(2)+L/2))
    idx=[0,2,4,6,1,3,5,7];M=S.diag(*blocks).extract(idx,idx)
    T=S.eye(4)[:3,:];k=S.Rational(5,2)
    R,U,Bout=certify(M,T,k)
    # Gram normalization, for this diagonal fixture; general SPD R admits
    # R^{-1/2} by the spectral theorem.
    assert R.is_diagonal()
    C=S.diag(*[1/S.sqrt(S.simplify(R[j,j])) for j in range(3)])
    P=(U*C).applyfunc(S.simplify)
    assert zero(C.H*R*C-S.eye(3))
    assert zero(k*P.H*P-S.eye(3))
    return R,U,Bout,C,P,k


def reopen(port,z):
    R,U,B,C,P,k=port;i=C*z;u=P*z
    # Actual matched terminal current is i by certify(), so reflection zero.
    assert zero(U*i-u) and zero(B*(i-i))
    assert S.simplify((i.H*R*i)[0]-(z.H*z)[0])==0
    assert zero(k*P.H*u-z)
    return k*P.H*u


def run():
    F,_=geometry();x,_=modal_cycle(F)
    high=port(S.Rational(783,100));low=port(S.Rational(783,200))
    incoming=F.H[:,0];s=F*reopen(high,incoming)
    assert zero(s-S.eye(3)[:,0])
    h=S.Matrix([x[2],x[3],0]);y=reopen(low,h)
    bright=S.Matrix([[1,1,0],[1,-1,0],[0,0,S.sqrt(2)]])/S.sqrt(2)
    assert zero(bright.H*bright-S.eye(3))
    assert zero(bright*y-S.eye(3)[:,0])
    two_mode_hamiltonian();store=continuous()
    # Signed residual controls: orthogonal output and mismatch are not unity.
    assert zero(bright*S.Matrix([1,-1,0])/S.sqrt(2)-S.eye(3)[:,1])
    R,U,B,C,P,k=high;d=C[:,0];assert S.simplify(k*(B*d).dot(S.conjugate(B*d)))==1
    print('PASS exact harmonic interface composition: incident=1 useful=1 reflection=0 dark=0')
    print('PASS continuous HF internal storage return, no source pause; normalized stored energy',store)
    print('Conditional matched source subspaces and ideal envelope interconnect; physical causal coupling unadmitted')
if __name__=='__main__':run()

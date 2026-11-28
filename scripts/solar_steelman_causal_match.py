"""Two-frequency reciprocal passive matching, exact Foster synthesis.
Finite interpolation, not broadband or atmospheric realization.
"""
import sympy as S
from solar_steelman_exact_radial import certify, zero


def fixture(w):
    blocks=[]
    for j in range(1,5):
        L=S.Matrix([[0,-S.I*w*j],[-S.I*w/j,0]])
        blocks.append((S.eye(2)-L/2).inv()*(S.eye(2)+L/2))
    idx=[0,2,4,6,1,3,5,7];M=S.diag(*blocks).extract(idx,idx)
    T=S.Matrix([[1,1,0,0],[0,1,1,0],[0,0,1,1]])
    R,U,Bout=certify(M,T,S.Rational(5,2))
    A,B,C,D=M[:4,:4],M[:4,4:],M[4:,:4],M[4:,4:]
    Z=T*(A-C).inv()*(D-B)*T.T/S.Rational(5,2)
    return Z.H.applyfunc(S.simplify),R,U,Bout


def branch(w,v,target,s):
    R=S.re(target);X=S.im(target);I=S.eye(R.rows)
    assert zero(R-R.T) and zero(X-X.T)
    assert all(S.simplify(R[:j,:j].det()).is_positive for j in range(1,R.rows+1))
    # Positive residue I at the blocking pole. Add positive L and inverse C
    # to match arbitrary real symmetric target reactance at own frequency.
    Y=X-w/(v*v-w*w)*I
    alpha=1+sum(abs(x) for x in Y)
    L=(Y+alpha*I)/w;K=w*alpha*I
    assert all(S.simplify(L[:j,:j].det()).is_positive for j in range(1,R.rows+1))
    Z=R+s*L+K/s+s/(s*s+v*v)*I
    assert zero(Z.subs(s,S.I*w)-target)
    # Pole-free admittance expression; exactly zero at other frequency.
    den=s*(s*s+v*v)
    N=(den*R+s*den*L+(s*s+v*v)*K+s*s*I).applyfunc(S.expand)
    assert zero(N.subs(s,S.I*v)+v*v*I)
    return R,L,K,Z,N,den


def run():
    s=S.symbols('s');w=S.Rational(783,200);v=2*w
    rows=[fixture(f) for f in (w,v)]
    branches=[branch(w,v,rows[0][0],s),branch(v,w,rows[1][0],s)]
    for k,f in enumerate((w,v)):
        Y=S.zeros(3)
        for R,L,K,Z,N,den in branches:
            Y+=den.subs(s,S.I*f)*N.subs(s,S.I*f).inv()
        assert zero(Y.inv()-rows[k][0])
        print('exact two-band termination',f,'PASS',flush=True)
    # State realization of each series branch: effort R i+L idot+K q+x,
    # qdot=i, xdot=i-v² z, zdot=x. Energy storage L,K,I,v²I.
    i,di,q,x,z,r,l,k,b=S.symbols('i di q x z r l k b',real=True)
    e=r*i+l*di+k*q+x
    assert S.expand(l*i*di+k*q*i+x*(i-b*b*z)+b*b*z*x-e*i+r*i*i)==0
    # At blocking frequency, branch current zero but resonator effort x
    # equals applied voltage; periodic z=x/(i omega) restores its state.
    V=S.symbols('V');assert S.simplify(S.I*v*V+v*v*V/(S.I*v))==0
    # Both sinusoidal frequencies share a period. No startup claim.
    assert v/w==2
    print('PASS passive reciprocal causal state realization and common periodic return')
    print('Conditional two-frequency fixtures; no actual nonlinear converter termination or measured source admission')
if __name__=='__main__':run()

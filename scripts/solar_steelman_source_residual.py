"""Same incident source, exact matched-space projection and dark complement."""
import sympy as S
from solar_steelman_causal_match import fixture
from solar_steelman_exact_radial import zero


def run():
    k=S.Rational(5,2)
    for f in (S.Rational(783,200),S.Rational(783,100)):
        Zload,R,U,B=fixture(f)
        # Independently recover the original fixture's outgoing wave map.
        blocks=[]
        for j in range(1,5):
            L=S.Matrix([[0,-S.I*f*j],[-S.I*f/j,0]])
            blocks.append((S.eye(2)-L/2).inv()*(S.eye(2)+L/2))
        idx=[0,2,4,6,1,3,5,7];M=S.diag(*blocks).extract(idx,idx)
        A,Bm,C,D=M[:4,:4],M[:4,4:],M[4:,:4],M[4:,4:]
        T=S.Matrix([[1,1,0,0],[0,1,1,0],[0,0,1,1]])
        F=2*(A-C).inv();Z=(A-C).inv()*(D-Bm);G=T.T/k
        B0=A*F-S.eye(4)
        assert zero(B0.H*B0-S.eye(4))
        assert zero(B+B0*U) and zero(T*F-2*k*U.H)
        assert zero(B+(A*Z+Bm)*G)
        # Power-orthogonal projection in common incident coordinates.
        P=(k*U*R.inv()*U.H).applyfunc(S.simplify)
        assert zero(P.H-P) and zero(P*P-P) and P.rank()==3
        u=U[:,0];d=U.H.nullspace()[0]
        u=u/S.sqrt(S.simplify(k*(u.H*u)[0]))
        d=d/S.sqrt(S.simplify(k*(d.H*d)[0]))
        assert zero(P*u-u) and zero(P*d)
        # Source kept fixed; do not replace it by its projection.
        z=(3*u+4*d)/5
        i=R.inv()*k*U.H*z
        captured=S.simplify((i.H*R*i)[0])
        residual=S.simplify(k*((z-P*z).H*(z-P*z))[0])
        p=(T*Z*G+Zload).inv()*T*F*z
        assert zero(p-i)
        outgoing=(B0*z+B*p).applyfunc(S.simplify)
        assert zero(outgoing-B0*(z-P*z))
        assert S.simplify(k*(outgoing.H*outgoing)[0])==residual
        assert captured==S.Rational(9,25) and residual==S.Rational(16,25)
        assert S.simplify(k*(z.H*z)[0])==1
        # Arbitrary current mismatch increases reflection above the
        # inaccessible source residual (orthogonal output components).
        delta=S.Matrix([1,0,0]);extra=S.simplify((delta.H*R*delta)[0])
        assert extra>0
        mismatch=outgoing+B*delta
        assert S.simplify(k*(mismatch.H*mismatch)[0]-residual-extra)==0
        print(f,'incident=1 accessible=9/25 residual=16/25; unity iff residual=0')
    print('PASS fixed-source projection and explicit signed complement; no measured source membership claimed')
if __name__=='__main__':run()

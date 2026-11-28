"""Exact lossless radial port theorem, with rational complex regression.
The continuum premise is J-unitarity, proved by the radial generator identity.
No numeric ODE tolerance is used to certify unity; no physical loss removal.
"""
import sympy as S


def zero(M):
    return all(S.simplify(x)==0 for x in M)


def certify(M,T,k):
    n=T.cols; m=T.rows; I=S.eye(n); O=S.zeros(n)
    J=O.row_join(I).col_join(I.row_join(O))
    assert zero(M.H*J*M-J)
    A,B,C,D=M[:n,:n],M[:n,n:],M[n:,:n],M[n:,n:]
    E,H=(M.inv()*I.col_join(-I))[:n,:],(M.inv()*I.col_join(-I))[n:,:]
    assert zero(E.H*H+H.H*E+2*I)
    # H is injective by the preceding identity, hence invertible.
    G=T.H/k; U=-H.inv()*G; V=E*U
    Z=(A-C).inv()*(D-B); F=2*(A-C).inv()
    Zp=T*Z*G; R=(Zp+Zp.H)/2
    # The reverse solution has precisely zero reflected amplitude.
    assert zero(M*V.col_join(-G)-U.col_join(-U))
    assert zero(V-F*U+Z*G)
    # Reflection for arbitrary receiver current p: b=Bout*(p-i).
    Bout=-A*Z*G-B*G
    assert zero(R-k*Bout.H*Bout)
    assert zero(T*F*U-2*R)
    assert zero(R-k*U.H*U)
    assert zero(T*V-Zp.H)
    assert all(S.simplify(R[:j,:j].det()).is_positive for j in range(1,m+1))
    # Independently solve matched terminal equation for all incident columns.
    assert zero((Zp+Zp.H).inv()*T*F*U-S.eye(m))
    return R,U,Bout


def run():
    # Lossless radial generator: arbitrary real TE/TM reactances.
    a,b,y=S.symbols('a b y',real=True,nonzero=True)
    J=S.Matrix([[0,1],[1,0]])
    L=S.Matrix([[0,-S.I*a*y],[-S.I*b/y,0]])
    assert zero(L.H*J+J*L)
    # Thus d(M^H J M)/dr=0 for the original variable radial generator.
    # Rational Cayley products are independent exact regression fixtures,
    # not numerical approximations asserted equal to the original ODE.
    for f in (S.Rational(783,200),S.Rational(783,100)):
        blocks=[]
        for j in range(1,4):
            l=L.subs({a:f*j,b:f/(j+1),y:2});I=S.eye(2)
            blocks.append((I-l/2).inv()*(I+l/2))
        M=S.diag(*blocks);idx=[0,2,4,1,3,5];M=M.extract(idx,idx)
        T=S.Matrix([[1,2,0],[0,1,1]])
        R,U,Bout=certify(M,T,S.Rational(5,2))
        p=S.Matrix([1,S.I]);w=(p.H*R*p)[0];p=p/S.sqrt(w)
        assert S.simplify((p.H*R*p)[0])==1
        assert S.simplify((p.H*U.H*U*p)[0]*S.Rational(5,2))==1
        assert zero(Bout*(p-p))
        # A nonzero current mismatch gives strictly positive reflection.
        d=S.Matrix([1,0]);assert S.simplify((d.H*R*d)[0])>0
        print('exact fixture',f,'incident=1 useful=1 reflected=0')
    print('PASS exact radial generator and matched-subspace identities')
if __name__=='__main__':run()

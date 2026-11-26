"""BE: source-preserving periodic scalar/second-jet coupling, exact algebra.
No numeric PDE integration or evaluated small-data threshold.
"""
import sympy as s


def main():
    L,y,j,u,S=s.symbols('L y j u S', positive=True)
    f=y*y*(L-y)**2*(L-2*y)/L**3
    for z in (0,L):
        assert f.subs(y,z)==0 and s.diff(f,y).subs(y,z)==0
    assert s.diff(f,y,2).subs(y,0)==2
    assert s.diff(f,y,2).subs(y,L)==-2
    assert s.expand(f.subs(y,L-y)+f)==0
    a,b,c,d,e=s.symbols('a b c d e', real=True)
    M=s.Matrix([[a,b,c],[b,d,e],[c,e,-a-d]])
    p,q,r,t,v=s.symbols('p q r t v', real=True)
    J=s.Matrix([[p,q,r],[q,t,v],[r,v,-p-t]])
    C=-(J+3*j*(u-1)*M)/(2*S)
    ex=lambda A:A.applyfunc(s.expand)
    assert ex(J+2*S*C+3*j*(u-1)*M)==s.zeros(3)
    assert s.expand(s.trace(C))==0
    # Normal second jet from tangential block modification: principal Ricci
    # tensor formula at a point with zero correction and zero first derivatives.
    av=s.Matrix(s.symbols('a0:3',real=True)); I=s.eye(3)
    G=(I+av*av.T).row_join(av).col_join(av.T.row_join(s.ones(1,1)))
    Gi=I.row_join(-av).col_join((-av.T).row_join(s.Matrix([[1+av.dot(av)]])))
    assert ex(G*Gi-s.eye(4))==s.zeros(4)
    Z=C.row_join(s.zeros(3,1)).col_join(s.zeros(1,4))
    def dd(i,k,a,b):return 2*Z[a,b] if i==k==3 else 0
    R=s.Matrix(4,4,lambda a,b:sum(Gi[i,k]*(dd(i,a,k,b)+dd(i,b,k,a)-dd(i,k,a,b)-dd(a,b,i,k))/2 for i in range(4) for k in range(4)))
    assert ex(R[:3,:3]+Gi[3,3]*C)==s.zeros(3)
    # Exact BIDI connection, radion and horizontal block after correction.
    g=u**2*(G+Z); phi2=g[3,3]; read=g[:3,3]/phi2
    assert ex(read-av)==s.zeros(3,1)
    assert ex(g[:3,:3]-phi2*read*read.T-u**2*(I+C))==s.zeros(3)
    # Polynomial clearing of original AN rational Hopf connection. delta=1-r²,
    # F=2(1+r²)/h0; X=F*x/delta². A=2 delta⁴ W / (delta⁴+F² r²)².
    x=s.Matrix(s.symbols('x1:4',real=True)); x1,x2,x3=x; d0,F,H=s.symbols('delta F h0',positive=True)
    X=F*x/d0**2; X1,X2,X3=X
    W=s.Matrix([2*F**2*x1*x3-2*F*d0**2*x2,2*F*d0**2*x1+2*F**2*x2*x3,d0**4-F**2*x1*x1-F**2*x2*x2+F**2*x3*x3])
    A=2*s.Matrix([2*X1*X3-2*X2,2*X1+2*X2*X3,1-X1*X1-X2*X2+X3*X3])/(1+X.dot(X))**2
    den=d0**4+F**2*x.dot(x)
    assert (A-2*d0**4*W/den**2).applyfunc(s.cancel)==s.zeros(3,1)
    P=F/d0**2*I+2*(2/(H*d0**2)+2*F/d0**3)*x*x.T
    assert (P*A-d0*2*(F*d0*I+(4*d0/H+4*F)*x*x.T)*W/den**2).applyfunc(s.cancel)==s.zeros(3,1)
    # AK5 seam operator and positive ground-state potential (c=1).
    n=s.symbols('n',real=True); b0=s.Rational(4,5)*s.cosh(n-s.log(2))
    lapb=s.diff(b0,n,2)+3*s.diff(b0,n)**2/b0
    assert s.simplify(-lapb+4*b0-3*s.Rational(4,5)**2/b0)==0
    assert s.simplify(s.diff(b0,n).subs(n,0)-s.diff(b0,n).subs(n,2*s.log(2))+s.Rational(6,5))==0
    eps,z=s.symbols('eps z',real=True)
    # At epsilon=0 both M_TF and J_TF vanish: coupling's u derivative zero.
    seed=-f*(eps*J+3*j*z*eps*M)/(2*S)
    assert seed.diff(z).subs(eps,0)==s.zeros(3)
    print('PASS signed polynomial seam, full five-component cancellation, independent Ricci principal jet, KK BIDI, original rational decay, AK5 gap and zero-amplitude linearization')

if __name__=='__main__':main()

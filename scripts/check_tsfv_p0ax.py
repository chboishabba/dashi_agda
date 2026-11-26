"""AX: selected original complex Hilbert and same-action source controls."""
import sympy as s


def observer():
    a=s.symbols('a:8',real=True); b=s.symbols('b:8',real=True)
    mat=lambda z:s.Matrix(2,2,[z[2*j]+s.I*z[2*j+1] for j in range(4)])
    A,B=mat(a),mat(b); psi=s.Matrix([1,1]); u=A*psi; v=B*psi
    norm=lambda x:s.expand((x.conjugate().T*x)[0]/2)
    omega=lambda M:s.expand((psi.T*M*psi)[0]/2)
    assert omega(s.eye(2))==1 and omega(s.zeros(2))==0
    assert s.expand(omega(A.conjugate().T*B)-(u.conjugate().T*v)[0]/2)==0
    assert s.expand(omega(A.conjugate().T*A)-norm(u))==0
    assert s.im(norm(u))==0
    section=lambda x:x.row_join(s.zeros(2,1))
    residual=A-section(u)
    assert residual*psi==s.zeros(2,1)
    assert (section(u)+residual)==A
    assert all(s.expand(x)==0 for x in B*residual*psi)
    # Kernel is only a left ideal: right multiplication can reveal it.
    R=s.Matrix([[1,-1],[0,0]]); X=s.diag(1,-1)
    assert R*psi==s.zeros(2,1) and R*X*psi!=s.zeros(2,1)
    # Exact original ABL ratio unchanged when both amplitudes share half scaling;
    # its stronger admissibility certificate need not survive the rescaling.
    x,y=s.symbols('x y',nonnegative=True)
    assert s.cancel((x/4)/(x/4+y/4)-x/(x+y))==0
    assert s.Rational(1,4)<1
    print('PASS original normalized complex Gram, zero, cyclic residual, left ideal and ABL distinction')


def path_stress():
    t=s.symbols('t',real=True); g0=s.diag(-2,3,4,5); p=s.Matrix([2,-1,3,s.Rational(1,2)])
    q=s.Rational(2,3); m=s.Rational(7,10); v=s.sqrt(-g0.det()); checks=0
    # All ordered off-diagonal elementary shears preserve determinant, including time-space mixing.
    for i in range(4):
        for j in range(4):
            if i==j: continue
            N=s.zeros(4); N[i,j]=1; B=s.eye(4)+t*N
            g=B.T*g0*B; gi=(s.eye(4)-t*N)*g0.inv()*(s.eye(4)-t*N).T
            assert g.det()==g0.det() and s.simplify(g*gi)==s.eye(4)
            H=v*gi; V=v*m
            S1=-((p.T*H*p)[0]+V*q*q)/2
            S2=-v*((p.T*gi*p)[0]+m*q*q)/2
            assert s.expand(S1-S2)==0
            E=s.diff(g,t).subs(t,0); T=p*p.T-g0*((p.T*g0.inv()*p)[0]+m*q*q)/2
            assert s.simplify(s.diff(S1,t).subs(t,0)-v*s.trace(g0.inv()*T*g0.inv()*E)/2)==0
            checks+=1
    print('PASS',checks,'globally nondegenerate metric shear action paths and stress variations')


def coupled_ward():
    t=s.symbols('t',real=True); q=s.Function('q')(t); z=s.Function('z')(t); h=s.Function('h')(t)
    m,b,l=s.symbols('m b l',real=True); V=(m*q*q+b*z*z+l*q*q*z*z)/2
    dq=s.diff(q,t); dz=s.diff(z,t)
    rho=(dq*dq+dz*dz)/2+V; p=(dq*dq+dz*dz)/2-V
    Eq=s.diff(q,t,2)+3*h*dq+(m+l*z*z)*q
    Ez=s.diff(z,t,2)+3*h*dz+(b+l*q*q)*z
    assert s.expand(s.diff(rho,t)+3*h*(rho+p)-Eq*dq-Ez*dz)==0
    rq=(dq*dq+(m+l*z*z)*q*q)/2; pq=(dq*dq-(m+l*z*z)*q*q)/2
    exchange=l*q*q*z*dz
    assert s.expand(s.diff(rq,t)+3*h*(rq+pq)-Eq*dq-exchange)==0
    print('PASS coupled scalar Ward and explicit source exchange; no Einstein evolution claimed')


if __name__=='__main__':
    observer(); path_stress(); coupled_ward()

"""BQ/BR: exact fourth normal jump, shell variable inverse and energy controls.
Finite algebra and frozen energy examples, not a coupled Einstein evolution.
"""
import sympy as s
from itertools import product


def z(A):
    return all(s.expand(x)==0 for x in A) if isinstance(A,s.MatrixBase) else s.expand(A)==0


def fourth():
    j,q,b,m3,ub=s.symbols('j q b m3 ub'); U,B,C=s.symbols('U B C',commutative=False)
    tau1=4-q-j*j; J=j*(4+q)-12*j*U**2
    pol=[]; ls=[]
    for sign in (1,-1):
        A=U+sign*j/2; F=C+sign*J/2; tau=sign*2*j
        tau2=-2*(ub+sign*j*b/2)+4*(m3+sign*3*j*q/2+sign*j**3/2)
        ls.append((8-tau1)*A-tau*B+2*(B*A+A*B-2*A**3))
        pol.append(8*B-tau2*A-2*tau1*B-tau*F+2*(F*A+A*F+2*B**2-4*B*A**2-4*A**2*B+8*A**4-2*A*B*A))
    actual=s.expand(pol[0]-pol[1]-4*j*(C-(ls[0]+ls[1])/2)).subs(b,4+q+j*j).expand()
    target=j*((40+6*j*j-2*q)*U-12*(B*U+U*B)-4*C+2*ub-4*m3)
    assert z(actual-target)
    # Independent rational normal-series check with noncommuting Lorentz self-adjoint tensors.
    h=s.diag(-1,1,1,1); I=s.eye(4); t=s.symbols('t'); j=s.Rational(-6,5)
    for seed in range(1,9):
        def selfadj(k):
            A=s.Matrix(4,4,lambda a,b:s.Rational(((a+b+1)*(a*b+seed+k)+k)%17-8,19))
            return h*A
        U=selfadj(1);U-=s.trace(U)*I/4;q=s.trace(U**2)
        B=selfadj(2);B+=(4+q+j*j-s.trace(B))*I/4
        C=selfadj(3);C+=(4*s.trace(U*B)-4*s.trace(U**3)-s.trace(C))*I/4
        J=j*((4+q)*I-12*U**2); out=[]; Ls=[]
        for side in (1,-1):
            A=U+side*j*I/2;F=C+side*J/2
            assert s.trace(F)==4*s.trace(A*B)-4*s.trace(A**3)
            # h(n)=h(1+2nA+n²B+n³F/3), K(n)=h(A+nB+n²F/2).
            # Polynomial inverse through order 2, independently multiply and extract.
            hh=I+2*t*A+t*t*B; inv=I-2*t*A+t*t*(4*A*A-B); K=A+t*B+t*t*F/2
            low=lambda X,k:X.applyfunc(lambda x:s.expand(x).coeff(t,k))
            assert low(hh*inv,0)==I and low(hh*inv,1)==s.zeros(4) and low(hh*inv,2)==s.zeros(4)
            L=4*hh-s.trace(inv*K)*K+2*K*inv*K
            Ls.append(low(L,1));out.append(2*low(L,2))
        # Ric'' difference from constant scaling = -4j(C-Lmean).
        result=out[0]-out[1]-4*j*(C-(Ls[0]+Ls[1])/2)
        want=j*((40+6*j*j-2*q)*U-12*(B*U+U*B)-4*C+(2*s.trace(U*B)-4*s.trace(U**3))*I)
        assert result==want
        assert want.T*h==h*want
        # Reflection U,C odd, B even gives opposite fourth-jet jump.
        assert j*((40+6*j*j-2*q)*(-U)-12*(B*(-U)+(-U)*B)-4*(-C)+(2*s.trace((-U)*B)-4*s.trace((-U)**3))*I)==-want
    # Highest fourth-jet repair, +/- fourth coordinate derivatives.
    u,S=s.symbols('u S',positive=True); E=s.symbols('E'); c4=-u*u*E/S**2
    assert s.simplify(E+u*u*(s.sqrt(S)/u)**4*c4)==0
    print('PASS exact fourth jump, 8 independent rational noncommuting series, signed reflection and fourth repair',flush=True)


def flatten():
    # Arbitrary Lorentz tangential block, nonzero shift, lapse lambda>0.
    h=s.Matrix([[-3,1,0,0],[1,4,1,0],[0,1,5,1],[0,0,1,2]])
    b=s.Matrix(s.symbols('b:4')); a,j=s.symbols('a j',positive=True)
    g=h.row_join(h*b).col_join((b.T*h).row_join(s.Matrix([[a*a+(b.T*h*b)[0]]])))
    n=s.Matrix([0,0,0,0,a]); J=a*(2*j*g+6*j*n*n.T)
    assert z(J[:4,:4]-2*j*a*h)
    db=h.inv()*(J[:4,4]-J[:4,:4]*b);assert z(db)
    dl2=J[4,4]-(b.T*J[:4,:4]*b)[0]-2*(b.T*h*db)[0]
    da=s.simplify(dl2/(2*a));assert da==4*j*a*a
    assert s.simplify(-da/a**2)==-4*j
    assert z(J[:4,:4]/s.sqrt(a)-h*da/(2*a**s.Rational(3,2)))
    # Inverse reconstruction and normal norm.
    gi=g.inv();assert s.simplify(gi[4,4]-1/a**2)==0
    assert s.simplify((n.T*gi*n)[0]-1)==0
    # Linearized jump triangular mixing: eigenmode shift removes h*normal term.
    R=s.Matrix([[2*j,j],[0,12*j]]);T=s.Matrix([[1,-s.Rational(1,10)],[0,1]])
    assert T*R*T.inv()==s.diag(2*j,12*j)
    assert (T.T*T*R).T==T.T*T*R
    # Periodic cusp profile with specified same-oriented derivative jump.
    y,L=s.symbols('y L',positive=True);p=-2*j*y*(L-y)/L
    assert p.subs(y,0)==p.subs(y,L)==0 and s.diff(p,y).subs(y,0)-s.diff(p,y).subs(y,L)==-4*j
    print('PASS nonlinear lapse/shift/shape jump flattening with nonzero shift, inverse, linear symmetrizer, periodic cusp',flush=True)


def energy():
    # Frozen common metric, component Euclidean norm. Boundary flux is -Ct^T R C.
    j=s.symbols('j',real=True); C=s.Matrix(s.symbols('C:5')); V=s.Matrix(s.symbols('V:5'));R=s.diag(2*j,2*j,2*j,2*j,4*j)
    assert z((V.T*R*C)[0]-(C.T*R*V)[0]/2-(V.T*R*C)[0]/2)
    # Time dependent positive component inner product and symmetric product S=WR.
    t=s.symbols('t'); c=s.Matrix([s.Function('c'+str(i))(t) for i in range(5)]); W=s.diag(*[s.Function('w'+str(i))(t) for i in range(5)])
    S=W*R
    assert s.simplify(s.diff((c.T*S*c)[0]/2,t)-(c.diff(t).T*S*c)[0]-(c.T*S.diff(t)*c)[0]/2)==0
    # Negative Robin potential controlled by trace |v(0)|² <= L^-1||v||²+2||v||||v'||.
    # Frozen actual parameters L=2log2>1, a=4|j|=24/5. Add mass 104.
    a=s.Rational(24,5);mass=104
    bound=a+2*a*a;assert bound<mass/2
    # No energy-level control of forced term by bulk time-derivative L2 alone.
    # normalized one-sided linear ramp v=(1-y/d)/sqrt(d), 0<=y<=d.
    y,d=s.symbols('y d',positive=True);v=(1-y/d)/s.sqrt(d)
    assert s.integrate(v*v,(y,0,d))==s.Rational(1,3) and v.subs(y,0)==1/s.sqrt(d)
    k=s.Function('k')(t);cn=c[4]
    assert s.simplify(-6*j*k*s.diff(cn,t)+s.diff(6*j*k*cn,t)-6*j*s.diff(k,t)*cn)==0
    print('PASS gauge Robin energy, explicit frozen mass coercivity, forcing trace obstruction and product identity',flush=True)


def adS_scalar():
    R,h,lam=s.symbols('R h lam',positive=True);D=s.symbols('D',real=True);f=1+h*h*R*R;v=R**(-D)
    expr=s.expand(R**D*s.diff(R*R*f*s.diff(v,R),R)/(R*R))
    assert s.simplify(s.limit(expr,R,s.oo)-h*h*D*(D-3))==0
    # Leading radial flux coefficient exponent 3-2D, decaying root >=3 for lam>=0.
    assert s.simplify((3+s.sqrt(9+4*lam/h**2))/2*((3+s.sqrt(9+4*lam/h**2))/2-3)-lam/h**2)==0
    print('PASS AK scalar radial indicial equation, distinct from gravitational tensor modes',flush=True)

def moving_symbol():
    # Local principal model, not all lower-order terms of the real moving wall.
    j,L,f=s.symbols('j L f',real=True,nonzero=True)
    t,x,y,z=s.symbols('t x y z',real=True)
    F=s.Function('F')(t,x,y,z);a=s.symbols('a:4');h=s.diag(-1,1,1,1)
    # Unit normal to graph n=y-F: tangential variation -dF.
    dF=s.Matrix([s.diff(F,i) for i in (t,x,y,z)])
    K=s.Matrix(4,4,lambda i,k:-s.diff(dF[i],(t,x,y,z)[k]))
    assert s.expand(s.trace(h*K)+sum(h[i,i]*s.diff(F,(t,x,y,z)[i],2) for i in range(4)))==0
    # Laplace-Fourier decaying mode exp(-L*n) and exp(+L*n).
    # D^a D_a=-L^2; Eulerian value jump=-f*J0, J0_ab=2j h_ab.
    value_jump=-2*j*f*h;normal_mean=-L*value_jump/2
    assert s.trace(h*normal_mean)==4*j*L*f
    # Leading tilted normal derivative jump in mixed channel = -6j D_a f.
    # Average mixed amplitude = 3j D_a f/L (omit all order-zero Robin terms).
    div_mixed=3*j*(-L**2)*f/L
    mean_curvature=L**2*f+s.trace(h*normal_mean)/2-div_mixed
    assert s.expand(mean_curvature-L*(L+5*j)*f)==0
    print('PASS graph mean curvature and leading moving-interface normal-mode cancellation (not full symbol)',flush=True)


if __name__=='__main__':fourth();flatten();energy();adS_scalar();moving_symbol()

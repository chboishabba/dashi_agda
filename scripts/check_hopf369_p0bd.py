"""BD: exact original AN initial shear and parallel-normal length obstruction.
No assertion of global Gaussian normal coordinates on the original seed.
"""
import sympy as s


def exact_seed(point, eps):
    # AN wall: b=1, H=gamma+a*a.T, shift covector a, normal lapse 1/sqrt(S).
    # Rational pullback of original Hopf connection; at rational points all
    # tangential derivatives are rational, so q=tr((h^-1 M)^2) is exact.
    x=s.Matrix(s.symbols('x1:4')); r2=x.dot(x); h0=s.Rational(4,5)
    fac=2*(1+r2)/(h0*(1-r2)**2)
    X=fac*x; X1,X2,X3=X; den=1+X.dot(X)
    A=2*s.Matrix([2*X1*X3-2*X2,2*X1+2*X2*X3,1-X1**2-X2**2+X3**2])/den**2
    a=eps*X.jacobian(x).T*A
    gam=4/(h0**2*(1-r2)**2)
    sub=dict(zip(x,point)); v=a.subs(sub); dv=a.jacobian(x).subs(sub)
    g=gam.subs(sub); dg=s.Matrix([s.diff(gam,z).subs(sub) for z in x])
    H=g*s.eye(3)+v*v.T; I=H.inv(); S=1+v.dot(v)/g
    dH=[dg[k]*s.eye(3)+dv[:,k]*v.T+v*dv[:,k].T for k in range(3)]
    G=[s.Matrix(3,3,lambda i,j:sum(I[k,l]*(dH[j][l,i]+dH[i][l,j]-dH[l][i,j])/2 for l in range(3))) for k in range(3)]
    # M = sqrt(S) * T; mean derivative b_y cancels between endpoints.
    T=-(dv+dv.T)/2+sum((v[k]*G[k] for k in range(3)),s.zeros(3))
    U=I*T; tr=s.trace(U)
    q=s.factor(S*(s.trace(U*U)+tr**2))  # M_tt=tr_H M_spatial, B=0
    assert q>=0
    return q,S


def main():
    j=-s.Rational(6,5); n=s.symbols('n',real=True); L=2*s.log(2)
    ref=4*s.tanh(n-s.log(2))
    assert s.simplify(s.diff(ref,n)-4+ref**2/4)==0
    assert s.simplify(ref.subs(n,0)-2*j)==0
    assert s.simplify(ref.subs(n,L)+2*j)==0
    # Difference equation and reciprocal comparison integral, checked exactly.
    a,b,z=s.symbols('a b z',real=True)
    assert s.expand((4-a*a/4)-(4-b*b/4-z)+(a+b)*(a-b)/4-z)==0
    assert s.simplify(s.diff(s.atanh(a/4),a)*(4-a*a/4-z)-(1-z/(4-a*a/4)))==0
    # Zero-amplitude periodic warped Einstein comparator: Ric(h_base)=-3 h0^2 h_base.
    b0=s.Rational(4,5)*s.cosh(n-s.log(2))
    assert s.simplify(-4*s.diff(b0,n,2)/b0+4)==0
    assert s.simplify(-3*s.Rational(4,5)**2/b0**2-s.diff(b0,n,2)/b0-3*(s.diff(b0,n)/b0)**2+4)==0
    # Exact trace/shape density equations from the mixed normal Einstein operator.
    A=s.diag(*s.symbols('A0:4')); R=s.Matrix(4,4,s.symbols('R0:16'))
    tau=s.trace(A); Aprime=R+4*s.eye(4)-tau*A
    tf=lambda M:M-s.trace(M)*s.eye(4)/4
    assert (tf(Aprime)+tau*tf(A)-tf(R)).applyfunc(s.expand)==s.zeros(4)
    assert s.expand(s.trace(Aprime)+tau*tau-s.trace(R)-16)==0
    # Lorentz self-adjoint A can have negative shear norm away from time reflection.
    h=s.diag(-1,1,1,1); M=s.zeros(4); M[0,1]=M[1,0]=1
    assert s.trace(h.inv()*M)==0 and s.trace((h.inv()*M)**2)==-2
    print('PASS comparator, signed Riccati difference, integral and indefinite negative control',flush=True)
    for pt in ((s.Rational(1,5),0,0),(s.Rational(1,5),s.Rational(1,10),0),(0,0,0)):
        vals=[exact_seed(pt,eps) for eps in (s.Rational(1,40),-s.Rational(1,40),0)]
        assert vals[0]==vals[1] and vals[2]==(0,1)
        print('point',pt,'q',vals[0][0], 'q_float',float(vals[0][0]),'S',vals[0][1],flush=True)
    assert exact_seed((s.Rational(1,5),0,0),s.Rational(1,40))[0]>0
    print('PASS exact nonzero source shear on both signed amplitudes; zero comparator retained',flush=True)

if __name__=='__main__':main()

"""Moving scalar constitutive closure and Ward compatibility; not coercivity."""
import sympy as s

def exact():
    t=s.symbols('t',positive=True); b=1/t; k=s.symbols('k',real=True); q=s.I*k*b
    B=s.sqrt(1+b*b); K=s.Function('K')(t); w=s.Function('w')(t)
    f,l,X,Y,W,lam,ln,Yn,j0,jx,jy,jm,R0,Rx,u,v=[s.Function(a)(t) for a in ('f','l','X','Y','W','lam','ln','Yn','j0','jx','jy','jm','R0','Rx','u','v')]
    dt=lambda a:s.diff(a,t)
    # Induced metric, not the wall-fixed metric; mixed tangent metric zero.
    L=l+2*f/B; J=X+2*Y-6*B*f
    D=q*v-J/2; A=dt(u)+L/2; V=dt(v)-b*v
    rho=w*D+K*A-3*b*K*u
    p=w*D/3+K*A+(dt(K)+3*b*K)*u
    rho_g=(B*B-1)*f-B*lam/2-b*W-Yn/2-b*dt(f)+jy
    mixed=q*(W/2+dt(f)-b*f)
    # K^0_x=-3 T^0_x+j_m, T^0_x=-w V-K grad u.
    U=s.solve(rho-rho_g,dt(u))[0]
    Vrate=s.solve(mixed-3*(w*V+K*q*u)-jm,dt(v))[0]
    P=s.simplify(p.subs(dt(u),U))
    acc=(2*B*B-3+B**-2)*f-2*b*dt(f)-(B+1/(2*B))*lam-2*b*W-dt(W)-Yn+ln/2+3*P+j0+2*jy
    assert s.simplify((rho-rho_g).subs(dt(u),U))==0
    assert s.simplify((mixed-3*(w*V+K*q*u)-jm).subs(dt(v),Vrate))==0
    assert s.simplify(P-rho_g+2*w*D/3-(dt(K)+6*b*K)*u)==0
    # Ward rows (source convention: divergence of unknown + known = 0).
    clock=dt(u).diff(t)+(3*b+dt(K)/K)*dt(u)-q*q*u+3*b*b*u+(dt(L)+dt(J))/2+(3*b+dt(K)/(2*K))*L-R0/K
    fluid=dt(v).diff(t)-b*dt(v)+b*b*v-q*(q*v/3-J/6-L/2)-Rx/(t*w)
    def close(expr):
        expr=expr.subs({dt(u).diff(t):dt(U),dt(v).diff(t):dt(Vrate)},simultaneous=True)
        expr=expr.subs({dt(u):U,dt(v):Vrate,dt(f).diff(t):acc},simultaneous=True)
        return s.expand(expr)
    C0,Cx=close(clock),close(fluid)
    # Reverse direction is an exact differential-algebraic identity.
    # Residuals for arbitrary histories, including nonzero forcing.
    assert not C0.has(dt(u).diff(t),dt(v).diff(t),dt(f).diff(t))
    assert not Cx.has(dt(u).diff(t),dt(v).diff(t),dt(f).diff(t))
    assert s.diff(C0,R0)==-1/K and s.diff(Cx,Rx)==-1/(t*w)
    # No inverse wave number in the wall constitutive reconstruction.
    assert all(not a.subs(k,0).has(s.zoo,s.nan) for a in (U,Vrate,P,acc,C0,Cx))
    # Trace obstruction: H^1 bulk energy controls Z, not trace of Z_t in L2.
    # v_n(n)=sqrt(N) exp(-N n); integral v_n^2=1/2 but v_n(0)^2=N.
    N=s.symbols('N',positive=True); n=s.symbols('n',nonnegative=True)
    vel=s.sqrt(N)*s.exp(-N*n)
    assert s.integrate(vel**2,(n,0,s.oo))==s.Rational(1,2)
    assert vel.subs(n,0)**2==N
    print('9 grouped checks PASS; scalar wall DAE, Ward residuals and trace obstruction')
    return U,Vrate,acc,C0,Cx

if __name__=='__main__': exact()

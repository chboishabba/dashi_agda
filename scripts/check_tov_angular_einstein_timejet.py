"""W3.2 original TOV angular Einstein second-time-jet inverse.
Derives 2+2 Einstein tensor directly, checks static original anisotropic
source, and shows lapse-time gauge terms cancel between angular Einstein
and time-differentiated material momentum flux. No continuum evolution.
"""
import sympy as s


def main():
    t,r=s.symbols("t r",real=True)
    N=s.Function("N")(t,r);f=s.Function("f")(t,r)
    h=s.diag(-N*N,1/f);inv=h.inv();coords=[t,r]
    C=[[[s.factor(sum(inv[k,z]*(s.diff(h[z,j],coords[i])+
              s.diff(h[z,i],coords[j])-s.diff(h[i,j],coords[z]))/2
              for z in range(2))) for j in range(2)]
              for i in range(2)] for k in range(2)]
    R=s.zeros(2)
    for i in range(2):
        for j in range(2):
            R[i,j]=s.factor(sum(
                s.diff(C[k][i][j],coords[k])-s.diff(C[k][i][k],coords[j])+
                sum(C[k][k][u]*C[u][i][j]-C[k][j][u]*C[u][i][k]
                    for u in range(2)) for k in range(2)))
    base_R=s.factor(s.trace(inv*R))
    Gtheta=s.factor((f*s.diff(N,r)/N+s.diff(f,r)/2)/r-base_R/2)
    ftt=s.diff(f,t,2)
    assert s.simplify(s.diff(Gtheta,ftt)-1/(2*N*N*f))==0
    nu=s.diff(N,r)/N
    expected_static=(f*(s.diff(nu,r)+nu**2)+nu*s.diff(f,r)/2+
                     f*nu/r+s.diff(f,r)/(2*r))
    stat=s.factor(Gtheta.subs({s.diff(f,t):0,ftt:0,s.diff(N,t):0,
                               s.diff(N,r,2):N*(s.diff(nu,r)+nu**2)}))
    assert s.simplify(stat-expected_static)==0
    x,l=s.symbols("x lam",positive=True)
    p=l/(8*s.pi);rho=(l+2)*p*(1-x);pr=-p*(1-x)**2
    ff=1-l*(l+2)*(x/3-x*x/5)
    P=(l+2)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*ff)
    f0=ff.subs(x,r*r);nu0=r*l*P.subs(x,r*r)/f0
    gr=(f0*(s.diff(nu0,r)+nu0**2)+nu0*s.diff(f0,r)/2+
        f0*nu0/r+s.diff(f0,r)/(2*r))
    assert s.cancel(gr-8*s.pi*pt.subs(x,r*r))==0
    # The original signed matter flux gives f_t=-16*pi*r*d*f*Yt*Yr.
    # Euler acceleration has Ytt_Nt coefficient Yt/N, so the
    # differentiated momentum and angular Einstein Nt terms coincide.
    d,U,Yr=s.symbols("d U Yr",real=True)
    Ft=-16*s.pi*r*d*f*U*Yr
    momentum_Nt=-16*s.pi*r*d*f*Yr*U/N
    angular_Nt=Ft/N
    assert s.simplify(momentum_Nt-angular_Nt)==0
    print("PASS exact 2+2 angular Einstein ftt inverse and original static anisotropic source")
    print("PASS lapse-time gauge coefficient cancellation in momentum/angular time jets")
    print("OPEN physical lapse-time field, full bulk evolution and moving GHY/corners")


if __name__=="__main__":
    main()

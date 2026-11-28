"""W2.6 original TOV Euler surface obstruction on a frozen spatial slice.
Y=r, f=f0, N=N0, but Y_t !=0: the nonlinear Euler boundary residue is
nonzero even for bounded Y_tt, N_t and f_t. NOT a general moving-solution
no-go; O(velocity²) spatial/metric initial corrections may change it.
"""
import sympy as s
def zero(z):
    assert s.factor(s.cancel(z))==0,s.factor(z)
def main():
    x,r,l,sd=s.symbols('x r lam Sdot',positive=True)
    p=l/(8*s.pi);rho=(l+2)*p*(1-x);pr=-p*(1-x)**2
    f=1-l*(l+2)*(x/3-x*x/5)
    P=(l+2)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f)
    a=(rho+pt)/2;d=(rho+pr)/(2*f);V=rho-2*a-d*f
    f0=f.subs(x,r*r);d0=d.subs(x,r*r);dx=s.diff(d,x).subs(x,r*r)
    Y,Yr,Yt,Ytt,F,N,Nt,Ft=s.symbols('Y Yr Yt Ytt F N Nt Ft',real=True)
    W=d.subs(x,Y**2)*(F*Yr**2-Yt**2/N**2)+2*a.subs(x,Y**2)*Y**2/r**2+V.subs(x,Y**2)
    # Euler=W_Y-D_r(W_Yr)-D_t(W_Yt)-alpha*W_Yr-beta*W_Yt.
    nu=r*l*P.subs(x,r*r)/f0
    alpha=2/r+nu-s.diff(f0,r)/(2*f0)
    base={Y:r,Yr:1,F:f0}
    wsp=W.subs(Yt,0)
    original=s.diff(wsp,Y).subs(base)-s.diff(s.diff(wsp,Yr).subs(base),r)-alpha*s.diff(wsp,Yr).subs(base)
    zero(original)
    DYt=s.diff(W,Yt)
    timederiv=(s.diff(DYt,Y)*Yt+s.diff(DYt,Yr)*s.symbols('Yrt')+
               s.diff(DYt,Yt)*Ytt+s.diff(DYt,F)*Ft+s.diff(DYt,N)*Nt)
    beta=Nt/N-Ft/(2*F)
    spatial=s.diff(W,Y).subs(base)-s.diff(s.diff(wsp,Yr).subs(base),r)-alpha*s.diff(wsp,Yr).subs(base)
    EL=s.factor(spatial-timederiv.subs(base)-beta.subs(F,f0)*DYt.subs(base))
    expected=(2*r*dx*Yt**2+2*d0*Ytt-2*d0*Yt*Nt/N-d0*Yt*Ft/f0)/N**2
    zero(EL-expected)
    u=-r*(l+2)/(l+1+r*r)*sd
    assert d0.subs(r,1)==0
    surface=s.factor(EL.subs({Yt:u,Ytt:s.Symbol('acc'),Nt:0,Ft:0,N:s.sqrt(f0.subs(r,1))}).subs(r,1))
    target=-225*l*(l+2)*sd**2/(8*s.pi*(2*l*l+4*l-15)**2)
    zero(surface-target)
    assert s.factor(surface.subs({l:s.Rational(1,10),sd:1}))!=0
    zero(surface.subs(sd,0))
    required=-r*dx*u**2/d0
    zero(s.limit((1-r)*required/sd**2,r,1,dir='-')-s.Rational(1,2))
    print('PASS full frozen-slice Euler jet and exact moving-surface obstruction')
    print('PASS restricted bounded-acceleration no-go; corrected O(v²) data OPEN')
    print('SURFACE_EL=',surface)
if __name__=='__main__':main()

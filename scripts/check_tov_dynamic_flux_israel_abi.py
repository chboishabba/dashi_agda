"""W2.1 time-dependent polar-areal Einstein radial energy flux / Israel ABI.
Metric ds^2=-N(t,r)^2dt^2+dr^2/f(t,r)+r^2dOmega^2.
Uses spherical Einstein radial and mixed equations. No bulk existence/GHY.
"""
import sympy as s

def eq(x):
    assert s.simplify(s.factor(x)) == 0, s.factor(x)

def main():
    r,t=s.symbols('r t',positive=True)
    N=s.Function('N')(t,r);f=s.Function('f')(t,r)
    v,a=s.symbols('v a',real=True)
    ut=s.sqrt(f+v*v)/(N*s.sqrt(f))
    # Exact nonstationary 2D Christoffel symbols, computed from metric.
    base=s.diag(-N*N,1/f);inv=base.inv();xx=(t,r)
    Gamma=lambda k,i,j:s.simplify(sum(inv[k,l]*(s.diff(base[l,j],xx[i])+s.diff(base[l,i],xx[j])-s.diff(base[i,j],xx[l]))/2 for l in range(2)))
    eq(Gamma(1,0,0)-f*N*s.diff(N,r))
    eq(Gamma(1,0,1)+s.diff(f,t)/(2*f))
    eq(Gamma(1,1,1)+s.diff(f,r)/(2*f))
    ar=a+Gamma(1,0,0)*ut**2+2*Gamma(1,0,1)*ut*v+Gamma(1,1,1)*v*v
    Ktau=ar/s.sqrt(f+v*v)
    expected=(a+(f+v*v)*s.diff(N,r)/N-s.diff(f,r)*v*v/(2*f)-s.diff(f,t)*ut*v/f)/s.sqrt(f+v*v)
    eq(Ktau-expected)
    # Warped product Ricci_tr: R_tr = Ricci(base)_tr+2 Gamma^r_tr/r.
    # Ricci_2D(tr)=R_2D*g_tr/2=0, hence G_tr=-f_t/(r*f).
    Gtr=-s.diff(f,t)/(r*f)
    m=s.Function('m')(t,r);j=s.symbols('j',real=True)
    # Original signed Eulerian radial flux j := -T_{tr}sqrt(f)/N.
    Ttr=-N*j/s.sqrt(f)
    ft=8*s.pi*r*N*s.sqrt(f)*j
    eq(Gtr.subs(s.diff(f,t),ft)-8*s.pi*Ttr)
    eq(s.diff(1-2*m/r,t).subs(s.diff(m,t),-4*s.pi*r*r*N*s.sqrt(f)*j)-ft)
    # On a common two-face wall f,N,v,a agree. Exterior vacuum.
    rho,p=s.symbols('rho p_r',real=True)
    fr_ext=2*m/r**2
    fr_int=2*m/r**2-8*s.pi*r*rho
    Nr_ext=m/(r*r*f)
    Nr_int=(m+4*s.pi*r**3*p)/(r*r*f)
    def kt(nu,fr,fdot):
        return (a+(f+v*v)*nu-fr*v*v/(2*f)-fdot*ut*v/f)/s.sqrt(f+v*v)
    jump=s.factor(kt(Nr_int,fr_int,ft)-kt(Nr_ext,fr_ext,0))
    target=4*s.pi*r*((f+v*v)*p+v*v*rho-2*v*s.sqrt(f+v*v)*j)/(f*s.sqrt(f+v*v))
    eq(jump-target)
    # Normal-frame signed traction in the wall's local Lorentz frame.
    normal_stress=((f+v*v)*p+v*v*rho-2*v*s.sqrt(f+v*v)*j)/f
    eq(jump-4*s.pi*r*normal_stress/s.sqrt(f+v*v))
    # Reverse no-shell: pressure must cancel both density and flux.
    prest=s.solve(s.Eq(jump,0),p)[0]
    eq(prest+(v*v*rho-2*v*s.sqrt(f+v*v)*j)/(f+v*v))
    eq(jump.subs({p:0,rho:0,j:0}))
    assert s.simplify(jump.subs({p:0,rho:0,j:1,v:1}))!=0
    assert s.simplify(jump.subs({p:0,rho:1,j:0,v:1}))!=0
    # Static wall v=0: only radial pressure is visible in Ktau; density
    # and flux terms decouple, but original field constraints remain.
    eq(jump.subs(v,0)-4*s.pi*r*p/s.sqrt(f))
    print('PASS nonstationary Christoffel/normal and original radial Einstein flux source')
    print('PASS exact moving Israel normal traction, reverse pressure and flux negative controls')
    print('OPEN actual common metric pullback, full time-dependent Einstein-matter bulk and GHY/corners')

if __name__=='__main__':main()

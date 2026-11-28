"""W2 exact moving timelike spherical two-face Israel source ABI.
Static polar-areal metrics on each face, common proper-time R(tau), v and a.
Necessary no-shell junction identity; NOT time-dependent Einstein evolution/GHY.
"""
import sympy as s

def zero(expr):
    assert s.factor(s.cancel(expr)) == 0, s.factor(expr)

def main():
    r, f, N, Nr, fr, v, a = s.symbols('r f N N_r f_r v a', positive=True)
    # Exact radial geodesic-acceleration formula for a moving timelike wall.
    U_t=s.sqrt(f+v*v)/(N*s.sqrt(f))
    ar=a+f*N*Nr*U_t**2-fr*v*v/(2*f)
    Kt=(a+(f+v*v)*Nr/N-fr*v*v/(2*f))/s.sqrt(f+v*v)
    Ktheta=s.sqrt(f+v*v)/r
    zero(ar/s.sqrt(f+v*v)-Kt)
    # Derive proper-time lapse and normal in the original metric.
    zero(-N*N*U_t**2+v*v/f+1)
    n_t=-N*v/s.sqrt(f)
    n_r=s.sqrt(f+v*v)/f
    zero(-n_t*n_t/(N*N)+f*n_r*n_r-1)
    zero(n_t*U_t+n_r*v)
    # Reconstruct both sides from the SAME mass and the original
    # Einstein source equations. Exterior rho=p_r=0.
    m, rho, p=s.symbols('m rho p_r',real=True)
    f0=1-2*m/r
    fp_ext=2*m/r**2
    fp_int=2*m/r**2-8*s.pi*r*rho
    nu_ext=m/(r*r*f0)
    nu_int=(m+4*s.pi*r**3*p)/(r*r*f0)
    def temporal(nu,fp):
        return (a+(f0+v*v)*nu-fp*v*v/(2*f0))/s.sqrt(f0+v*v)
    delta=s.factor(temporal(nu_int,fp_int)-temporal(nu_ext,fp_ext))
    formula=4*s.pi*r*((f0+v*v)*p+v*v*rho)/(f0*s.sqrt(f0+v*v))
    zero(delta-formula)
    assert s.factor(delta.subs({rho:0,p:0}))==0
    # Reverse: no-shell moving temporal Israel compatibility fixes p.
    prequired=-v*v*rho/(f0+v*v)
    zero(delta.subs(p,prequired))
    assert s.factor(delta.subs({rho:0,p:1}))!=0
    assert s.factor(delta.subs({rho:1,p:0,v:1}))!=0
    # Original TOV rho, radial pressure vanish on the material level set.
    lam=s.symbols('lam',positive=True)
    pp=lam/(8*s.pi)
    rhot=(2+lam)*pp*(1-r*r)
    pt=-pp*(1-r*r)**2
    zero(formula.subs({rho:rhot,p:pt}).subs(r,1))
    # Nonzero velocity/acceleration does not spoil equality on that face.
    # But density and pressure off the physical level set cannot be dropped.
    witness=s.factor(formula.subs({rho:rhot,p:pt,lam:s.Rational(1,10),r:s.Rational(9,10),m:s.Rational(7,500),v:s.Rational(1,10)}))
    assert witness!=0
    print('PASS exact moving spherical normal, Ktau/Ktheta and source-derived Israel jump')
    print('PASS reverse traction condition; nonzero density/pressure counterexamples')
    print('OPEN time-dependent g_tr and lapse jets, full Einstein evolution, GHY/corners')

if __name__=='__main__':main()

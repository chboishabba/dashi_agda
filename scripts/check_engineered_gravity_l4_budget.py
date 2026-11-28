"""Coarse P1 budgets for all ten gravity routes; conditional, not device bounds.
Natural units for field models; explicit SI comparator where specified.
"""
import sympy as s
from fractions import Fraction as F


def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)


def main():
    # A: passive attenuation of independent positive baseline channels.
    t,u,T,S=s.symbols('t u T S',nonnegative=True)
    total=T+S; residual=t*T+u*S
    eq((total-residual)/total,(T*(1-t)+S*(1-u))/total)
    eq(((total-residual)/total).subs({t:1,u:0,S:T/3}),s.Rational(1,4))
    # B: finite disk field-to-tidal tradeoff; positive magnitude branch.
    R,z,G,g=s.symbols('R z G g',positive=True)
    sigma=s.symbols('sigma',real=True)
    a=2*s.pi*G*sigma*(1-z/s.sqrt(z*z+R*R))
    sigstar=g/(2*s.pi*G*(1-z/s.sqrt(z*z+R*R)))
    eq(a.subs(sigma,sigstar),g)
    eq(-s.diff(a,z)/a,(s.sqrt(z*z+R*R)+z)/(z*z+R*R))
    # C: massive scalar acceleration has larger relative gradient than massless.
    m,b,Q=s.symbols('m b Q',positive=True)
    a=b*Q*s.exp(-m*z)*(1+m*z)/z**2
    eq(-s.diff(a,z)/a,2/z+m*m*z/(1+m*z))
    # D: complete stationary weak-field source: pressure monopole cancels.
    E,P=s.symbols('E P',real=True); c=s.Integer(299792458)
    eq(((E+P)/c**2).subs(P,0),E/c**2)
    # E: coherent material source energy cannot be omitted from total.
    I1,I2,w1,w2=s.symbols('I1 I2 w1 w2',positive=True)
    Ekin=(I1*w1*w1+I2*w2*w2)/2
    L=I1*w1+I2*w2
    eq(Ekin-L*L/(2*(I1+I2)),I1*I2*(w1-w2)**2/(2*(I1+I2)))
    # F: passive two-port conversion ceiling, arbitrary positive loss rates.
    C=s.symbols('C',positive=True);eta=s.symbols('eta',nonnegative=True)
    trans=eta*4*C/(1+C)**2
    eq(eta-trans,eta*(C-1)**2/(C+1)**2)
    # G: static spherical lapse receiver. A prescribed a fixes the pressure
    # only AFTER mass profile is specified; cannot infer arbitrary low energy.
    r,mu,acc=s.symbols('r mu acc',positive=True)
    f=s.symbols('f',positive=True)
    pr=2*s.sqrt(f)*acc/r-2*mu/r**3
    eq(pr.subs(acc,(pr+2*mu/r**3)*r/(2*s.sqrt(f))),pr)
    # H: conventional work and reaction; no gravity modification.
    mass,height=s.symbols('mass height',positive=True)
    eq(s.integrate(mass*g,(z,0,height)),mass*g*height)
    # I: finite-wavelength derivative coupling, optimize over coupling strength.
    A,B,K,ap,k,l=s.symbols('A B K ap k l',positive=True)
    D=A*B+ap*l*l/K
    gain=l*k/D
    # Bound |gain| <= k sqrt(K)/(2 sqrt(A B ap)) by square completion.
    eq(D-2*l*s.sqrt(A*B*ap/K),(s.sqrt(A*B)-l*s.sqrt(ap/K))**2)
    opt=s.sqrt(A*B*K/ap)
    eq(s.diff(gain,l).subs(l,opt),0)
    eq(gain.subs(l,opt),k*s.sqrt(K)/(2*s.sqrt(A*B*ap)))
    # J: adjoint residual receiver estimate; finite Euclidean Cauchy control.
    a1,a2,b1,b2=s.symbols('a1 a2 b1 b2',real=True)
    eq((a1*a1+a2*a2)*(b1*b1+b2*b2)-(a1*b1+a2*b2)**2,(a1*b2-a2*b1)**2)
    # SI conventional monopole and canonical conformal-gradient energy scales.
    Gsi=F('6.67430e-11');gsi=F('9.80665');csi=299792458
    mass_si=gsi/Gsi
    gain_si=mass_si/1000
    # canonical phi/M gradient=sqrt(6)g/c²: scalar kinetic energy density
    # c^4/(16 pi G)*(phi/M gradient)^2 = 3g²/(8 pi G)
    energy_density=3*s.Rational(gsi.numerator,gsi.denominator)**2/(8*s.pi*s.Rational(Gsi.numerator,Gsi.denominator))
    assert gain_si>10**8
    print('SI monopole mass kg at 1m:',float(mass_si))
    print('canonical scalar local gradient energy J/m^3:',float(energy_density))
    print('PASS ten scoped L4 budgets; no total energy or physical feasibility certification')

if __name__=='__main__':main()

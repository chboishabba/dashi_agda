"""Source-specific signed receiver inverses for existing static geometries.
Normalized GR units; no calibration or physical mechanism promotion.
"""
import sympy as s


def main():
    r,M,l=s.symbols('r M l',positive=True); F=1-2*M/r
    # Schwarzschild held observer proper acceleration and radial tidal stretch.
    g=M/(r*r*s.sqrt(F)); tide=2*M/r**3
    assert s.simplify(g-(s.sqrt(F)/2*s.diff(s.log(F),r)))==0
    t=s.symbols('t',positive=True)
    assert s.simplify(g.subs(M,t*r**3/2)-t*r/(2*s.sqrt(1-t*r*r)))==0
    # Original TOV family mass and inverse amplitude, not one tunable action.
    mass=l*(2+l)/15
    assert s.simplify(mass.subs(l,s.sqrt(1+15*M)-1)-M)==0
    assert s.diff(mass,l).is_positive
    # A source mass change cannot hide from independent curvature at fixed r.
    assert s.diff(tide,M)==2/r**3
    assert s.simplify(s.diff(g,M)-(1-M/r)/(r*r*F**s.Rational(3,2)))==0
    # Canonical scalar-only shielding model: tensor unchanged, scalar fraction alpha.
    alpha,tau,S=s.symbols('alpha tau S',real=True)
    shield=alpha*(1-tau)/(1+alpha)
    assert s.cancel(shield.subs(tau,1-S*(1+alpha)/alpha)-S)==0
    assert shield.subs({alpha:s.Rational(1,3),tau:0})==s.Rational(1,4)
    assert shield.subs({alpha:s.Rational(1,3),tau:-3})==1
    # Complete cancellation requires reversal rather than passive attenuation here.
    # A neutral geodesic has zero proper acceleration; supported readout is distinct.
    print('PASS original TOV exterior mass/acceleration/tidal inverse and canonical scalar shielding obstruction')
    print('OPEN actual control of a single material action, Earth profile, EM/support discrimination and physical calibration')
if __name__=='__main__':main()

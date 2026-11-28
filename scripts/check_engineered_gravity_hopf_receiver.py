"""Hopf G3 receiver cut, source-specific initial jets, not new KK reduction.
Donor #1554 25a9c7cbb22c, P0T/V/AQ/AI; standard geodesic deviation.
Gaussian normal base frame, time-symmetric initial data. No physical units.
"""
import sympy as s

def eq(a,b=0):
    assert s.simplify(a-b)==0,(a,b)

def main():
    e,p=s.symbols('epsilon psi0',positive=True)
    # Original P0T: B0(0)=8 ez, grad psi=0, Delta psi=-eps² B² psi/12.
    # Radial symmetry fixes all three Hessian entries at centre.
    B=s.Matrix([0,0,8*e])
    F=s.Matrix(3,3,lambda i,j:sum(s.LeviCivita(i,j,k)*B[k] for k in range(3)))
    Hess=-B.dot(B)*s.eye(3)/36
    # P0V4 actual base metric second time jet.
    gdd=F*F.T+4*Hess+2*s.trace(Hess)*s.eye(3)
    tidal=gdd/(2*p*p)
    expected=s.diag(208,208,-80)*e*e/(9*p*p)
    assert (tidal-expected).applyfunc(s.simplify)==s.zeros(3)
    eq(s.trace(tidal),112*e*e/(3*p*p))
    # Sign of tidal acceleration in orthonormal neutral p5=0 base frame:
    # R_i0j0=-gdd_ij/2, relative acceleration=-R^i_0j0 separation.
    # At initial time, coordinate-static normal observers are geodesic.
    phidd=-112*e*e/(3*p)
    # Ric4_00=phi^-1 Hess00 phi (F_0i=0), so trace tidal=-Ric00.
    # P0V4 base acceleration yields trace 112/3 eps²/p²; check directly.
    # A mismatch is a source normalization error, not an exotic effect.
    eq(s.trace(tidal),-phidd/p)
    print('PASS actual source neutral tide and radion trace')

if __name__=='__main__':main()

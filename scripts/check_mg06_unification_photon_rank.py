#!/usr/bin/env python3
"""MG06 source-specific photon multiplicity and geometric-KK mass/charge gate.

Owners: KK E6 TwoVEV, E6 Orbifold and KK Casimir Minkowski Photon Source.
Symbolic finite gauge mass Gram only; not a derived gauge field action.
"""
import sympy as s


def main():
    g2, gy, v, h = s.symbols('g2 gy v h', positive=True)
    # E6-derived Higgs neutral charge covector in the source order (B,W3,Y).
    q = s.Matrix([0, -g2/s.Integer(2), gy/s.Integer(2)])
    M = v*v*q*q.T
    assert M.rank() == 1 and len(M.nullspace()) == 2
    assert M * s.Matrix([1, 0, 0]) == s.zeros(3, 1)
    assert M * s.Matrix([0, gy, g2]) == s.zeros(3, 1)
    # Gravitational graviphoton A_g independent and still massless in this selected fixture.
    q4 = s.Matrix([0, 0, -g2/s.Integer(2), gy/s.Integer(2)])
    M4 = v*v*q4*q4.T
    assert M4.rank() == 1 and len(M4.nullspace()) == 3
    # Remove separate Maxwell B and graviphoton A from the observed low-energy sector.
    qed = s.Matrix([-g2/s.Integer(2), gy/s.Integer(2)])
    Mew = v*v*qed*qed.T
    assert Mew.rank() == 1 and len(Mew.nullspace()) == 1
    assert Mew * s.Matrix([gy, g2]) == s.zeros(2, 1)
    # Giving B a separate mass removes B, but A_g remains another massless vector.
    M4b = M4 + h*h*s.diag(0,1,0,0)
    assert M4b.rank() == 2 and len(M4b.nullspace()) == 2
    # Merely identifying coordinates without a source-side symmetry quotient cannot
    # turn the rank-one 4-field mass Gram into a unique massless photon.
    assert s.simplify(s.trace(M4) - v*v*(g2*g2+gy*gy)/4) == 0
    # Source-specific no-go: KK q_n= sqrt2 n/(M_Pl*b),
    # m_n^2=m5^2+n^2/b^2, so m_n/|q_n| >= M_Pl/sqrt2 for m5^2>=0.
    n, b, mp, m5 = s.symbols('n b mp m5', positive=True)
    m2 = m5*m5+n*n/(b*b)
    charge2 = 2*n*n/(mp*mp*b*b)
    assert s.simplify(m2/charge2-mp*mp/2) == m5*m5*mp*mp*b*b/(2*n*n)
    assert s.simplify((m2/charge2).subs(m5,0)-mp*mp/2) == 0
    print('PASS: E6 EW + independent B gives 2 massless null directions')
    print('PASS: also keeping graviphoton gives 3 null directions')
    print('PASS: EW alone gives 1; massive B with unbroken graviphoton still gives 2')
    print('PASS: periodic pure-KK positive bare mass gives m/|q| >= M_Pl/sqrt(2)')
    print('OPEN: unique physical photon, mixed actions, exact source quotient, anomalies, physical masses')


if __name__ == '__main__':
    main()

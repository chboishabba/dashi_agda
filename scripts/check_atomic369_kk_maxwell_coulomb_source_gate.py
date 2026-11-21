#!/usr/bin/env python3
"""MG06 conditional 5D Maxwell/Dirac zero-mode to Coulomb source audit.

Matches source selections in KK PR #1241: independent 5D Maxwell B_A
(not the metric graviphoton), 5D Dirac mass equal to observed electron
mass INPUT, chosen e5 to reproduce e4. Not physical KK charge generation.
External static point-charge source and nonrelativistic reduction are
explicit additional assumptions; no 5D matter/stress solution claimed.
"""
import sympy as s

def check():
    L, e5, m5, R, Z, radius = s.symbols(
        "L e5 m5 R Z radius", positive=True, real=True
    )
    # Canonically normalised matter and photon zero modes on S1:
    # psi_5=psi_4/sqrt(L); B_5mu=B_4mu/sqrt(L), L=2*pi*R.
    psi_norm = 1 / s.sqrt(L)
    photon_norm = 1 / s.sqrt(L)
    e4 = e5 / s.sqrt(L)
    assert s.simplify(L * psi_norm**2 - 1) == 0
    assert s.simplify(L * photon_norm**2 - 1) == 0
    assert s.simplify(L * psi_norm**2 * photon_norm * e5 - e4) == 0
    assert s.simplify(L * psi_norm**2 * e5 - e4) != 0  # missing B normalization
    # Source-prescribed Dirac mass: n=0 returns m5; it does not predict m5.
    mode0 = s.sqrt(m5**2 + (s.Integer(0) / R)**2)
    mode1 = s.sqrt(m5**2 + (s.Integer(1) / R)**2)
    assert s.simplify(mode0 - m5) == 0
    assert s.simplify(mode1 - m5) != 0

    e4symbol = s.symbols("e4", positive=True, real=True)
    # Independent external static nucleus: 4D Gauss law
    # div E = Z*e4*delta_3; Phi = Z*e4/(4*pi*r) outside source.
    # The electron is assigned q_e=-e4, so V=q_e*Phi.
    phi = Z * e4symbol / (4 * s.pi * radius)
    coulomb = s.simplify(-e4symbol * phi)
    assert s.simplify(coulomb + Z * e4symbol**2 / (4 * s.pi * radius)) == 0
    assert s.simplify(coulomb.subs(e4symbol**2, 4*s.pi) + Z / radius) == 0
    assert s.simplify(coulomb.subs(Z, 0)) == 0  # no nuclear source, no atom
    assert s.simplify(coulomb.subs(e4symbol, -e4symbol) - coulomb) == 0  # both source and electron reverse
    # Distinguish coupling-matched from an alleged predicted electron charge.
    assert e4.free_symbols == {e5, L}
    assert s.simplify(coulomb.subs(e4symbol, e4) + Z*e5**2/(4*s.pi*L*radius)) == 0
    print("PASS zero-mode matter/photon normalizations; Maxwell coupling; mode 0/1 source-mass audit")
    print("PASS conditional Coulomb source and charge/normalization negative controls")
    print("OPEN independent KK graviphoton-to-QED identification; electron mass, e5, source, spin and same-H")
if __name__ == "__main__":
    check()

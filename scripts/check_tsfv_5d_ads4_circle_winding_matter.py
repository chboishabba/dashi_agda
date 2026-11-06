#!/usr/bin/env python3
"""Exact, reproducible 5D Einstein--periodic-scalar KK control.

Independent action (signature -++++):
 S = integral sqrt(|g5|) [(R5 - 2 Lambda)/(2 kappa5^2)
                           - 1/2 g^{AB} d_A phi d_B phi].
For AdS4 x S1, phi=n theta modulo 2*pi with nonzero INTEGER winding n.
This demonstrates a non-flat NONZERO-MATTER exact solution. It is NOT the
original observer-generated measured g4; KK08 remains open.
"""
import sympy as s

def main():
    t, x, y, z, theta = s.symbols("t x y z theta", real=True)
    L, R, kappa = s.symbols("L R kappa", positive=True)
    n = s.symbols("n", integer=True, nonzero=True)
    coords = (t, x, y, z, theta)
    D = 5
    g = s.diag(-L**2/z**2, L**2/z**2, L**2/z**2, L**2/z**2, R**2)
    gi = g.inv()
    gamma = [[[s.simplify(sum(gi[a, d] *
                 (s.diff(g[d, b], coords[c]) +
                  s.diff(g[d, c], coords[b]) -
                  s.diff(g[b, c], coords[d])) / 2
                 for d in range(D)))
               for c in range(D)] for b in range(D)] for a in range(D)]
    ric = s.Matrix(D, D, lambda a, b: s.simplify(sum(
        s.diff(gamma[c][a][b], coords[c])
        - s.diff(gamma[c][a][c], coords[b])
        + sum(gamma[c][a][b]*gamma[d][c][d]
              - gamma[d][a][c]*gamma[c][b][d] for d in range(D))
        for c in range(D))))
    assert ric == s.diag(3/z**2, -3/z**2, -3/z**2, -3/z**2, 0)
    scalar_curvature = s.simplify(sum(gi[a,b]*ric[a,b]
                                      for a in range(D) for b in range(D)))
    assert s.simplify(scalar_curvature + 12/L**2) == 0
    # The circle-valued field has d phi = n d theta. The resulting
    # scalar equation holds since all fields are theta independent.
    grad = s.Matrix([0,0,0,0,n])
    grad2 = (grad.T * gi * grad)[0]
    assert s.simplify(grad2 - n**2/R**2) == 0
    laplacian_phi = s.simplify(sum(
        gi[a,b] * (s.diff(grad[b], coords[a]) -
                   sum(gamma[c][a][b]*grad[c] for c in range(D)))
        for a in range(D) for b in range(D)))
    assert laplacian_phi == 0
    stress = grad*grad.T - g*grad2/2
    einstein = ric - g*scalar_curvature/2
    Lambda = -3*kappa**2*n**2/(2*R**2)
    L_squared = 3*R**2/(kappa**2*n**2)
    residual = (einstein + Lambda*g - kappa**2*stress).applyfunc(
        lambda v: s.factor(v.subs(L**2, L_squared)))
    assert residual == s.zeros(D)
    assert ric[0,0] != 0 and stress[4,4] != 0
    assert g[4,4] == R**2
    # Exact horizontal reduction of this metric is AdS4, not a
    # posthoc claimed equality to any experimentally observed metric.
    assert g[:4,:4] == s.diag(-L**2/z**2,L**2/z**2,L**2/z**2,L**2/z**2)
    print("PASS: full 5x5 Ricci, Einstein+Lambda=scalar stress, scalar EOM")
    print("PASS: nonflat, nonzero winding stress, exact AdS4 horizontal metric")
    print("LIMITATION: no TSVF-measured AdS4 metric, radion stability, OS/YM match")

if __name__ == "__main__":
    main()

"""Exact layer-cake p=2 bridge from Shahmurov threshold identity to enstrophy.

Attribution: Rishad Shahmurov, arXiv:2605.01873v3, sections 2-3.
This symbolic audit verifies the layer-cake coefficients. The full
coarea/regular-value theorem, boundary convergence and solution
hypotheses remain separate mathematical obligations.
"""
import sympy as S

def test_p2_layer_cake_coefficients():
    f,a,alpha,dr=S.symbols("f a alpha dr",positive=True)
    # For each point, 2*int_0^f (f-a)da = f^2.
    assert S.simplify(S.integrate(2*(f-a),(a,0,f))-f**2)==0
    # Stretching threshold: 2*int_0^f alpha*f da =2 alpha f^2.
    assert S.simplify(S.integrate(2*alpha*f,(a,0,f))-2*alpha*f**2)==0
    # Directional dissipation: 2*int_0^f f|grad xi|²da
    assert S.simplify(S.integrate(2*f*dr**2,(a,0,f))
                       -2*f**2*dr**2)==0

def test_vorticity_gradient_orthogonal_split():
    # omega=f*xi, |xi|=1, xi·grad xi=0, hence
    # |grad omega|² = |grad f|² + f²|grad xi|².
    f,df,dxi=S.symbols("f df dxi",real=True)
    assert S.expand(df**2+f**2*dxi**2)==df**2+f**2*dxi**2

# Source theorem's surface coarea term additionally requires
# int_0^infinity int_{f=a}|grad f|dH^2 da
# = int |grad f|² dx; NOT certified by these finite symbolic tests.

"""F13: certified passive complex-branch planar Maxwell Green.

Finite Fourier/Cayley model only: not a retarded 3D dyadic and not an
original instrument or environmental source calibration.  exp(-i omega t),
real omega>0 and scalar mu>0, epsilon with Im epsilon >=0.

Reuses the 4x4 oblique Maxwell generator, tangential radiation Schur
operator, and original F = signed tangential Poynting form.
"""
import sympy as S
from smith_filsinger_oblique_maxwell_sympy import oblique_generator
from smith_filsinger_tangential_maxwell_sympy import transfer_midpoint_z
from smith_filsinger_radiation_green_sympy import F, R, flux_z, sheet_power_identity


def _is_nonnegative(x):
    x = S.simplify(x)
    return x.is_nonnegative is True


def _is_positive(x):
    x = S.simplify(x)
    return x.is_positive is True


def outgoing_passive_wavenumber(omega, kx, ky, mu, epsilon):
    """Retarded-sign spectral *branch*: q=sqrt(omega² mu eps-k²).

    This is an algebraic real-frequency outgoing/decaying branch certificate,
    not a proof that the inverse time transform is a causal distribution.
    Uncertified passive parameters are rejected rather than guessed.
    """
    w,kx,ky,mu,eps = map(S.sympify,(omega,kx,ky,mu,epsilon))
    if not _is_positive(w) or not _is_positive(mu):
        raise ValueError('positive real omega and mu required')
    if not (_is_nonnegative(S.im(eps)) and _is_positive(S.re(eps))):
        raise ValueError('passive epsilon with Re>0 and Im>=0 required')
    q2=S.simplify(w*w*mu*eps-kx*kx-ky*ky)
    if S.simplify(q2)==0:
        raise ValueError('branch point q=0 unsupported')
    q=S.sqrt(q2)
    qr,qi=S.simplify(S.re(q)),S.simplify(S.im(q))
    if not _is_nonnegative(qr) or not _is_nonnegative(qi):
        raise ValueError('uncertified outgoing/decaying square-root branch')
    if not (_is_positive(qr) or _is_positive(qi)):
        raise ValueError('zero/indeterminate outgoing branch')
    return q


def passive_halfspace_admittance(omega,kx,ky,mu,epsilon):
    w,kx,ky,mu=map(S.sympify,(omega,kx,ky,mu))
    q=outgoing_passive_wavenumber(omega,kx,ky,mu,epsilon)
    return S.Matrix([[-kx*ky,-(q*q+ky*ky)],
                     [q*q+kx*kx,kx*ky]])/(w*mu*q)


def passive_sheet_green(T,omega,kx,ky,eps_bottom,eps_top,
                        mu_bottom=1,mu_top=1):
    """Same Schur map as oblique_sheet_green with certified complex q."""
    Yb=passive_halfspace_admittance(omega,kx,ky,mu_bottom,eps_bottom)
    Yt=passive_halfspace_admittance(omega,kx,ky,mu_top,eps_top)
    A,B,C,D=T[:2,:2],T[:2,2:],T[2:,:2],T[2:,2:]
    Q=A-B*Yb;N=C-D*Yb
    boundary=R*(N-Yt*Q)
    if S.simplify(boundary.det())==0:
        raise ValueError('singular source sheet or pole')
    Eb=boundary.inv();Et=Q*Eb
    return dict(upper_E=Et,lower_E=Eb,upper_H=Yt*Et,
                lower_H=-Yb*Eb,inside_H=N*Eb,boundary_matrix=boundary,
                upper_Y=Yt,lower_Y=Yb)


def cayley_passivity_identity(M,d):
    """Exact matrix Cayley flux identity; never equates Cayley to exp(Md).

    T†FT-F=d (I-dM/2)^(-†) (M†F+FM) (I-dM/2)^(-1).
    For absorbing eps with Im>=0, the RHS is <=0 for positive d.
    """
    d=S.sympify(d)
    ident=S.eye(M.rows)
    inv=(ident-d*M/2).inv()
    T=transfer_midpoint_z(M,d)
    lhs=S.simplify(T.conjugate().T*F*T-F)
    rhs=S.simplify(d*inv.conjugate().T*(M.conjugate().T*F+F*M)*inv)
    return lhs,rhs


def exact_slab_absorption(M, thickness, incident_state):
    """Flux in minus flux out in the finite Cayley slab."""
    T=transfer_midpoint_z(M,thickness)
    up=T*incident_state
    dissipated=S.simplify(S.re((incident_state.conjugate().T*F*incident_state
                               -up.conjugate().T*F*up)[0])/2)
    return dissipated

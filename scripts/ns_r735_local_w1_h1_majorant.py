"""Cutoff-uniform *local-time* R735/W1 analytical certificate.

Provenance: classical Leray/Galerkin H1 energy calculus, periodic GN/Sobolev,
M. Riesz rectangle partial-sum and Leray/Riesz L4 multipliers, Holder.
DASHI contribution: same-helical-carrier composition into existing R691/R735 W1.

For real divergence-free mean-zero periodic Galerkin u_N on T3 with the
NORMALIZED physical H+ and H- projectors and actual Leray forcing F_N,

  X_N = ||grad u_N||_2^2, Y_N = ||Delta u_N||_2^2,
  X_N' + nu Y_N <= K nu^(-3) X_N^3.

This yields an explicit cut-off UNIFORM local time for X_N and int(Y_N).
The helical quintic commutator satisfies the standard conditional bound
  |C_N| <= C_W ||u_N||_(H1)^(7/2) ||u_N||_(H2)^(3/2).

This code checks the EXACT symbolic scalar assembly; the functional
inequalities themselves are classical mathematical assumptions, not
proved by numeric examples or a runnable symbolic program.

No arbitrary-time W1, W2, B7, A3 or Clay B claim is made.
"""
from dataclasses import dataclass
import sympy as sp


@dataclass(frozen=True)
class Certificate:
    max_time: sp.Expr
    gradient_ceiling: sp.Expr
    h2_time_integral: sp.Expr
    commutator_time_integral: sp.Expr
    initial_mixed_ceiling: sp.Expr
    weighted_plus_terminal_ceiling: sp.Expr


def local_w1_certificate(E0, D0, nu, K, CW, CM, T):
    """Return exact formulas for E0>=0, D0>0, nu,K,CW,CM>0,
    0 <= T <= nu^3/(4 K D0^2). Uses E0=||u0||² and D0=||grad u0||².
    CW: helical/product/Calderon-Zygmund multiplier constant;
    CM: helical initial product H1 mass ceiling constant.
    No numerical values for analytic constants are fabricated.
    """
    sqrt2 = sp.sqrt(2)
    lifetime = nu**3/(4*K*D0**2)
    Xmax = sqrt2*D0
    # H2(inhomogeneous)^2 = E + 2X + Y on the normalized torus.
    Yint = (D0 + K*nu**(-3)*Xmax**3*T)/nu
    H2int = T*(E0 + 2*Xmax) + Yint
    # H1^2=E+X; Holder integral H2^(3/2) <= T^(1/4)(int H2²)^(3/4).
    Cint = CW*(E0+Xmax)**sp.Rational(7,4)*T**sp.Rational(1,4)*H2int**sp.Rational(3,4)
    M0 = CM*(E0+D0)**2
    return Certificate(lifetime,Xmax,H2int,Cint,M0,M0+Cint)


def scalar_ode_supersolution(D0, nu, K, t):
    """Exact comparison solution for X' <= K nu^-3 X³."""
    return D0/sp.sqrt(1-2*K*D0**2*t/nu**3)


if __name__ == '__main__':
    e,d,n,k,cw,cm,t = sp.symbols('E0 D0 nu K CW CM T',positive=True)
    print(local_w1_certificate(e,d,n,k,cw,cm,t))


@dataclass(frozen=True)
class SmallDataCertificate:
    gradient_smallness_threshold: sp.Expr
    h2_infinite_time_integral: sp.Expr
    commutator_infinite_time_integral: sp.Expr
    initial_mixed_ceiling: sp.Expr
    weighted_plus_terminal_ceiling: sp.Expr


def small_data_global_w1_certificate(E0, D0, nu, K, CW, CM):
    """Uniform-for-all-T/N *restricted small-H1 data* physical W1 ceiling.

    Requires periodic mean-zero, D0<=nu²/sqrt(2K), actual physical
    Galerkin NS, normalized helical projections. From Y>=X and
    X'+nu Y<=K nu^-3 X³ infer X'+(nu/2)Y<=0, hence
    X(t)<=D0 exp(-nu*t/2). Standard kinetic energy decay gives
    E(t)<=E0 exp(-2nu*t), and int H2² <= (3E0/2+2D0)/nu.
    Holder with the H1 exponential weight closes the infinite-time
    integral of the physical quintic commutator. This is CLASSICAL
    SMALL DATA, not unrestricted B or a closure of R735 W2.
    """
    threshold = nu**2/sp.sqrt(2*K)
    H2total = (sp.Rational(3,2)*E0+2*D0)/nu
    Ctotal = CW*(E0+D0)**sp.Rational(7,4)*(sp.Rational(2,7)/nu)**sp.Rational(1,4)*H2total**sp.Rational(3,4)
    initial = CM*(E0+D0)**2
    return SmallDataCertificate(threshold,H2total,Ctotal,initial,initial+Ctotal)


@dataclass(frozen=True)
class EventualTailCertificate:
    enstrophy_threshold: sp.Expr
    averaging_start: sp.Expr
    common_entry_time: sp.Expr
    universal_tail_energy_ceiling: sp.Expr
    universal_tail_W1_ceiling: sp.Expr


def eventual_all_data_tail_w1_certificate(E0, nu, K, CW, CM):
    """Cutoff-uniform W1 from a common LATE TIME for ALL periodic data.

    Assumes unforced mean-zero 2π periodic Galerkin NSE, E0>0 and nu,K>0.
    This follows the CLASSICAL eventual regularity/absorbing-ball
    argument, not a new global regularity theorem.

    Energy E_N(t)<=E0*exp(-2nu*t) (Poincare). Choose averaging
    window [t0,t0+1/nu] with E_N(t0)<=2d, d=nu²/sqrt(2K).
    Energy identity gives int X <= E_N(t0)/(2nu)<=d/nu.
    Hence for each cutoff N a time s_N in that COMMON window
    satisfies X_N(s_N)<=d. Invariance of the small-H1 region
    proves X_N(Tentry)<=d simultaneously for all N, where
    Tentry=t0+1/nu. E_N(Tentry)<=2d*exp(-2) uniformly.

    Applying the already-available small_data_global_w1_certificate
    to the SHIFTED physical trajectory yields
      [W_N(T)-W_N(Tentry)] + E_M,N(T) <= universalTailBound
    for all N, T>=Tentry. This is a bound on the physical selected
    output W1 TAIL, NOT on W_N(T) from time 0 or on W2.
    """
    threshold=nu**2/sp.sqrt(2*K)
    t0=sp.Max(sp.Integer(0),sp.log(E0/(2*threshold))/(2*nu))
    common_entry=t0+1/nu
    energy_tail=2*threshold*sp.exp(-2)
    small=small_data_global_w1_certificate(energy_tail,threshold,nu,K,CW,CM)
    return EventualTailCertificate(threshold,t0,common_entry,
                                   energy_tail,small.weighted_plus_terminal_ceiling)

# RH G3 — quartic signed cone exact geometry, 14 Nov 2026

## Reuse the true theorem owners

The original Agda master already contains:
- DASHI/Analysis/RiemannQuarticSignedPoleCompensationExact.agda,
  whose LocalDebt, SignedCompensation, global cofinal-limit and
  strict-residual *compilers* exist and whose eventual strict
  compensation gap remains an OPEN analytic obstruction.
- DASHI/Analysis/RiemannQuarticSignedPoleConeDebtExact.agda,
  with the cone/good/far source split, mixed local quartic jet,
  canonical radius and zero-count cone-envelope inequalities.
- DASHI/Analysis/RiemannQuarticSignedPoleFrontierExact.agda,
  which explicitly forbids upgrading those compilers into a
  proof of the global Riemann hypothesis.

Do not duplicate paid scalar/cofinal-assembly lemmas or replace
FarExact with an arbitrary absolute-value allowance.

## Exact quartic geometry: both signs lie *inside* the mixed cone

The existing leading signed quartic source is

  Q(alpha,q)=alpha²*q²-(alpha⁴+q⁴)/6.

For alpha!=0, set r=(q/alpha)². Then

  6Q(alpha,q)/alpha⁴ = 6r - 1 - r².

The mixed cone has 0<=r<=6. Within that same cone:
- q=0 gives Q=-alpha⁴/6<0 (favorable negative core);
- q=alpha gives Q=(2/3)*alpha⁴>0 (unfavorable positive lobe);
- q=(2449/1000)*alpha is still inside the cone but Q<0;
- the maximum is at r=3, with 6Q/alpha⁴=8.

Therefore any proof that takes the absolute value over the
entire cone discards real signed cancellation; nor may one claim
the entire cone is negative. These statements are exact
quartic-polynomial results; they are NOT claims about existence
of zeta zeros with the prescribed (alpha,q), not estimates on
the full nonpolynomial pair kernel.

For every rational alpha=1/n, n>=1, q=0 and q=alpha produce
these opposite signs and all quartic terms shrink as alpha⁴.
In particular the strip restriction 0<|alpha|<=1/2 by itself
does not yield a positive lower bound of order alpha⁴.
This is a structural warning against scalar estimates with
an implicit uniform horizontal-distance floor.

Independent exact-rational regression:
  python3 scripts/check_rh_g3_quartic_signed_cone_geometry.py

## True unchanged strict G3 analytic cut

Let

  LocalDebt_n = ConeDebt_n + LocalRemainderDebt_n,
  SignedCompensation_n = GoodQuarticGain_n - FarExact_n,
  T_W(rho) = 4*D_comb(rho) + integral Psi_t*mu.

The original source compiler consumes the actual
eventual signed inequality, for some eps>0 and N,

  for all n>=N:
    LocalDebt_n - SignedCompensation_n <= T_W(rho)-eps.

The chosen sharpened cone gain route adds favorable negative
cone mass while preserving FarExact sign.

**Nothing here supplies the above eventual gap.** To close it
one needs an actual theorem on the canonical cofinal zeta-zero
exhaustion with controlled signed near/far mass, including all
zeros and the original completed-residual limit. An artificial
pair of rational alpha,q is not an admissible zero configuration.
The Riemann hypothesis and RH G3 stay OPEN.

All checks here are exact-rational code tests; no Agda or Lean
kernel receipt was produced. Preserve this status in the
eleven-lane source ledger, and avoid false equivalence between
a finite quartic model and global analytic zeta constraints.

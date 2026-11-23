# RH G3 — quartic signed cone exact geometry, 14 Nov 2026

## 22 November 2026 — both horizontal half-strips, exact reflection and strict nonpromotion

This is an update to the **original G3 signed-cone source owner**, not a
parallel RH/GRH theorem or a replacement pole–quotient route.
The existing `scripts/check_rh_g3_quartic_signed_cone_geometry.py`
has been extended in place on Agda #1533 (commit `8b699b99`)
to check both `α=Re(s)−1/2>0` and the mirror `−α<0` for the SAME
original quartic
`Q(α,q)=α²q²−(α⁴+q⁴)/6`.
The exact identities are:

```text
left real part = 1/2−α; right real part = 1/2+α
signed pair (α)+(−α) = 0
even-defect pair α²+(−α)² = 2α²
Q(−α,q) = Q(α,q)
Q(α,0) = −α⁴/6 < 0 (α ≠ 0)
Q(α,α) = 2α⁴/3 > 0 (α ≠ 0).
```

**Local mathematical verification:** independent Python Fraction
and SymPy 1.14.0 symbolic calculations PASS on 20 sign-reflected
`(α,q)` pairs over denominators `2,3,11,1000,1000000`.
The original 30 rational signed-cone samples and sign-state
positive/negative controls remain in the committed checker.
The revised script was read back from GitHub (committed blob
`561638cdd8eef70c4e1b6f6c142609ae5177bd19`);
the **full fetched revised Python file was not executed end-to-end**
in this runtime, so the local receipt covers the exact replicated
mathematical assertions rather than claiming a new full-file
or kernel run.

An explicit **non-ζ countermodel** is
`f(s)=(s−1/4)(s−3/4)`: `f(1−s)=f(s)`
yet both its zeros are OFF the critical line. It refutes
the general inference "functional-equation symmetry alone
implies RH", without claiming those are ζ zeros.
The existing exact Agda owners are
`DASHI/Mathematics/NumberTheory/RiemannXiSymmetryExact.agda`
and `RiemannReflectionOrbitDefectExact.agda`
(the latter source-writes
`criticalReflectionNegatesDisplacement`,
`pairSignedDisplacementCancels` and
`pairDefectMassIsDouble`).
No new horizontal reflection axiom/wrapper is needed.

**Do not confuse three axes:** (1) horizontal functional
reflection `s→1−s` changes `Re(s)−1/2` sign;
(2) conjugation `s→conj(s)` exchanges positive/negative
**ordinates** and preserves real part (Lean
`Synthesis/RiemannZeta23RvMTwoSidedDiscrepancy.lean`
already proves actual ζ zero-count and μ-integral
negative-ordinate transfer); (3) normalized
left/right RvM prefix gaps are intervals on the
ordinate axis around a target height, not separate
critical-half-strip theorems.

The source-pinned *conditional* external zero-free-right
cap `β≤437479/500000` yields the reflected
left bound `Re(s)≥62521/500000`, and
`|Re(s)−1/2|≤187479/500000`, provided
one has the **same actual ζ theorem** and its
functional equation. DASHI Lean
`RiemannImprovedZeroFreeHalfPlaneDonorAudit.lean`
marks the exact external same-zeta theorem import
as **false**: source documentation alone does not
establish a native RH proof or fill the G3 signed
analytic inequality.

The original selected-W `LocalDebt−SignedCompensation`
strict eventual epsilon gap, physical kernel identity,
selected tail and same-object analytic proof remain
OPEN. Reflection doubles the even defect but also
doubles whichever SIGN the original quartic exhibits;
it does **not** pay a positive signed cone uniformly
or imply every zero is centered. Native source
Agda/Lean kernel was not run.

---

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

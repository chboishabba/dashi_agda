# Literal selected-plaquette singleton: the remaining calculation

## Sources

- Tadeusz Bałaban, *The Variational Problem and Background Fields in
  Renormalization Group Method for Lattice Gauge Theories*, Communications in
  Mathematical Physics **102** (1985), 277–309.
  DOI: [10.1007/BF01229381](https://doi.org/10.1007/BF01229381).
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background
  Field*, Communications in Mathematical Physics **99** (1985), 389–434.
  DOI: [10.1007/BF01240355](https://doi.org/10.1007/BF01240355).
- Ramon E. Moore, R. Baker Kearfott, and Michael J. Cloud, *Introduction to
  Interval Analysis*, SIAM, 2009.
  DOI: [10.1137/1.9780898717716](https://doi.org/10.1137/1.9780898717716).

## What is actually left

The six pair terms and five cubic-or-quartic terms in a four-link Wilson
placement are already finite algebra once the selected-link radius is known.
They do **not** contain the outstanding analytic problem.  The remaining
quantity is the *singleton* part of the literal Wilson second variation on the
actual selected background.

For a plaquette \(p\), let \(C_p\) be the repository's literal cross charge.
The required estimate is

\[
 -\frac{55}{18\,874\,368} C_p
 \;\leq\; W^{(1)}_p(A;h),
 \qquad
 \frac{55}{18\,874\,368}
 = 2.914004855685764\ldots\times10^{-6}.
\]

This is the only estimate that turns the selected Euler–Lagrange equation into
the sharp local Wilson curvature bound.  It is not legitimate to replace it by
a bound on inverse-link radius alone: the repository contains an explicit
counterexample to that implication in
`BalabanP33CovariantCurlRadiusStressTestExact.agda`.

## Exact signed form of the calculation

At the selected constrained minimizer, the localized admissible variation
\(v_p\) must satisfy the *literal* stationarity identity

\[
  0 = \delta S_A(v_p)
    = W^{(1)}_p(A;h) + R_p(A;h).
\]

Thus the desired lower bound is equivalent to the one-sided upper bound

\[
 R_p(A;h) \leq \frac{55}{18\,874\,368} C_p. \tag{1}
\]

The initial finite Möbius decomposition gives the sign-sensitive expression

\[
 R_p=\sum_{\varnothing\ne S\subseteq\{0,1,2,3\}}L_S
      -\sum_{\varnothing\ne S,T\subseteq\{0,1,2,3\}}G_{S,T}. \tag{2}
\]

There are exactly 15 raw terms \(L_S\) and 225 directed Green terms
\(G_{S,T}\) before cancellation.  Equation (2) is crucial: independently
bounding their absolute values destroys the cancellation needed for the
\(2.9\cdot10^{-6}\) margin.

For region-wide rational intervals

\[
L_S\in[\ell_S,u_S],\qquad G_{S,T}\in[a_{S,T},b_{S,T}],
\]

the rigorous upper endpoint is therefore exactly

\[
 U_R=\sum_Su_S-\sum_{S,T}a_{S,T}. \tag{3}
\]

The certificate test is the single rational comparison

\[
 U_R\leq \frac{55}{18\,874\,368}\,C_*,
 \qquad C_*\leq C_p(A;h)\quad\hbox{throughout the selected region}. \tag{4}
\]

Equations (2)--(4) are a valid proof of (1) once every endpoint is an
outward-rounded enclosure of its literal formula.  The sign directions in
(3) are forced: raw terms use upper endpoints and Green terms use lower
endpoints.

## The exact cancellation that makes the calculation viable

The literal plaquette geometry has a stronger identity.  After grouping by
Möbius degree, all source and defect degrees above one vanish *before* the KKT
pseudoinverse.  Consequently all Green blocks except \(G_{11}\) vanish and

\[
 R_p=(R_1-G_{11})+(R_2+R_3+R_4). \tag{5}
\]

The physical calculation is therefore **two** signed, charge-relative bounds,
not 240 independent atom intervals:

\[
 R_1-G_{11}\le a C_p,\qquad
 R_2+R_3+R_4\le b C_p,\qquad
 a+b\le\frac{55}{18\,874\,368}. \tag{6}
\]

This reduction is essential rather than cosmetic.  The separate nonnegative
state-norm/polarization route has a compulsory Green cost \(1/6\), whereas
the whole target is \(55/18\,874\,368\); it misses by a factor
\(3\,145\,728/55>57\,195\), even before raw terms are estimated.  Any proof
that applies absolute values to \(R_1\) and \(G_{11}\) separately cannot close
the stated budget.

## The non-negotiable physical input

To establish (6) uniformly on a selected-minimizer region, the project must
provide the same literal objects in both terms:

1. The selected background and the localized, gauge/constraint-projected
   variation defining the actual first-variation source.
2. The finite Wilson-plus-constraint KKT operator evaluated at that background
   and a certified region containing the selected minimizer.
3. A *joint signed* enclosure of \(R_1-G_{11}\), followed by an upper
   enclosure of the raw higher-degree sum.  A lower charge bound is not needed
   for this charge-relative formulation.

For an invertible unconstrained Hessian \(H_A\) and constraint map \(C\), the
constrained Green operator to be enclosed is the Schur-complement expression

\[
\mathcal G_A=H_A^{-1}-H_A^{-1}C^*(CH_A^{-1}C^*)^{-1}CH_A^{-1}, \tag{7}
\]

with a Moore--Penrose replacement only after its rank has been certified
constant on the region.  Formula (5) shows why a generic inverse-link bound is
insufficient: it gives neither a lower spectral bound for the constrained
Hessian nor sign information for the matrix elements entering \(G_{S,T}\).

## Current result and obstruction

The repository defines rational SU(2) link coordinates, the finite constraint
carrier, and a contraction-based inverse construction on its side-four test
carrier.  It also proves the finite propagation from (6) to the physical
Wilson Hessian and the pair/deep budgets separately.

What remains absent is the actual selected-background family and its literal
first-variation source, together with the two uniform signed estimates in
(6).  The abstract KKT/pseudoinverse records and generic inverse bounds cannot
substitute for those estimates; the no-go calculation above proves that their
separate norm majorants have insufficient headroom.

This is a concrete obstruction, not a missing compiler: the next executable
mathematical artifact must evaluate the same selected-background KKT/source
data in the jointly signed degree-one expression, then certify (6) with
outward rounding and a uniform-in-volume localization argument.  Until then
`LiteralSelectedPlaquetteFamily` must remain conditional and no positive
physical beta or mass-gap claim follows.

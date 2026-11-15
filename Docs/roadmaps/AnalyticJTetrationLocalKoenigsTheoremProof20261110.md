# Local principal-log Koenigs theorem — exact rational certificate and analytic proof

**Status:** a rigorous **ordinary complex-analysis** construction, with all constants
audited by exact rational arithmetic in
`scripts/check_analytic_j_tetration_local_koenigs_rational.py`.
**NOT** yet a constructive Bishop/Agda proof, and **NOT** the globally
normalized Kneser tetration. This intentionally separates mathematical
proof from Agda kernel acceptance and full-plane contour certification.

## The selected fixed point is inhabited, not assumed

Let `L(z)=Log(z)` be the principal complex logarithm on the right half
plane. Let `c=318/1000 + (1337/1000)i` and `R=1/100`. Exact rational
alternating-arctangent (Machin pi) and positive-log atanh enclosures prove

```text
|Log(c)-c| < 3/10000;
1.372 < |c| < 1.378.
```

The exact script proves these inequalities using 24 terms and explicit
remainders, **without floating-point inequality decisions**. The real part
of every point in `D(c,R)` is positive, so the selected Log branch is
holomorphic throughout that disk. On the closed disk,

```text
|L'(z)| = 1/|z| <= 1/(|c|-R) < 3/4.
|L(z)-c| < (3/10000)+(3/4)R < R.
```

The ordinary complex Banach fixed-point theorem produces a **unique**
`p ∈ D(c,R)` with `L(p)=p`, and

```text
|p-c| < (3/10000)/(1-3/4) = 0.0012,
1.37 < |p| < 1.38, Re(p) > 0.
```

These statements use the ordinary complex completeness theorem and its
standard branch derivatives. To promote to native Bishop, prove its exact
source Log construction, derivative and contraction theorem and transport
the rational enclosures into the original Bishop real/complex setoid.

## The genuine uniform local Koenigs limit

On `D = {z : |z-p| <= 1/10}`, the right-half-plane Log stays on the
selected branch, since `Re(p)>0.316`. For `|w|<=1/10`,

```text
|L(p+w)-p| <= q |w|,                 q=4/5,
|L(p+w)-p-w/p| <= M |w|²,           M=311/1000,
|p| <= Lambda,                      Lambda=69/50.
```

The first is integration of the derivative `1/z` along a segment,
using `|p|-1/10>1.27`. The second is the **exact** integral identity

```text
L(p+w)-p-w/p = -w² ∫₀¹ t / (p(p+tw)) dt,
```

giving the remainder coefficient `1/(2*1.37*1.27) < M=311/1000`. No Taylor
remainder is being guessed.

Put `w_n(z)=L^[n](z)-p`, `h_n(z)=p^n w_n(z)`.
Then `|w_n(z)|<=q^n|z-p|`, and for every n,

```text
h_(n+1)(z)-h_n(z) = p^(n+1) (L(p+w_n)-p-w_n/p),

|h_(n+1)-h_n| <= Lambda*M*(Lambda*q²)^n |z-p|²
                    = (69/50)*(311/1000)*(552/625)^n |z-p|².
```

Here `beta=Lambda*q²=552/625<1`. The geometric Weierstrass
M-test proves **uniform** convergence of `h_n` on the closed disk;
there is no need to assume Cauchy convergence as a record field:

```text
chi(z)=lim_(n→∞) h_n(z),

|chi(z)-h_N(z)| <= (21459/5840)*(552/625)^N |z-p|².
```

The exact script checks the coefficient identity. Every `h_n` is
holomorphic on a neighbourhood of the disk, so the Weierstrass holomorphic
limit theorem gives analytic `chi` in the disk interior.
Since `h_n(p)=0` and `h'_n(p)=1` identically,
`chi(p)=0`, `chi'(p)=1`. It is locally biholomorphic near `p`.
Also, by shifting the finite sequence,

```text
h_n(L(z)) = h_(n+1)(z)/p,
chi(L(z)) = chi(z)/p.
```

Thus this proves **local nonconstant Schröder linearization** in ordinary
complex analysis for the concrete branch and fixed point. It is **not** a
global Kneser/Abel chart. In particular `chi(z)/(z-p)` obeys

```text
|chi(z)/(z-p)-1| <= (21459/5840)|z-p| < 1  (0<|z-p|<=0.1),
```

allowing a local logarithm of the normalized ratio. The remaining
**integer** winding cocycle for `Log chi` is still branch-dependent
and must be proved on an explicit punctured sector, not inferred
from this inequality alone.

## A genuine local integer winding result and branch obstruction

The rigorous uniform limit estimate gives, for `0<|w|≤1/10`,
```text
chi(p+w) = w(1+eps(w)),   |eps(w)|≤(21459/5840)|w|≤0.368<1.
```

Consequently `1+eps(w)` lies in the simply connected right half-plane
disk `B(1,1)` and admits the **same principal Log everywhere on the full
closed radius-1/10 disk** (including the removable value at w=0).
For any `0<rho≤1/10`, the loop `chi(p+rho e^{it})` has winding number
**exactly 1** around 0, because the straight-line homotopy
```text
H_s(t) = rho e^{it} (1+s eps(rho e^{it})),   0≤s≤1,
```
never vanishes. At s=0 it winds once. This is a genuine
**ordinary complex topological** theorem about the actual constructed
local Koenigs function, not a numerical winding guess or a C3 phase
identification.

It follows by the argument principle (or the path-lifting obstruction)
that **no globally single-valued continuous/holomorphic logarithm of
chi exists on the entire punctured disk**. On any simply connected
sector with a chosen branch of `Log(z-p)` we can instead write
```text
Log_sector chi(z)
  = Log_sector(z-p) + Log_principal(chi(z)/(z-p)).
```
Two such sector choices differ by a locally constant **integer
multiple of 2πi**. This gives the mathematical construction and
the local winding-1 obstruction required for P1b. The remaining
native Bishop/Agda obligation is to define the actual sector and
integer winding carriers and prove the chart-overlap cocycle, including
the fixed-point multiplier `1/p` and all selected branch transitions.

It does **not** assert a single global Abel coordinate on the punctured
disk and does not solve Kneser conjugate-pair continuation.

## The exact next formal theorem leaves

1. `originalBishopPrincipalLogOnSeries`: give the original Bishop
   complex principal Log and prove its same-branch integral remainder.
2. `originalBishopLogInverseDiskIteration`: instantiate the rational
   fixed-point enclosure and derivative/contraction on the same carrier.
3. `originalBishopKoenigsIncrementMagnitude`: use that integral
   remainder and the verified rationals; the prior native Bishop
   geometric absolute-summability/telescoping/limit owners consume it.
4. `originalBishopKoenigsUniformCauchy`: source uniform modulus
   `beta=552/625`, not merely pointwise convergence.
5. `originalSchroederHolomorphicLocalLinearization`: Bishop holomorphic
   Weierstrass limit, derivative `chi'(p)=1`, injectivity and
   same-source Schröder equation.
6. `originalPuncturedSectorLogBranchCocycle`: selected integer winding,
   branch gluing; then global Kneser conjugate fixed-point normalization.
7. `originalKouznetsovCertifiedNumerics`: still requires original
   complex contour formulation, independent truncation/rounding
   enclosures and error control. Finite exact point estimates,
   including the ones above, do not certify the contour integral.

## Attribution and global proof boundary

D. Kouznetsov, *Solution of F(z+1)=exp(F(z)) in complex z-plane*,
Math. Comp. 78 (2009), 1647–1670,
[DOI 10.1090/S0025-5718-09-02188-7](https://doi.org/10.1090/S0025-5718-09-02188-7).
The paper presents an imaginary-axis integral-equation numerical method and
reports small numerical residuals. That evidence does not replace a
kernel-accepted constructive global existence/uniqueness theorem. Its
selected normalization `F(0)=1` also does not follow from the above
local fixed-point coordinate.

**Acceptance:** the rational program should exit zero; the precise
analytic argument above is a mathematical derivation; the Bishop
formalization and all global/Kouznetsov targets remain OPEN until native
Agda kernel receipts and source-faithful certified computations exist.

# Original exponential local Schröder construction: analytic maximum cut

Date: 2026-11-09. Status: **classical conditional proof and exact formal/numerical diagnostics; NOT Agda 2.9 kernel checked or Kneser-global construction.**

## Source identity and normalization

Take the *ordinary complex analytic* exponential as the target for Kouznetsov's tetration (distinct from other DASHI carrier-parametric interpretations). Write `p=-W_{-1}(-1)`; its numerically checked upper-branch value is approximately

```text
p = 0.318131505204764135312654251588
    + 1.33723570143068940890116214319 i.
abs(p) = 1.3745570107437074865.
```

Algebraically, once the Lambert W identity and the selected branch are **proved in the original complex setoid**, `exp(p)=p`, hence the multiplier `lambda=exp'(p)=p`. The numerical checks above do not constitute such a proof.

Choose `g(z)=Log(z)`, the principal complex logarithm, in a disk centred on p. Under `Log(p)=p`, this is the local inverse of exp fixing p.

## Constructive mathematical route to a nontrivial local Schröder chart

The following is a conventional complex-analytic proof *conditional on the stated fixed-point and modulus bounds*. Its realization through the Bishop setoid complex remains an Agda task.

1. Prove a complex enclosure `1.37 < |p| < 1.38`, `Log(p)=p` and exp(p)=p using a branch-certified interval or constructive complex proof. Define `D={z : |z-p|<1/10}`. It is disjoint from the principal logarithm cut and zero.
2. For z in D, `|g'(z)|=1/|z| ≤ 1/(1.37-0.1)=1/1.27<0.8=:q`. Since D is convex and `g(p)=p`, the straight-segment integral gives `|g(z)-p|≤q|z-p|`. Thus `g(D)⊂D`.
3. With `lambda=p`, `g'(p)=1/lambda`, and the second derivative `g''(z)=-1/z²`, the Taylor remainder on D satisfies

   `|g(p+t)-p-t/lambda| ≤ M|t|²,` where `M=1/(2*(1.27)^2)<0.311`.

4. Define `h_n(z)=lambda^n*(g^n(z)-p)`. Then

   `|h_{n+1}(z)-h_n(z)| ≤ |lambda|*M*(|lambda|*q²)^n*|z-p|²`.

   Here `|lambda|*q² <1.38*(0.8)^2=0.8832<1`. Therefore `(h_n)` converges locally uniformly to a holomorphic `chi(z)`, with explicit tail bound

   `|chi(z)-h_N(z)| ≤ [1.38*M/(1-0.8832)]*(0.8832)^N*|z-p|²`.

5. The telescoping limit yields `chi(g(z))=chi(z)/lambda`. Every `h_n'(p)=1`, so `chi(p)=0` and `chi'(p)=1`. The analytic inverse function theorem gives a smaller disk on which chi is injective. For z, exp(z) both in that disk, `chi(exp z)=lambda*chi(z)`: a **genuine nonconstant local Schröder conjugacy**.
6. On a simply connected punctured-sector subdomain where chi and lambda*chi have coherently chosen logarithm branches, define `A(z)=Log(chi(z))/Log(lambda)`. If `Log(lambda*chi(z))=Log(lambda)+Log(chi(z))` on that sector and `Log(lambda)≠0`, then `A(exp z)=A(z)+1`. The branch correction/winding must be tracked; the fixed point p itself is excluded.

This is a **local** Abel chart with a restricted one-step domain; it does not yet produce global exp-invariant iterates or Kneser's normalization. It does not imply a uniquely defined Abel function without the appropriate fixed-point-pair geometric criterion and fundamental-region continuation.

## Exact symbolic and numerical test receipts

`scripts/analytic_j_tetration_schroeder_formal.py --degree 6` ran with SymPy 1.14.0 and found exact rational-function coefficients c1..c6 and six identically zero Schroeder residual coefficients (not floating-point comparisons). Denominators contain factors `lambda^n-lambda` and require nonresonance.

`scripts/analytic_j_tetration_koenigs_diagnostic.py` ran with mpmath 80-digit working precision and 40 log iterates. For shifts `0.001` and `0.0001+0.0002i`, the last two Koenigs iterates differed by approximately `2.04529e-12` and `1.02224e-13`. This is a *diagnostic only*, not interval arithmetic or a proof of a certified truncation error.

## Exact remaining proof gates

- `originalExpFixedPointComplexExistence`: produce p, exp(p)=p, Log(p)=p and a certified enclosure on the original Bishop setoid complex.
- `originalLogInverseDiskRadiusBound`: prove disk cut avoidance, derivative bound q=4/5 and image containment for g.
- `originalLogQuadraticRemainderBound`: prove the M remainder from actual complex derivatives or an equivalent constructive power-series tail.
- `originalKoenigsSequenceGeometricCauchy`: prove the displayed uniform tail in the source analysis infrastructure.
- `originalSchroederHolomorphicLocalLinearization`: construct chi from that limit, show holomorphicity and chi'(p)=1, local injectivity and the conjugacy equation.
- `originalLogMultiplierBranchAndCocycleInstance`: establish nonzero chi on the selected punctured sector and the exact coherent log branch.
- `originalSelectedAbelSemiconjugacyInstance`: apply `AbelSchroederLogCocycleTransportExact.originalSelectedAbelSemiconjugacy` to that actual chart.
- `originalKneserFundamentalRegionGluing`: match conjugate fixed-point charts and prove continuation, overlap and monodromy constraints.
- `originalKneserRealAxisNormalization`: implement the normalizations and uniqueness criterion for the specific Kneser function; not implied by local linearization.
- `originalBishopQSeriesTPeriod`: source-construct the true T action on the upper half-plane, prove q periodicity with Bishop complex setoid equality and E4/E6/Delta/j compatibility.
- `originalRendererAbelWeldInstance`: identify the Abel image with the exact original modular point/renderer in the valid half-plane domain.
- `originalKneserToModularLevelLift`: provide the actual moving fine-level action and demonstrate equivariance, rather than forcing invariance.
- `originalKouznetsovCertifiedNumerics`: reproduce the published contour-integral procedure with interval-certified truncation and phase error, explicit branch/zero exclusions and F(0)=1 normalization.

## External authority and attribution

- H. Kneser, *Reelle analytische Lösungen der Gleichung φ(φ(x))=eˣ und verwandter Funktionalgleichungen*, Journal für die reine und angewandte Mathematik 187 (1949), 56–67.
- Henryk Trappmann and Dmitrii Kouznetsov, *Uniqueness of Holomorphic Abel Functions at a Complex Fixed Point Pair*, Aequationes Mathematicae 81 (2011), 65–76. DOI: 10.1007/s00010-010-0021-6. https://arxiv.org/abs/1006.3981
- Dmitrii Kouznetsov, *Solution of F(z+1)=exp(F(z)) in complex z-plane*, Mathematics of Computation 78 (2009), 1647–1670. DOI: 10.1090/S0025-5718-09-02188-7.

The sourced existence/uniqueness and numerical approaches remain credited to their authors. DASHI's new contribution is the explicit Agda proof-cut, same-object renderer/observer transport and reproducible formal/numerical testing.

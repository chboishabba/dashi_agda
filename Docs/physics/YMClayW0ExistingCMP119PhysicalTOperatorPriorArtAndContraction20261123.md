# YM P0 W0 — existing literal CMP119 T operations and original F19 source contraction (23 November 2026)

## User-prompted prior-art audit: the repo indeed already has T

The preferred physical T sources are already implemented as typed producers on master:

1. `BalabanClayGate4ComponentClassAndFiniteTOperationExact.agda`: `FiniteLocalTOperationData`, `SecondClassComponent`, `localizedTOperation`, a genuine finite *constrained integral* of local density times a functional, and monotonicity/positivity compilers.
2. `BalabanClayGate4CanonicalRationalPhysicalTExact.agda`: canonical rational constrained-sum realization of the physical finite T data, including original six-factor input via `BalabanClayT2LiteralWilsonSixFactorProducerExact`; it is **not** identical to continuous SU(N) Haar integration.
3. `BalabanCMP122Equation171TOperationSemanticsExact.agda`: Eq. (1.71) constrained integration of a source-localized exponential density defines a source T mass. Explicit finite realization is still marked **conditional**.
4. `BalabanCMP119FiniteDensityAssemblySemanticsExact.agda`: literal CMP119 complete-density `assembleDensity` operation/action evaluation, with the source-semantic leaf **conditional**.
5. `BalabanCMP119PhysicalTOperationAssemblyRealizationExact.agda`: selected T/A application = Gate4 physical T at one functional, supplied as the **`operationActionIsPhysicalTOperation` field**, not unconditionally established.
6. `BalabanCMP119PhysicalTOperationWeldExact.agda`: compilation of selected assembled density = physical T, with **`assembledDensityIsPhysicalTOperation` an input field** of the weld and physical positive support separately conditional.
7. `BalabanCMP119Equation171PhysicalTOperationRealizationExact.agda`: a finer Eq. (1.71) source-T-mass middle layer; both the application-to-source and source-to-Gate4 meaning remain **conditional**.
8. `BalabanBetaDrivenCMP119FunctionalOperatorExact.agda`: preferred literal functional carrier, `Operation = Action -> SlowField -> Real`, `assembleDensity T A = T A` definitionally; still requires a physical `operationAt`/source identity.
9. `BalabanCMP119Equation218FactorizedFunctionalDensityExact.agda`: literal finite *scalar expression* shape: sum over admissible sequences, component products and **ordered** scalar `oneStepValue` factors with explicit `sequenceResidual`. The original domain/step extraction levels are **conditional**.
10. `BalabanCMP119Section2CompleteDensityDictionaryExact.agda`: actual source shape is `rho_k = T_k(A_k)`, `A_k=Wilson(g_k,U_k)+E_k+R_k+B_k-E_vac`; the five compact DASHI summary coordinates are only derived projections.

The exact original F19 full marked source is already available via `YMClayOriginalWilsonF19FineTwoMarkMomentBIDIExact.agda`, `YMClayOriginalWilsonPhysicalF19PartitionExact.agda`, and the canonical reindex/Haar owners. Reuse them; original fine plaquette marks are not solely coarse-measurable. Keep all four coefficients K0/KF/KG/KFG and the 896 interacting spectators.

## Algebraic interface hazard: scalarized product need not equal composed T

Exact SymPy regression in `scripts/check_ym_w0_ordered_T_operator_vs_scalar_product_20261123.py`, **executed locally**. This is an illustrative finite positive two-state operator example, **NOT** a claim about the actual CMP119/SU(N) T operations or measure.

Let A=[[2,1],[1,3]], B=[[3,2],[1,2]], F=diag(0,2), G=diag(2,0), left=(1,0) and right=(1,1)^T. The true ordered functional contraction is

```
K(s,t) = left A (I+sF) B (I+tG) right
       = 13 + 6s + 14t + 4st.
```

Retaining and summing the **shared intermediate state index** reproduces every coefficient exactly. Incorrectly multiplying separately contracted scalar masses gives

```
Kshortcut(s,t) = [left A (I+sF) right] [left B (I+tG) right]
               = 15 + 10s + 18t + 12st.
```

Both four-coefficient vectors separately satisfy the original positive [0,2]-mark *necessary cone*, so positive coefficients and even sharp moment-cone membership cannot identify the underlying T source. The matrices also fail to commute, so changing the T order is not generally lawful. This is only a type/semantic negative control; CMP119's actual factorization over disjoint components may be valid once the source supplies the proper localized interfaces and ordered step contractions.

## Physical same-source W0 weld to discharge; no duplicate compiler

The correctly typed path should be original fine marked SU(N) Wilson/Haar at fixed W (all 64 fibre and 896 spectator links) -> **actual source localized T operation acting on the appropriate functional** -> CMP122 Eq.(1.71) localized integration -> CMP119 (2.18) admissible domain-sequence sum, (2.19) disjoint component product, (2.20)/(2.22) ordered step composition, retaining explicit residual -> existing T/A density and Round214/R108 E/R/B/V action -> absolute W3 source-localized connecting shells.

In particular:
- Identify the actual `fastFibre`, `coarseMatches`, normalization and original Wilson/FP/ghost/Jacobian density from the original F19 Haar source, not an arbitrary rational quadrature or independently selected Gate4 reference measure.
- When mapping composed functionals to `oneStepValue` scalars, prove all intermediate-state contractions/conditional integrations are retained. For any disjoint component scalar product, prove the relevant conditional factorization and that no fine-mark FG fibre-connected term is dropped.
- Show the four original coefficients 1/F/G/FG after the **same** T operation, not just the unmarked partition or pointwise positivity; preserve unique global insertions and inherited Hessian/score-covariance.
- Do not infer CMP119 physical step identity from a `machineChecked` *compiler status label*: check whether the relevant premise is a physical equality field, the source's exact 2.18-2.22 indices, or an independently verified proof term.
- The finite rational positive T is not, by itself, a continuous SU(N) Haar integration certificate or an all-cutoff/volume uniform physical W3 estimate.

**Status:** source-reviewed existing T owners and exact locally executed finite two-state SymPy negative control. No Agda kernel/CI, no actual physical T/normalizer identity, no continuum OS/spectral-gap completion. Attribution: original Wilson/Haar; Bałaban CMP119/CMP122; existing DASHI/P3/Gate4/F19 source authors and finite operator algebra.

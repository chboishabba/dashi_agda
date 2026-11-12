# Bałaban physical P0: exact source donors and remaining welds (2026-11-13)

**Scope:** user-provided 12-group "constructively closed" outline, checked against
the actual DASHI source and PR #1498 head; arithmetic sibling PR #1479;
historical PR #564 is CLOSED and is not the current integration head.

**Authority:** local Agda 2.9 kernel acceptance > static source > Python exact
rational tests > descriptive ProofLevel markers > prose.
No CI used. Source-written declarations below are NOT kernel verified here.
No axiom, postulate, synthetic physical source, proxy four-integral value or
`Set=⊤` receipt may be substituted for the actual physical input.

## Concrete in-repo proof donors: DO NOT restart

| Carrier / source | Actual theorem or producer | What is paid |
|---|---|---|
| `BalabanP33PhysicalRationalWilsonPlaquetteJetExact` | `physicalWilsonSecondVariationIsSixteenAtomSum`; `identityPhysicalWilsonIsFlatCurl` | side-four lattice SU2 Wilson Hessian at identity and rational 16-atom curl |
| `BalabanP33PhysicalFaddeevPopovOperatorExact` | `identityFaddeevPopovIsFlat`; `flatFaddeevPopovIsPeriodicLaplacian` | actual finite FP at identity = flat nearest-neighbour Laplacian |
| `BalabanReducedFaddeevPopovPhysicalFourthJetExact` | `physicalReducedGhostMatrices4`; `physicalGhostTraceLogJet` | native reduced FP perturbation coefficients through degree four, formal trace-log polynomial |
| `BalabanReducedFaddeevPopovMatrixTraceLogJetExact` | `matrixTraceLogJet4` | exact finite matrix moment and cyclic trace arithmetic |
| `BalabanClayT4FaddeevPopovWilsonSymbolBridgeExact` | `freeGhostSymbolIsCanonicalHatMomentumAtom` | free FP and canonical Wilson Fourier symbol are the same Bishop real *given coherent half-angle* |
| `BalabanCompactSimpleHaarQuadraticCasimirExact` | `classifiedHaarQuadraticCoefficientExact` | Haar quadratic effective-action coefficient = `C_A /24 * ||X||²` under selected compact-group trace conditions |
| `BalabanClayT4LiteralVacuumPolarizationIntegralExact` | `adjointStructureConstantContraction`; `combinedElevenThirdColorFactorExact` | SU2 color factor and rational 11/3 arithmetic, NOT physical per-diagram loop calculation |
| `BalabanCMP109MixedDerivativeBetaExtractionExact` | `cmp109MixedDerivativeExtractsBeta` | reads beta from a correctly supplied off-diagonal two-jet; does not produce that jet |
| `BalabanClayT4RefinedOriginalWilsonBishopEnvironmentExact` | `originalWilsonHatSound`; `refinedLoopDenominatorPositive` | conditional original loop-symbol Bishop membership and strictly positive interval on each regular box |
| `BalabanClayT4AuxiliaryWilsonNormalizedMeasureExact` | `regularUnitMassExact` and normalized free-propagator bounds | true x-chart to Brillouin measure factor 1/16; auxiliary propagator only |

## New source-written max-cut welds on PR #1498, this round

1. `BalabanP0FreeGhostWilsonPositiveWeldExact.agda`:
   `actualGhostSymbolInRefinedWilsonBox` uses the *actual*
   `freeGhostSymbolIsCanonicalHatMomentumAtom` proof and physical
   `originalWilsonHatSound` to put the same ghost and Wilson real
   symbol in the same positive rational denominator box.
   `regularFreeGhostWilsonSharedPositiveInterval` produces the
   combined Bishop membership + strict rational endpoint positivity.
   `loopAndShiftedFreeSymbolsBothPositive` explicitly requires a
   potentially different original regular cell for p+k; does NOT
   infer the shifted cell is regular or assume an unproved half-angle.
2. `BalabanP0TransverseGaugeFixingNoGoExact.agda`:
   `feynmanGaugeRestoresComponentLaplacian` proves
   `(qhat² δ - qhat_mu qhat_nu) + qhat_mu qhat_nu = qhat² δ`.
   `flatCurlNotUnfixedComponentLaplacian` disproves the attachment's
   naked `d*d = Σ Δ` by a longitudinal rational counterexample.
   `su2PureGaugeBetaRationalPrefactor` derives
   `(11/3)*C_A*(1/16)=11/24` using actual source constants.
   `su2AdjointCasimirNotFour` refutes C_A=2N in SU2 convention.
3. `BalabanP0FourOrbitMidpointHessianBudgetAlgebraExact.agda`:
   exact physical-normalization algebra:
   per original x cell `M2/384`, after the Fourier Jacobian
   per physical cell `M2/6144`, four-orbit physical budget
   `(4 M1 +6 M2 +4 M3 +M4)/384`.
   `actualFourHessianBudget` consumes actual source quadrature
   `hessianNormUpper` fields, not invented four values.
   Does NOT prove those four fields bound the actual source Hessians.
4. `BalabanP0SU2HaarQuarticFormalJetExact.agda`:
   correct SU2 exponential-coordinate formal series:
   `J(r)=1-r²/12+r⁴/360+O(r⁶)`,
   `log J(r)=-r²/12-r⁴/1440+O(r⁶)`.
   The `haarLogExpFourthCoefficientExact` rational identity
   and positive effective-action signs are proved at formal coefficient
   level. The actual analytic remainder/chart identification is open.
5. `BalabanClayT4LiteralOneLoopBoxEvaluatorExact.agda`:
   `rationalInterval` is now explicitly a definitional alias for the
   original `interval` constructor. Existing canonical Bishop and
   reciprocal modules still refer to that alias, previously missing.
   `BalabanClayT4CanonicalBishopAtomEnvironmentExact` singleton
   constructor also aligned to `Eval.interval`.

## Exact remaining maximum cut — NOT 12 closed groups

| Gate | First unpaid physical declaration / source proof | Smallest source-preserving next action |
|---|---|---|
| P0.1 W cubic/quartic | `LiteralMomentumVertices.wilsonCubicBackgroundVertexMomentumExact`, `wilsonQuarticBackgroundVertexMomentumExact` | FFT of the *existing* finite P33 Wilson plaquette third/fourth jets, proving correct link, orientation, phase and gauge convention, not merely the Hessian two-jet |
| P0.2 FP loop | `physicalReducedGhostBishopFifthOrderRemainderLevel`, `literalOneLoopFaddeevPopovFourierIdentificationLevel` | construct actual reduced FP determinant/log and uniform Bishop remainder; identify finite side-four momentum frequencies with correct continuum/Brillouin Fourier limit |
| P0.3 Haar chart | `physicalBalabanHaarCoordinateNormalizationLevel`, `physicalSU2HaarDensityIdentificationInputsLevel`, `physicalSU2HaarLogRemainderInputsLevel` | match existing Haar Casimir/formal jet to Bałaban's exact link chart, prove Jacobian and controlled analytic logarithmic remainder |
| P0.4 literal AST | `LiteralDiagramExpressions` | instantiate four real Wilson bubble/tadpole/ghost/Haar numerator and denominator expressions and their `gaugeBubbleDefinition` etc; must reflect actual Lorentz/color contractions and external momentum |
| P0.5 Ward | `LiteralWardExpressionProofs.diagramwiseWardSumIsZero`, `transverseFactorizationExact` | derive the genuine same-source Ward contraction and tensor factorization, not a syntactic zero chosen by a free contraction function |
| P0.6 beta two-jet | `literalWilsonFPHaarOffDiagonalTwoJetIdentificationLevel`, `LiteralScalarIntegrandExpression.singularRegularSplitExact` | build original combined off-diagonal two-jet from the four physical diagram kernels and show semantic same-real singular+regular decomposition (old divide-vs-add AST equality was impossible and has been repaired on #1498) |
| P0.7 trig | `CoherentGhostTrigBoxData.halfAngleExact`, `ActualSourceFourSineMembership.axis0RealSine` through `axis3RealSine` | supply actual *same Bishop values* q=πx, cos q, sin(q/2) with strict source box enclosures for all roles |
| P0.8 denominators | `LiteralGeneratedBoxEvaluator.everyRegularDenominatorPositive` plus every division in selected Typed AST | link true Fourier sin bounds to the interval evaluator; pay shifted p+k positivity and possible box crossing separately; the loop-only floor 7569/4096 does not pay shifted |
| P0.9 atoms B4 | `LiteralSevenSemanticGeneratorData.atomsFlip0` through `atomsSwap23` | proof of transformed source atoms in the SAME evaluator, including odd sine, cosine, loop/external/shifted roles and phases |
| P0.10 scalar B4 | `LiteralSevenSemanticGeneratorData.semanticFlip0` through `semanticSwap23` | prove seven semantic symmetries of selected physical *regular scalar* AFTER tensor-to-beta projection. Fixed external axis may admit only the 96-element stabiliser; trace covariance under simultaneous action is not fixed-k invariance |
| P0.11 quadrature | `CertifiedBoxQuadrature.midpointInsideInterval`, `hessianBoundValid`, `quadratureErrorFormulaValid`, `trueIntegralInsideIntervalPlusError`, and source error covariance | compute four ACTUAL scalar integrals and a genuine analytic Hessian/interval error theorem. Algebraic `M/384` is NOT a Hessian bound or a numerical source receipt |
| P0.12 source coefficient | `ConfiguredPhysicalOneLoopInstance.boxCoefficientMatchesBalabanCoefficient`, `quarticRemainderMatchesBalabanBetaPrimeError` | connect source four integral values with correct `d^4x/16` normalisation to CMP109 off-diagonal coefficient; establish physical RG quartic remainder, not merely the known algebraic 11/3 |

### Adversarial mathematical corrections to attached claims

- In the Pauli-half/Tr(Ta Tb)=δab/2 convention `C_A(SU(N))=N`,
  so for SU2 it is 2, not the stated 2N=4.
- `Re Tr(I-exp(aF))` for anti-Hermitian F begins with
  **`-a² Tr(F²)/2`**, not `+a² Tr(F²)/2`.
- `d*d` is transverse; the gauge-fixed operator is `d*d+d d*`
  (on flat periodic carrier) and has scalar-Laplacian symbol.
- Matching `hat{q}²` free Wilson/ghost poles does not prove a
  one-loop cancellation or uniform background FP determinant bound.
- `sin(pi/4)>=87/128` is weaker than the sharp `sqrt2/2` floor:
  the source conditional rational rank floor 7569/4096 differs
  from the sharp 2 by 623/4096. No automatic 2m endpoint proof.
- `q=πx`, physical `d^4q/(2π)^4=d^4x/16`: require this additional
  Jacobian after the source cell x-volume 1/16, not one or the other.
- `I_total=11/(24π²)*log 2±10^-6` is not an output of the
  current certified quadrature code. The number and error claimed in
  the attachment have no four physical source numerical receipts.
- Even after a one-loop beta *coefficient* is correctly identified,
  Clay YM E1/D1/D2 do NOT follow from `g²~1/k` alone: original
  Wilson covariance, nonperturbative uniform scale bounds, continuum
  limit and spectral gap remain separate theorems.

### Verification and authority

- Rational/formal analytic sanity checks performed locally:
  `11/3*2/16=11/24`, `log(J)_4=-1/1440`,
  `J_4=1/360`, `M2/384`, physical `M2/6144`,
  exact original 64/96/64/16 to 4/6/4/1 orbit fold, and
  anti-Hermitian sign. PASS under Python Fractions/SymPy.
- New Agda code committed/read back on PR #1498, NOT kernel checked:
  Agda/Nix executable unavailable here. `scripts/check_balaban_t4_semantic_p0_local.sh`
  is the local authoritative checker; **no CI**.
- Do not use its final `machineChecked` descriptive labels as
  kernel receipts. No original physical or Clay endpoint promoted.

{-# OPTIONS --safe #-}
module DASHI.Analysis.BishopOriginalCompletedXiFactorContinuityCompilerExact where

------------------------------------------------------------------------
-- K04d-CONTINUITY: DISTINCT ORIGINAL ZETA AND COMPLETED XI WELD.
--
-- This module evaluates the actual RiemannAnalyticSubstrate
-- CompletedRiemannZeta.xi, gamma and zeta function fields, on the
-- same literal RiemannBishopComplexAnalyticCarrierExact carrier.
--
-- The prefactor represents 1/2*s*(s-1)*pi^(-s/2) on the original
-- selected chart. No fabricated default prefactor, gamma, or xi is
-- chosen. The source-value equality to the displayed xi formula and
-- each factor's continuity are explicit inputs, not inferred from
-- the opaque xiEntire / CompletedDefinition Set-valued fields.
--
-- Once those *actual* inputs are supplied, every remaining algebraic
-- continuity transport is a native pinned-Bishop Sequence proof.
-- This module is a conditional compiler, NOT proof that the missing
-- original gamma/prefactor/xi semantic fields are inhabited.
--
-- Riemann (1859), Bishop/Bridges; Murray/Csimma pinned Bishop backend.
------------------------------------------------------------------------

open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as R
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopComplexSequentialContinuityAlgebraExact as ComplexCont
import DASHI.Analysis.BishopOriginalCompletedZetaUniformChartContinuityExact as ZetaCont

module OnOriginalXiChart
  (functions : BC.BishopComplexAnalyticFunctionLayer)
  (gamma : Analytic.GammaMellinLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (halfPlane : Analytic.ZetaHalfPlaneLayer
    (BC.bishopComplexAnalyticCarrier functions))
  (completed : Analytic.CompletedRiemannZeta
    (BC.bishopComplexAnalyticCarrier functions) gamma halfPlane)
  (chart gammaArgument : R.ℝ → BC.BishopComplex)
  where

  originalXi : R.ℝ → BC.BishopComplex
  originalXi x =
    BC.apply functions
      (Analytic.CompletedRiemannZeta.xi completed)
      (chart x)

  originalZeta : R.ℝ → BC.BishopComplex
  originalZeta x =
    BC.apply functions
      (Analytic.CompletedRiemannZeta.zeta completed)
      (chart x)

  originalGamma : R.ℝ → BC.BishopComplex
  originalGamma x =
    BC.apply functions
      (Analytic.GammaMellinLayer.gamma gamma)
      (gammaArgument x)

  selectedXiFactorProduct :
    (prefactor : R.ℝ → BC.BishopComplex) →
    R.ℝ → BC.BishopComplex
  selectedXiFactorProduct prefactor x =
    BC._*C_
      (prefactor x)
      (BC._*C_ (originalGamma x) (originalZeta x))

  -- A true xi-definition receipt must be extracted from the original
  -- completed-function implementation, not manufactured from a free
  -- Set field. The two selected coordinates are separately checked.
  XiIsOriginalFactorProduct :
    (prefactor : R.ℝ → BC.BishopComplex) → Set
  XiIsOriginalFactorProduct prefactor =
    (x : R.ℝ) →
    R._≃_
      (BC.re (originalXi x))
      (BC.re (selectedXiFactorProduct prefactor x))
    ×
    R._≃_
      (BC.im (originalXi x))
      (BC.im (selectedXiFactorProduct prefactor x))

  originalXiContinuityFromActualFactors :
    (prefactor : R.ℝ → BC.BishopComplex) →
    XiIsOriginalFactorProduct prefactor →
    ComplexCont.ComplexSequentiallyContinuous prefactor →
    ComplexCont.ComplexSequentiallyContinuous originalGamma →
    ComplexCont.ComplexSequentiallyContinuous originalZeta →
    ComplexCont.ComplexSequentiallyContinuous originalXi
  originalXiContinuityFromActualFactors
      prefactor sameXi prefactorContinuous gammaContinuous zetaContinuous =
    let
      internalProductContinuous =
        ComplexCont.selectedComplexProductSequentiallyContinuous
          originalGamma originalZeta
          gammaContinuous zetaContinuous

      productContinuous =
        ComplexCont.selectedComplexProductSequentiallyContinuous
          prefactor
          (λ x → BC._*C_ (originalGamma x) (originalZeta x))
          prefactorContinuous internalProductContinuous
    in
    ZetaCont.pointwiseEquivalentPreservesSequentialContinuity
      (λ x → BC.re (originalXi x))
      (λ x → BC.re (selectedXiFactorProduct prefactor x))
      (λ x → proj₁ (sameXi x))
      (proj₁ productContinuous)
    ,
    ZetaCont.pointwiseEquivalentPreservesSequentialContinuity
      (λ x → BC.im (originalXi x))
      (λ x → BC.im (selectedXiFactorProduct prefactor x))
      (λ x → proj₂ (sameXi x))
      (proj₂ productContinuous)

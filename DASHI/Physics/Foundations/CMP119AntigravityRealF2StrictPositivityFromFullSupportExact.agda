{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityRealF2StrictPositivityFromFullSupportExact where

open import Data.Product.Base using (_,_)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; _<ℝ_)

import DASHI.Physics.Foundations.CMP119AntigravityRealStrictSignExact as Strict
import DASHI.Physics.Foundations.CMP119AntigravityRealCurvatureF2PointBridgeExact as F2
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as GibbsPositive
import DASHI.Physics.Foundations.CMP119AntigravityRealFullSupportHaarExact as FullSupport
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsPhysicalFiniteMeasureCylinderAlgebraExact as Finite
import DASHI.Physics.YangMills.YangMillsCMP119WilsonGibbsHaarActionRound443Exact as Gibbs
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed

------------------------------------------------------------------------
-- NONZERO CURVATURE + POSITIVE GIBBS DENSITY + FULL SUPPORT => N(F^2) > 0
--
-- No explicit finite quadrature and no hand-built region are needed on the
-- preferred physical path.
------------------------------------------------------------------------

weightedF2 :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ} →
  (Configuration → ℝ) →
  Configuration → ℝ
weightedF2 {measure = measure} fieldStrengthSquare configuration =
  Physical.density measure configuration
  *ℝ fieldStrengthSquare configuration

weightedF2Numerator :
  ∀ {Configuration}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ} →
  (Configuration → ℝ) →
  ℝ
weightedF2Numerator {measure = measure} fieldStrengthSquare =
  Physical.haarIntegral measure
    (weightedF2 fieldStrengthSquare)

record RealPhysicalF2StrictPositivityInput
    {Configuration Action : Set}
    {measure : Physical.PhysicalFiniteYMMeasure Configuration ℝ}
    {laws : Finite.PhysicalFiniteMeasureIntegrationLaws measure}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    (gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws)
    (exponential : GibbsPositive.StrictPositiveRealExponential)
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure) : Set₁ where
  field
    gibbsExponential :
      GibbsPositive.WilsonGibbsExponentialDensityAttachment
        gibbs exponential

    curvature :
      F2.RealCurvatureF2PointBridge Configuration embedding

    weightedF2Continuous :
      FullSupport.Continuous fullSupport
        (weightedF2
          (F2.realFieldStrengthSquare curvature))

open RealPhysicalF2StrictPositivityInput public

weightedF2Nonnegative :
  ∀ {Configuration Action measure laws}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    {gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws}
    {exponential : GibbsPositive.StrictPositiveRealExponential}
    {fullSupport : FullSupport.FullSupportRealHaarAuthority measure}
    (input :
      RealPhysicalF2StrictPositivityInput
        strict embedding gibbs exponential fullSupport) →
  Finite.PointwiseNonnegative
    (weightedF2
      (F2.realFieldStrengthSquare (curvature input)))
weightedF2Nonnegative
    {laws = laws} strict embedding input =
  Finite.densityTimesNonnegativeObservable
    laws
    (F2.realFieldStrengthSquare (curvature input))
    (F2.realF2NonnegativeEverywhere (curvature input))

weightedF2PositiveAtWitness :
  ∀ {Configuration Action measure laws}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    {gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws}
    {exponential : GibbsPositive.StrictPositiveRealExponential}
    {fullSupport : FullSupport.FullSupportRealHaarAuthority measure}
    (input :
      RealPhysicalF2StrictPositivityInput
        strict embedding gibbs exponential fullSupport) →
  0ℝ <ℝ
    weightedF2
      (F2.realFieldStrengthSquare (curvature input))
      (F2.witnessConfiguration (curvature input))
weightedF2PositiveAtWitness
    {gibbs = gibbs} {exponential = exponential}
    strict embedding input =
  Strict.positiveTimesPositive strict
    (GibbsPositive.gibbsDensityStrictlyPositive
      (gibbsExponential input)
      (F2.witnessConfiguration (curvature input)))
    (F2.realF2PositiveAtWitness (curvature input))

realPhysicalF2NumeratorStrictlyPositive :
  ∀ {Configuration Action measure laws}
    (strict : Strict.RealStrictSignLaws)
    (embedding : Embed.OrderedRationalRealEmbedding)
    {gibbs :
      Gibbs.WilsonGibbsHaarAction
        {Configuration = Configuration} {Action = Action}
        measure laws}
    {exponential : GibbsPositive.StrictPositiveRealExponential}
    (fullSupport : FullSupport.FullSupportRealHaarAuthority measure)
    (input :
      RealPhysicalF2StrictPositivityInput
        strict embedding gibbs exponential fullSupport) →
  0ℝ <ℝ
    weightedF2Numerator
      {measure = measure}
      (F2.realFieldStrengthSquare (curvature input))
realPhysicalF2NumeratorStrictlyPositive
    strict embedding fullSupport input =
  FullSupport.strictIntegralFromPositivePoint fullSupport
    (weightedF2
      (F2.realFieldStrengthSquare (curvature input)))
    (weightedF2Nonnegative strict embedding input)
    (weightedF2Continuous input)
    (F2.witnessConfiguration (curvature input) ,
      weightedF2PositiveAtWitness strict embedding input)

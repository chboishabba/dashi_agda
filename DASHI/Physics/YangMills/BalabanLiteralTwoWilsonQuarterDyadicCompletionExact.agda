{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonQuarterDyadicCompletionExact where

------------------------------------------------------------------------
-- Literal twice-Wilson CMP116 source theorem -> exact quarter-dyadic envelope.
--
-- R444/R445/R448/R452 already prove, on the same finite T5 covariance,
--
--   embed |Cov| <= A_src * W(time).
--
-- The residual-dyadic constructor makes W(time) = embed((1/2)^time).
-- The only Yang--Mills quantitative normalization retained here is
--
--   A_src <= embed(1/4).
--
-- Ring preservation then compiles the exact majorant
--
--   embed |Cov| <= embed((1/4)(1/2)^time).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_; ≤ℝ-refl; ≤ℝ-trans; mulMonotoneNonnegative)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116R429MixedLogResponseRound445Exact as R445
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalSeparationRound450Exact as R450
import DASHI.Physics.YangMills.BalabanCMP116ConnectedCorePathRound453Exact as R453
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonResidualDyadicCalibrationExact as Dyadic
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedExpansionTheoremExact as Literal
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Base
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Add
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Ring
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo

orderedEmbedding :
  Ring.RationalRealRingEmbedding →
  Base.OrderedRationalRealEmbedding
orderedEmbedding embedding =
  Add.base (Ring.additive embedding)

embedQ :
  Ring.RationalRealRingEmbedding →
  ℚ → ℝ
embedQ embedding =
  Base.embed (orderedEmbedding embedding)

record QuarterDyadicTwoWilsonSource
    {Measure Observable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure}
        {TestObservable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        base)
    (ringEmbedding : Ring.RationalRealRingEmbedding)
    : Set₁ where
  field
    mixedLog :
      R445.R429LiteralMixedLogResponse
        (R444.asR429 data)
        (orderedEmbedding ringEmbedding)

    connected :
      R453.ConnectedCorePathGeometry data

    sourceDyadic :
      Dyadic.ResidualDyadicSourceCalibration
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        {data = data}
        (orderedEmbedding ringEmbedding)
        (R453.asCanonicalDomainSpecificRateSplit data connected)

    physical :
      R450.CanonicalPhysicalSeparation data

    sourceAmplitudeBelowQuarter :
      R448.sourceAmplitude
        (R453.asCanonicalDomainSpecificRateSplit data connected)
      ≤ℝ
      embedQ ringEmbedding Shell.quarter

open QuarterDyadicTwoWilsonSource public

literalTheorem :
  ∀ {Measure Observable dataSet extension base data ringEmbedding} →
  QuarterDyadicTwoWilsonSource
    {Measure = Measure}
    {Observable = Observable}
    {dataSet = dataSet}
    {extension = extension}
    {base = base}
    data ringEmbedding →
  Literal.LiteralTwoWilsonMarkedExpansionTheorem
    {Measure = Measure}
    {Observable = Observable}
    {dataSet = dataSet}
    {extension = extension}
    {base = base}
    data
    (orderedEmbedding ringEmbedding)
literalTheorem source =
  Literal.fromDyadicSourceDecay
    (mixedLog source)
    (connected source)
    (sourceDyadic source)
    (physical source)

embeddedHalfPowerNonnegative :
  (embedding : Ring.RationalRealRingEmbedding) →
  ∀ depth →
  0ℝ ≤ℝ embedQ embedding (Geo.halfPower depth)
embeddedHalfPowerNonnegative embedding depth =
  subst
    (λ lower → lower ≤ℝ embedQ embedding (Geo.halfPower depth))
    (Base.zeroExact (orderedEmbedding embedding))
    (Base.orderPreserving
      (orderedEmbedding embedding)
      (Geo.halfPowerNonnegative depth))

embeddedQuarterDyadicExact :
  (embedding : Ring.RationalRealRingEmbedding) →
  ∀ depth →
  embedQ embedding (Shell.quarter * Geo.halfPower depth)
  ≡
  embedQ embedding Shell.quarter
    *ℝ embedQ embedding (Geo.halfPower depth)
embeddedQuarterDyadicExact embedding depth =
  Ring.multiplyExact embedding
    Shell.quarter
    (Geo.halfPower depth)

literalTwoWilsonEmbeddedQuarterDyadicDecay :
  ∀ {Measure Observable dataSet extension base data ringEmbedding}
    (source :
      QuarterDyadicTwoWilsonSource
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        data ringEmbedding) →
  let
    theorem = literalTheorem source
    geometry =
      R453.asCanonicalDomainSpecificRateSplit data (connected source)
    time = R450.euclideanTime (physical source)
  in
  embedQ ringEmbedding
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet
        (R445.cutoff (mixedLog source)))
      (R444.leftObservable data)
      (R444.rightObservable data))
  ≤ℝ
  embedQ ringEmbedding
    (Shell.quarter * Geo.halfPower time)
literalTwoWilsonEmbeddedQuarterDyadicDecay
    {data = data} {ringEmbedding = ringEmbedding}
    source =
  let
    theorem = literalTheorem source
    geometry =
      R453.asCanonicalDomainSpecificRateSplit data (connected source)
    time = R450.euclideanTime (physical source)

    sourceBound =
      Literal.literalTwoWilsonEmbeddedCovarianceDecay theorem

    amplitudeNN =
      R448.sourceAmplitudeNonnegative geometry

    halfNN =
      embeddedHalfPowerNonnegative ringEmbedding time

    scaledAmplitude :
      R448.sourceAmplitude geometry
        *ℝ embedQ ringEmbedding (Geo.halfPower time)
      ≤ℝ
      embedQ ringEmbedding Shell.quarter
        *ℝ embedQ ringEmbedding (Geo.halfPower time)
    scaledAmplitude =
      mulMonotoneNonnegative
        amplitudeNN
        (sourceAmplitudeBelowQuarter source)
        halfNN
        ≤ℝ-refl

    toEmbeddedProduct =
      ≤ℝ-trans sourceBound scaledAmplitude
  in
  subst
    (λ upper →
      embedQ ringEmbedding
        (R278.connectedCovarianceMagnitude extension
          (Gram.measureSequence dataSet
            (R445.cutoff (mixedLog source)))
          (R444.leftObservable data)
          (R444.rightObservable data))
      ≤ℝ upper)
    (sym (embeddedQuarterDyadicExact ringEmbedding time))
    toEmbeddedProduct

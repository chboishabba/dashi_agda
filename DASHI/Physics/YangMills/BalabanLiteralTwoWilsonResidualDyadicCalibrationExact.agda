{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonResidualDyadicCalibrationExact where

------------------------------------------------------------------------
-- Source residual decay + literal Euclidean separation -> R451.
--
-- The physical source need not supply the final composed statement
--
--   W(d_graph) <= envelope(time).
--
-- It is enough to prove the source-native residual weight is below the canonical
-- dyadic profile at every depth.  R450 supplies time <= graph distance and the
-- existing halfPower antitonicity then performs the physical-time transport.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; ≤ℝ-trans)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalSeparationRound450Exact as R450
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalDecayRound451Exact as R451
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph

record ResidualDyadicSourceCalibration
    {Measure Observable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure}
        {TestObservable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        base}
    (embedding : Embed.OrderedRationalRealEmbedding)
    (geometry : R448.CanonicalDomainSpecificRateSplit data)
    : Set₁ where
  field
    sourceResidualBelowDyadic :
      ∀ depth →
      R414.weight (R448.sourceDecay geometry) depth
      ≤ℝ
      Embed.embed embedding (Geo.halfPower depth)

open ResidualDyadicSourceCalibration public

asCanonicalPhysicalDecay :
  ∀ {Measure Observable dataSet extension base data embedding geometry}
    (source :
      ResidualDyadicSourceCalibration
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        {data = data}
        embedding geometry)
    (physical : R450.CanonicalPhysicalSeparation data) →
  R451.CanonicalPhysicalDecayCalibration geometry
asCanonicalPhysicalDecay
    {data = data} {embedding = embedding} {geometry = geometry}
    source physical = record
  { R451.CanonicalPhysicalDecayCalibration.euclideanTime =
      R450.euclideanTime physical
  ; R451.CanonicalPhysicalDecayCalibration.physicalEnvelope =
      λ time → Embed.embed embedding (Geo.halfPower time)
  ; R451.CanonicalPhysicalDecayCalibration.selectedResidualBelowPhysicalEnvelope =
      ≤ℝ-trans
        (sourceResidualBelowDyadic source
          (Graph.ymGraphDist
            (R444.leftMark data)
            (R444.rightMark data)))
        (Embed.orderPreserving embedding
          (R450.selectedHalfDecayBelowEuclideanTime physical))
  }

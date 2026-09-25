{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedExpansionTheoremExact where

------------------------------------------------------------------------
-- LITERAL TWO-WILSON MARKED POLYMER EXPANSION: CANONICAL SOURCE THEOREM
--
-- This is the source-native completion object for the W1/W3 lane.
--
-- The preferred carrier is R444:
--   * both Wilson/source marks are structural in every retained term;
--   * every retained common-Y fibre is structurally nonempty;
--   * the four-stage R410 operator layout is canonical;
--   * CMP116 (1.26)--(1.29) source domains and fixed-Y shells are attached on
--     the same literal domain carrier.
--
-- R453 compiles an actual connected-core path into the only distance inequality
-- required by R448.  R445 identifies the absolute selected differentiated
-- boundary with the embedded literal mixed-log Wilson response.  R448/R415 then
-- perform the differentiated fixed-Y/outer-shell estimate.
--
-- No printed-J = Wilson equality and no generic extensionActivity = Wilson
-- cluster-weight equality occurs in this theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _≤ℝ_)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116R429MixedLogResponseRound445Exact as R445
import DASHI.Physics.YangMills.BalabanCMP116CanonicalB12Round446Exact as R446
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalDecayRound451Exact as R451
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFiniteCovarianceDecayRound452Exact as R452
import DASHI.Physics.YangMills.BalabanCMP116ConnectedCorePathRound453Exact as R453

record LiteralTwoWilsonMarkedExpansionTheorem
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
    (embedding : Embed.OrderedRationalRealEmbedding)
    : Set₁ where
  field
    --------------------------------------------------------------------
    -- W1 same-object theorem at exactly the magnitude strength consumed by
    -- the mass-gap route.
    --------------------------------------------------------------------
    mixedLogResponse :
      R445.R429LiteralMixedLogResponse
        (R444.asR429 data)
        embedding

    --------------------------------------------------------------------
    -- W3 source geometry: an actual connected-core path, not a postulated
    -- graph-distance inequality.
    --------------------------------------------------------------------
    connectedCore :
      R453.ConnectedCorePathGeometry data

    --------------------------------------------------------------------
    -- Physical selected-distance calibration for the source residual weight.
    -- This remains source/physics content; R451 compiles it through the
    -- nonnegative source amplitude.
    --------------------------------------------------------------------
    residualDecay :
      R451.CanonicalPhysicalDecayCalibration
        (R453.asCanonicalDomainSpecificRateSplit data connectedCore)

open LiteralTwoWilsonMarkedExpansionTheorem public

canonicalB12 :
  ∀ {Measure Observable dataSet extension base data embedding} →
  LiteralTwoWilsonMarkedExpansionTheorem
    {Measure = Measure}
    {Observable = Observable}
    {dataSet = dataSet}
    {extension = extension}
    {base = base}
    data embedding →
  R446.CanonicalB12Source data embedding
canonicalB12 theorem = record
  { R446.CanonicalB12Source.response = mixedLogResponse theorem
  }

canonicalGeometry :
  ∀ {Measure Observable dataSet extension base data embedding} →
  (theorem :
    LiteralTwoWilsonMarkedExpansionTheorem
      {Measure = Measure}
      {Observable = Observable}
      {dataSet = dataSet}
      {extension = extension}
      {base = base}
      data embedding) →
  R448.CanonicalDomainSpecificRateSplit data
canonicalGeometry {data = data} theorem =
  R453.asCanonicalDomainSpecificRateSplit data (connectedCore theorem)

asCanonicalFiniteCovarianceDecaySource :
  ∀ {Measure Observable dataSet extension base data embedding} →
  (theorem :
    LiteralTwoWilsonMarkedExpansionTheorem
      {Measure = Measure}
      {Observable = Observable}
      {dataSet = dataSet}
      {extension = extension}
      {base = base}
      data embedding) →
  R452.CanonicalFiniteCovarianceDecaySource data embedding
asCanonicalFiniteCovarianceDecaySource theorem = record
  { R452.CanonicalFiniteCovarianceDecaySource.b12 =
      canonicalB12 theorem
  ; R452.CanonicalFiniteCovarianceDecaySource.geometry =
      canonicalGeometry theorem
  ; R452.CanonicalFiniteCovarianceDecaySource.physicalDecay =
      residualDecay theorem
  }

literalTwoWilsonEmbeddedCovarianceDecay :
  ∀ {Measure Observable dataSet extension base data embedding}
    (theorem :
      LiteralTwoWilsonMarkedExpansionTheorem
        {Measure = Measure}
        {Observable = Observable}
        {dataSet = dataSet}
        {extension = extension}
        {base = base}
        data embedding) →
  Embed.embed embedding
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet
        (R445.cutoff (mixedLogResponse theorem)))
      (R444.leftObservable data)
      (R444.rightObservable data))
  ≤ℝ
  R448.sourceAmplitude (canonicalGeometry theorem) *ℝ
    R451.physicalEnvelope (residualDecay theorem)
      (R451.euclideanTime (residualDecay theorem))
literalTwoWilsonEmbeddedCovarianceDecay theorem =
  R452.embeddedFiniteConnectedCovarianceBelowPhysicalEnvelope
    (asCanonicalFiniteCovarianceDecaySource theorem)

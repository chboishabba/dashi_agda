{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalFiniteCovarianceDecayRound452Exact where

------------------------------------------------------------------------
-- B / ROUND452: CANONICAL FINITE CONNECTED COVARIANCE PHYSICAL DECAY.
--
-- This is the preferred finite-volume B endgame.
--
-- R445:
--   |R429 selected boundary|
--     = embed(finite selected connected-covariance magnitude).
--
-- R448:
--   |R429 selected boundary|
--     <= A_src * W(d_selected).
--
-- R451:
--   W(d_selected) <= physicalEnvelope(time)
--   and therefore
--   |R429 selected boundary| <= A_src * physicalEnvelope(time).
--
-- Combining the SAME-object equality with that bound gives the physical decay
-- theorem directly on the exact finite T5 covariance consumed by R278.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _≤ℝ_; absℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116CanonicalB12Round446Exact as R446
import DASHI.Physics.YangMills.BalabanCMP116R429MixedLogResponseRound445Exact as R445
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalDecayRound451Exact as R451

record CanonicalFiniteCovarianceDecaySource
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (embedding : Embed.OrderedRationalRealEmbedding)
    : Set₁ where
  field
    b12 : R446.CanonicalB12Source data embedding

    geometry :
      R448.CanonicalDomainSpecificRateSplit data

    physicalDecay :
      R451.CanonicalPhysicalDecayCalibration geometry

open CanonicalFiniteCovarianceDecaySource public

embeddedFiniteConnectedCovarianceBelowPhysicalEnvelope :
  ∀ {Measure TestObservable dataSet extension base data embedding}
    (source :
      CanonicalFiniteCovarianceDecaySource
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data embedding) →
  Embed.embed embedding
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet
        (R445.cutoff (R446.response (b12 source))))
      (R444.leftObservable data)
      (R444.rightObservable data))
  ≤ℝ
  R448.sourceAmplitude (geometry source) *ℝ
    R451.physicalEnvelope (physicalDecay source)
      (R451.euclideanTime (physicalDecay source))
embeddedFiniteConnectedCovarianceBelowPhysicalEnvelope
    {data = data} source =
  let
    boundaryBound =
      R451.selectedBoundaryBelowPhysicalEnvelope
        (physicalDecay source)

    sameObject =
      R445.selectedBoundaryMagnitudeIsEmbeddedFiniteCovariance
        (R446.response (b12 source))
  in
  subst
    (λ lower →
      lower ≤ℝ
      R448.sourceAmplitude (geometry source) *ℝ
        R451.physicalEnvelope (physicalDecay source)
          (R451.euclideanTime (physicalDecay source)))
    sameObject
    boundaryBound

round452FiniteCovarianceDecayCompilerLevel : ProofLevel
round452FiniteCovarianceDecayCompilerLevel = machineChecked

-- The finite-volume B route is now reduced to the source inhabitants carried by
-- R444/R445/R448/R451.  Once those are physical, the exact finite connected
-- covariance has the required selected physical decay with no additional
-- localization/counting theorem.
literalRound452FiniteCovarianceDecaySourceLevel : ProofLevel
literalRound452FiniteCovarianceDecaySourceLevel = conditional

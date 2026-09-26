{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonR415CompletionExact where

------------------------------------------------------------------------
-- Literal two-Wilson R415 completion.
--
-- This owner composes the strongest existing source-native CMP116 lane:
--
--   R444 literal twice-marked four-stage terms
--   R445 selected boundary = literal mixed-log magnitude
--   R453 connected-core path -> d_selected <= d_k(Y)
--   R448 source (1.26)--(1.29) rate split -> R415 decay
--   R451 selected residual -> physical-time envelope
--   R452 exact finite connected covariance decay.
--
-- The theorem is deliberately at magnitude strength: that is exactly what the
-- mass-gap consumer uses, and avoids inventing a signed rational/real equality.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanCMP116CanonicalTwiceMarkedFourStageRound444Exact as R444
import DASHI.Physics.YangMills.BalabanCMP116R429MixedLogResponseRound445Exact as R445
import DASHI.Physics.YangMills.BalabanCMP116CanonicalB12Round446Exact as R446
import DASHI.Physics.YangMills.BalabanCMP116CanonicalDomainRateSplitRound448Exact as R448
import DASHI.Physics.YangMills.BalabanCMP116ConnectedCorePathRound453Exact as R453
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPhysicalDecayRound451Exact as R451
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFiniteCovarianceDecayRound452Exact as R452

record LiteralTwoWilsonR415Source
    {Measure Observable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure Observable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (data :
      R444.CanonicalTwiceMarkedFourStageData
        {Measure = Measure} {TestObservable = Observable}
        {dataSet = dataSet} {extension = extension} base)
    (embedding : Embed.OrderedRationalRealEmbedding)
    : Set₁ where
  field
    response :
      R445.R429LiteralMixedLogResponse
        (R444.asR429 data)
        embedding

    connectedCore :
      R453.ConnectedCorePathGeometry data

    physicalDecay :
      R451.CanonicalPhysicalDecayCalibration
        (R453.asCanonicalDomainSpecificRateSplit data connectedCore)

open LiteralTwoWilsonR415Source public

geometry :
  ∀ {Measure Observable dataSet extension base data embedding} →
  (source :
    LiteralTwoWilsonR415Source
      {Measure = Measure} {Observable = Observable}
      {dataSet = dataSet} {extension = extension} {base = base}
      data embedding) →
  R448.CanonicalDomainSpecificRateSplit data
geometry {data = data} source =
  R453.asCanonicalDomainSpecificRateSplit data (connectedCore source)

b12 :
  ∀ {Measure Observable dataSet extension base data embedding} →
  LiteralTwoWilsonR415Source
    {Measure = Measure} {Observable = Observable}
    {dataSet = dataSet} {extension = extension} {base = base}
    data embedding →
  R446.CanonicalB12Source data embedding
b12 source = record
  { R446.CanonicalB12Source.response = response source
  }

asFiniteCovarianceDecay :
  ∀ {Measure Observable dataSet extension base data embedding} →
  (source :
    LiteralTwoWilsonR415Source
      {Measure = Measure} {Observable = Observable}
      {dataSet = dataSet} {extension = extension} {base = base}
      data embedding) →
  R452.CanonicalFiniteCovarianceDecaySource data embedding
asFiniteCovarianceDecay source = record
  { R452.CanonicalFiniteCovarianceDecaySource.b12 = b12 source
  ; R452.CanonicalFiniteCovarianceDecaySource.geometry = geometry source
  ; R452.CanonicalFiniteCovarianceDecaySource.physicalDecay =
      physicalDecay source
  }

literalTwoWilsonFiniteCovarianceDecay :
  ∀ {Measure Observable dataSet extension base data embedding}
    (source :
      LiteralTwoWilsonR415Source
        {Measure = Measure} {Observable = Observable}
        {dataSet = dataSet} {extension = extension} {base = base}
        data embedding) →
  Embed.embed embedding
    (R278.connectedCovarianceMagnitude extension
      (Gram.measureSequence dataSet
        (R445.cutoff (response source)))
      (R444.leftObservable data)
      (R444.rightObservable data))
  ≤ℝ
  R448.sourceAmplitude (geometry source) *ℝ
    R451.physicalEnvelope (physicalDecay source)
      (R451.euclideanTime (physicalDecay source))
literalTwoWilsonFiniteCovarianceDecay source =
  R452.embeddedFiniteConnectedCovarianceBelowPhysicalEnvelope
    (asFiniteCovarianceDecay source)

literalTwoWilsonR415CompilerLevel : ProofLevel
literalTwoWilsonR415CompilerLevel = machineChecked

-- These are the irreducible source-native leaves.  They are not manufactured
-- by this compiler.
literalTwoWilsonR444TermConstructionLevel : ProofLevel
literalTwoWilsonR444TermConstructionLevel =
  R444.literalRound444TwiceDifferentiatedTermConstructionAndScalarizationLevel

literalTwoWilsonR445MixedLogIdentificationLevel : ProofLevel
literalTwoWilsonR445MixedLogIdentificationLevel =
  R445.literalRound445R429SelectedBoundaryMixedLogIdentificationLevel

literalTwoWilsonR453ConnectedCoreLevel : ProofLevel
literalTwoWilsonR453ConnectedCoreLevel =
  R453.literalRound453CMP116ConnectedCorePathLevel

literalTwoWilsonR451PhysicalCalibrationLevel : ProofLevel
literalTwoWilsonR451PhysicalCalibrationLevel =
  R451.literalRound451ResidualToPhysicalEnvelopeLevel

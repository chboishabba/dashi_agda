module DASHI.Physics.Semiconductor.Device.LitavisSPADConsumerSafeReductionExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Physics.Semiconductor.Device.LitavisSPADMultimodalObservationExact as Litavis

------------------------------------------------------------------------
-- LITAVIS SPAD CONSUMER-SAFE ON-SENSOR REDUCTION
--
-- Existing DASHI query-indexed adequacy is the owner of the theorem shape.
-- This file only instantiates it for a finite photon-event reduction fixture.
--
-- The Litavis company release motivates the architectural possibility of
-- in-pixel histogramming / event processing.  It does not prove that a chosen
-- reduction is safe for every downstream consumer.  Safety remains indexed by
-- the declared consumer query.
------------------------------------------------------------------------

bruschiniSPADReviewSource : Source.AttributedSource
bruschiniSPADReviewSource =
  Source.mkDOISource
    "Claudio Bruschini; Harald Homulle; Ivan Michel Antolovic; Samuel Burri; Edoardo Charbon"
    "Single-photon avalanche diode imagers in biophotonics: review and outlook"
    "Light: Science & Applications 8, Article 87"
    "2019"
    "10.1038/s41377-019-0191-5"
    "https://www.nature.com/articles/s41377-019-0191-5"
    Source.academicArticleSource
    "general SPAD architecture precedent: on-/in-pixel timing and processing, spatial/temporal granularity trade-offs, histogram generation and data-rate reduction; does not establish Litavis-specific measurements or this DASHI factorisation theorem"
    Source.publicAttribution

zhangInPixelHistogramSource : Source.AttributedSource
zhangInPixelHistogramSource =
  Source.mkDOISource
    "Chao Zhang; Ning Zhang; Zhijie Ma; Letian Wang; Yu Qin; Jieyang Jia; Kai Zang"
    "A 240 x 160 3D-Stacked SPAD dToF Image Sensor With Rolling Shutter and In-Pixel Histogram for Mobile Devices"
    "IEEE Open Journal of the Solid-State Circuits Society 2, 3-11"
    "2021"
    "10.1109/OJSSCS.2021.3118332"
    "https://doi.org/10.1109/OJSSCS.2021.3118332"
    Source.academicArticleSource
    "targeted engineering precedent: partial histogramming readout compresses photon events into in-pixel histograms and incomplete fine histograms require an explicit distortion treatment; not a Litavis benchmark and not proof of the repository-local consumer-safety theorem"
    Source.publicAttribution

reductionSourceAtlas : Source.AttributedSourceAtlas
reductionSourceAtlas =
  Source.mkSourceAtlas
    "Litavis SPAD consumer-safe reduction source snowball"
    "DASHI.Physics.Semiconductor.Device.LitavisSPADConsumerSafeReductionExact"
    (Litavis.singularPhotonicsLitavisRelease ∷
     Litavis.interestingEngineeringLitavisArticle ∷
     bruschiniSPADReviewSource ∷
     zhangInPixelHistogramSource ∷ [])
    "separates the Litavis launch architecture claim, secondary discovery report, general SPAD processing review, and a targeted in-pixel histogram compression precedent; none imports proof of universal reduction safety"

reductionSourceCount : Nat
reductionSourceCount = Source.sourceCount (Source.sources reductionSourceAtlas)

reductionSourceCountIsFour : reductionSourceCount ≡ 4
reductionSourceCountIsFour = refl

------------------------------------------------------------------------
-- Finite event fixture.
--
-- eventA and eventB have the same coarse histogram bin but different exact
-- timestamps.  A histogram-reduced output therefore pays the histogram-bin
-- consumer while failing the exact-timestamp consumer.  A joined observation
-- that retains both coordinates pays both declared consumers.
------------------------------------------------------------------------

data PhotonEventState : Set where
  eventA eventB : PhotonEventState

data HistogramReduction : Set where
  sameHistogramBin : HistogramReduction

data ExactTimestampObservation : Set where
  timestampA timestampB : ExactTimestampObservation

data JoinedReduction : Set where
  joinedA joinedB : JoinedReduction

data ReductionQuery : Set where
  histogramBinQuery exactTimestampQuery : ReductionQuery

data ReductionAnswer : Set where
  histogramBinAnswer : ReductionAnswer
  timestampAnswerA timestampAnswerB : ReductionAnswer

histogramReduction : PhotonEventState → HistogramReduction
histogramReduction eventA = sameHistogramBin
histogramReduction eventB = sameHistogramBin

exactTimestampObservation : PhotonEventState → ExactTimestampObservation
exactTimestampObservation eventA = timestampA
exactTimestampObservation eventB = timestampB

joinedReduction : PhotonEventState → JoinedReduction
joinedReduction eventA = joinedA
joinedReduction eventB = joinedB

reductionAnswer : ReductionQuery → PhotonEventState → ReductionAnswer
reductionAnswer histogramBinQuery eventA = histogramBinAnswer
reductionAnswer histogramBinQuery eventB = histogramBinAnswer
reductionAnswer exactTimestampQuery eventA = timestampAnswerA
reductionAnswer exactTimestampQuery eventB = timestampAnswerB

reductionSemantics :
  Query.QuerySemantics PhotonEventState ReductionQuery ReductionAnswer
reductionSemantics = Query.querySemantics reductionAnswer

HistogramReductionAdequacy : Set₁
HistogramReductionAdequacy =
  Query.AdequateFor
    histogramReduction
    reductionSemantics
    histogramBinQuery

ExactTimestampReductionDefect : Set₁
ExactTimestampReductionDefect =
  Query.QueryAdequacyDefect
    histogramReduction
    reductionSemantics
    exactTimestampQuery

JoinedHistogramAdequacy : Set₁
JoinedHistogramAdequacy =
  Query.AdequateFor
    joinedReduction
    reductionSemantics
    histogramBinQuery

JoinedTimestampAdequacy : Set₁
JoinedTimestampAdequacy =
  Query.AdequateFor
    joinedReduction
    reductionSemantics
    exactTimestampQuery

histogramReductionAdequate : HistogramReductionAdequacy
histogramReductionAdequate =
  Query.factorsForQuery
    (λ observation → histogramBinAnswer)
    (λ state → refl)

exactTimestampReductionDefect : ExactTimestampReductionDefect
exactTimestampReductionDefect =
  Query.queryAdequacyDefect
    eventA
    eventB
    refl
    (λ ())

histogramReductionCannotPayExactTimestamp :
  Query.AdequateFor
    histogramReduction
    reductionSemantics
    exactTimestampQuery →
  ⊥
histogramReductionCannotPayExactTimestamp =
  Query.queryAdequacyDefectBlocksFactorisation exactTimestampReductionDefect

joinedHistogramAnswer : JoinedReduction → ReductionAnswer
joinedHistogramAnswer joinedA = histogramBinAnswer
joinedHistogramAnswer joinedB = histogramBinAnswer

joinedTimestampAnswer : JoinedReduction → ReductionAnswer
joinedTimestampAnswer joinedA = timestampAnswerA
joinedTimestampAnswer joinedB = timestampAnswerB

joinedHistogramAdequate : JoinedHistogramAdequacy
joinedHistogramAdequate =
  Query.factorsForQuery joinedHistogramAnswer factor
  where
    factor : (state : PhotonEventState) →
      reductionAnswer histogramBinQuery state ≡
      joinedHistogramAnswer (joinedReduction state)
    factor eventA = refl
    factor eventB = refl

joinedTimestampAdequate : JoinedTimestampAdequacy
joinedTimestampAdequate =
  Query.factorsForQuery joinedTimestampAnswer factor
  where
    factor : (state : PhotonEventState) →
      reductionAnswer exactTimestampQuery state ≡
      joinedTimestampAnswer (joinedReduction state)
    factor eventA = refl
    factor eventB = refl

record JoinedReductionAdequacy : Set₁ where
  constructor joined-reduction-adequacy
  field
    histogramConsumerPaid : JoinedHistogramAdequacy
    exactTimestampConsumerPaid : JoinedTimestampAdequacy

open JoinedReductionAdequacy public

joinedReductionAdequate : JoinedReductionAdequacy
joinedReductionAdequate =
  joined-reduction-adequacy
    joinedHistogramAdequate
    joinedTimestampAdequate

------------------------------------------------------------------------
-- Source and interpretation firewalls.
------------------------------------------------------------------------

record ReductionSourceBoundary : Set where
  constructor reduction-source-boundary
  field
    litavisPrimarySourceRetained : Bool
    litavisPrimarySourceRetainedIsTrue : litavisPrimarySourceRetained ≡ true
    interestingEngineeringRetainedAsSecondary : Bool
    interestingEngineeringRetainedAsSecondaryIsTrue :
      interestingEngineeringRetainedAsSecondary ≡ true
    academicSPADPrecedentRetained : Bool
    academicSPADPrecedentRetainedIsTrue : academicSPADPrecedentRetained ≡ true
    targetedHistogramCompressionPrecedentRetained : Bool
    targetedHistogramCompressionPrecedentRetainedIsTrue :
      targetedHistogramCompressionPrecedentRetained ≡ true
    academicPrecedentIsLitavisBenchmark : Bool
    academicPrecedentIsLitavisBenchmarkIsFalse :
      academicPrecedentIsLitavisBenchmark ≡ false
    sourceClaimsProveConsumerSafety : Bool
    sourceClaimsProveConsumerSafetyIsFalse :
      sourceClaimsProveConsumerSafety ≡ false
    citationCreatesScientificAuthority : Bool
    citationCreatesScientificAuthorityIsFalse :
      citationCreatesScientificAuthority ≡ false

canonicalReductionSourceBoundary : ReductionSourceBoundary
canonicalReductionSourceBoundary =
  reduction-source-boundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl

record ReductionSafetyBoundary : Set where
  constructor reduction-safety-boundary
  field
    lessOutputDataImpliesNoInformationLoss : Bool
    lessOutputDataImpliesNoInformationLossIsFalse :
      lessOutputDataImpliesNoInformationLoss ≡ false
    histogramAdequacyImpliesExactTimestampAdequacy : Bool
    histogramAdequacyImpliesExactTimestampAdequacyIsFalse :
      histogramAdequacyImpliesExactTimestampAdequacy ≡ false
    safetyIsIndexedByConsumer : Bool
    safetyIsIndexedByConsumerIsTrue : safetyIsIndexedByConsumer ≡ true
    missingCoordinateCanBeRepairedByJoinedObserver : Bool
    missingCoordinateCanBeRepairedByJoinedObserverIsTrue :
      missingCoordinateCanBeRepairedByJoinedObserver ≡ true
    softwareConfigurabilityMakesEveryModeEquivalent : Bool
    softwareConfigurabilityMakesEveryModeEquivalentIsFalse :
      softwareConfigurabilityMakesEveryModeEquivalent ≡ false

canonicalReductionSafetyBoundary : ReductionSafetyBoundary
canonicalReductionSafetyBoundary =
  reduction-safety-boundary
    false refl
    false refl
    true refl
    true refl
    false refl

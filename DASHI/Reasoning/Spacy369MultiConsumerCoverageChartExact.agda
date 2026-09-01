module DASHI.Reasoning.Spacy369MultiConsumerCoverageChartExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Reasoning.SpacyPNF369DialecticBridgeExact as Bridge369
import DASHI.Reasoning.SpacyNegatedCoordinationScopeTraceExact as Trace
import DASHI.Reasoning.Spacy369MultiConsumerSharedProbeExact as Shared
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Synthesis

------------------------------------------------------------------------
-- A SECOND, EXPLICITLY DISTINCT 369 CHART: CONSUMER-COVERAGE STATUS.
--
-- The materialised parser already has its own 369 dialectic atom describing
-- dispositions of two parser-supported candidate readings plus adjudication.
-- This owner does not overload that atom.  It reuses the same T^3=27 carrier
-- only to chart three consumer-coverage coordinates after the shared context
-- probe: subject closed, governed-standing closed, closure-residual unresolved.
------------------------------------------------------------------------

data ConsumerCoverageStatus : Set where
  coverageOpen coverageSuspended coverageClosed : ConsumerCoverageStatus

coverageTrit : ConsumerCoverageStatus → Base.TriTruth
coverageTrit coverageOpen = Base.tri-low
coverageTrit coverageSuspended = Base.tri-mid
coverageTrit coverageClosed = Base.tri-high

sharedProbeCoverageChart : Synthesis.SynthesisChoice27
sharedProbeCoverageChart =
  Synthesis.makeSynthesisChoice
    (coverageTrit coverageClosed)
    (coverageTrit coverageClosed)
    (coverageTrit coverageSuspended)

sharedProbeComparisonCoordinates :
  Synthesis.comparisonOfSynthesis sharedProbeCoverageChart
  ≡ (Base.tri-high , Base.tri-high)
sharedProbeComparisonCoordinates = refl

sharedProbeClosureCoordinate :
  Synthesis.synthesisCoordinate sharedProbeCoverageChart
  ≡ Base.tri-mid
sharedProbeClosureCoordinate = refl

------------------------------------------------------------------------
-- Proof-bearing anchors behind the chart coordinates.
------------------------------------------------------------------------

subjectCoordinateClosed = Shared.sharedProbeClosesSubjectConsumer
standingCoordinateClosed = Shared.sharedProbeClosesStandingConsumer
closureCoordinateStillOpen = Shared.sharedProbeDoesNotCloseClosureConsumer

------------------------------------------------------------------------
-- The coverage chart is NOT the materialised parser-review chart.
--
-- The revised parser chart has left disposition reject -> tri-low, whereas the
-- shared-probe coverage chart has first coordinate closed -> tri-high.  So the
-- two T^3 values are constructively distinct despite sharing the 27 carrier.
------------------------------------------------------------------------

coverageChartNotParserReviewChart :
  sharedProbeCoverageChart ≡ Bridge369.chart Trace.revised369 → ⊥
coverageChartNotParserReviewChart same =
  highNotLow
    (cong proj₁ same)
  where
    highNotLow : Base.tri-high ≡ Base.tri-low → ⊥
    highNotLow ()

------------------------------------------------------------------------
-- This separation is the exact anti-overloading rule: same carrier/dimension
-- may support different typed observer languages, but carrier equality does not
-- identify their coordinates or semantic authority.
------------------------------------------------------------------------

record Spacy369MultiConsumerCoverageChartBoundary : Set where
  constructor spacy369MultiConsumerCoverageChartBoundary
  field
    consumerCoverageMayUseExistingTernary27Carrier : Bool
    consumerCoverageMayUseExistingTernary27CarrierIsTrue :
      consumerCoverageMayUseExistingTernary27Carrier ≡ true
    coverageChartEqualsParserDialecticChart : Bool
    coverageChartEqualsParserDialecticChartIsFalse :
      coverageChartEqualsParserDialecticChart ≡ false
    closedSubjectAndStandingForceClosureResidualClosed : Bool
    closedSubjectAndStandingForceClosureResidualClosedIsFalse :
      closedSubjectAndStandingForceClosureResidualClosed ≡ false
    ternaryMidMeansLogicalFalsehood : Bool
    ternaryMidMeansLogicalFalsehoodIsFalse :
      ternaryMidMeansLogicalFalsehood ≡ false
    sameTwentySevenCarrierMeansSameSemanticAuthority : Bool
    sameTwentySevenCarrierMeansSameSemanticAuthorityIsFalse :
      sameTwentySevenCarrierMeansSameSemanticAuthority ≡ false

canonicalSpacy369MultiConsumerCoverageChartBoundary :
  Spacy369MultiConsumerCoverageChartBoundary
canonicalSpacy369MultiConsumerCoverageChartBoundary =
  spacy369MultiConsumerCoverageChartBoundary
    true refl
    false refl
    false refl
    false refl
    false refl

module DASHI.Reasoning.Spacy369MultiConsumerCoverageFiltrationExact where

open import DASHI.Core.Prelude

import DASHI.Reasoning.Spacy369FeministLacanConsumerRelativeExact as Consumer
import DASHI.Reasoning.Spacy369MultiConsumerSharedProbeExact as Shared
import DASHI.Reasoning.Spacy369MultiConsumerCoveragePathResidueExact as Path

------------------------------------------------------------------------
-- CONSUMER-RELATIVE COVERAGE FILTRATION.
--
-- Observation / audit depth is not a global confidence scalar.  Different
-- consumers close at different stages over the same materialised analysis.
------------------------------------------------------------------------

data CoverageDepth : Set where
  depth0 depth1 depth2 : CoverageDepth

data DeclaredConsumer : Set where
  operationalConsumer
  subjectPositionConsumer
  governedStandingConsumer
  closureResidualConsumer
  : DeclaredConsumer

data ClosureStatus : Set where
  stillOpen closedHere : ClosureStatus

coverageStatus : CoverageDepth → DeclaredConsumer → ClosureStatus
coverageStatus depth0 operationalConsumer = closedHere
coverageStatus depth0 subjectPositionConsumer = stillOpen
coverageStatus depth0 governedStandingConsumer = stillOpen
coverageStatus depth0 closureResidualConsumer = stillOpen

coverageStatus depth1 operationalConsumer = closedHere
coverageStatus depth1 subjectPositionConsumer = closedHere
coverageStatus depth1 governedStandingConsumer = closedHere
coverageStatus depth1 closureResidualConsumer = stillOpen

coverageStatus depth2 operationalConsumer = closedHere
coverageStatus depth2 subjectPositionConsumer = closedHere
coverageStatus depth2 governedStandingConsumer = closedHere
coverageStatus depth2 closureResidualConsumer = closedHere

------------------------------------------------------------------------
-- Exact anchors for each filtration stage.
------------------------------------------------------------------------

operationalClosedAtDepth0 = Consumer.operationalClosureReceipt
subjectClosedAtDepth1 = Shared.sharedProbeClosesSubjectConsumer
standingClosedAtDepth1 = Shared.sharedProbeClosesStandingConsumer
closureStillOpenAtDepth1 = Shared.sharedProbeDoesNotCloseClosureConsumer

coverageChartAtDepth : CoverageDepth → Set
coverageChartAtDepth depth0 = Path.stageChart Path.startStage ≡ Path.initialCoverage
coverageChartAtDepth depth1 = Path.stageChart Path.sharedStage ≡ Path.afterSharedContextProbe
coverageChartAtDepth depth2 = Path.stageChart Path.terminalStage ≡ Path.fullyClosedCoverage

coverageChartDepth0 : coverageChartAtDepth depth0
coverageChartDepth0 = refl

coverageChartDepth1 : coverageChartAtDepth depth1
coverageChartDepth1 = refl

coverageChartDepth2 : coverageChartAtDepth depth2
coverageChartDepth2 = refl

------------------------------------------------------------------------
-- First closure depth is consumer indexed.
------------------------------------------------------------------------

data FirstClosureAt : DeclaredConsumer → CoverageDepth → Set where
  operationalFirstAt0 : FirstClosureAt operationalConsumer depth0
  subjectFirstAt1 : FirstClosureAt subjectPositionConsumer depth1
  standingFirstAt1 : FirstClosureAt governedStandingConsumer depth1
  closureResidualFirstAt2 : FirstClosureAt closureResidualConsumer depth2

operationalAndSubjectClosureDepthsDiffer :
  depth0 ≡ depth1 → ⊥
operationalAndSubjectClosureDepthsDiffer ()

subjectAndClosureResidualDepthsDiffer :
  depth1 ≡ depth2 → ⊥
subjectAndClosureResidualDepthsDiffer ()

------------------------------------------------------------------------
-- Closing a shallower consumer does not transfer to a deeper consumer.
------------------------------------------------------------------------

operationalClosureDoesNotForceSubjectClosureAtDepth0 :
  coverageStatus depth0 operationalConsumer
  ≡ coverageStatus depth0 subjectPositionConsumer → ⊥
operationalClosureDoesNotForceSubjectClosureAtDepth0 ()

subjectClosureDoesNotForceClosureResidualAtDepth1 :
  coverageStatus depth1 subjectPositionConsumer
  ≡ coverageStatus depth1 closureResidualConsumer → ⊥
subjectClosureDoesNotForceClosureResidualAtDepth1 ()

------------------------------------------------------------------------
-- A later stage preserves already-earned finite coverage in this fixture.
-- This is a local filtration property, not a theorem that every future evidence
-- update globally preserves every certificate.
------------------------------------------------------------------------

subjectRemainsClosedAtDepth2 :
  coverageStatus depth2 subjectPositionConsumer ≡ closedHere
subjectRemainsClosedAtDepth2 = refl

standingRemainsClosedAtDepth2 :
  coverageStatus depth2 governedStandingConsumer ≡ closedHere
standingRemainsClosedAtDepth2 = refl

operationalRemainsClosedAtEveryDepth :
  (depth : CoverageDepth) →
  coverageStatus depth operationalConsumer ≡ closedHere
operationalRemainsClosedAtEveryDepth depth0 = refl
operationalRemainsClosedAtEveryDepth depth1 = refl
operationalRemainsClosedAtEveryDepth depth2 = refl

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record Spacy369MultiConsumerCoverageFiltrationBoundary : Set where
  constructor spacy369MultiConsumerCoverageFiltrationBoundary
  field
    oneUniversalClosureDepthForAllConsumers : Bool
    oneUniversalClosureDepthForAllConsumersIsFalse :
      oneUniversalClosureDepthForAllConsumers ≡ false
    operationalClosureRequiresFullAuditDepth : Bool
    operationalClosureRequiresFullAuditDepthIsFalse :
      operationalClosureRequiresFullAuditDepth ≡ false
    subjectClosureAtDepth1ForcesClosureResidualClosure : Bool
    subjectClosureAtDepth1ForcesClosureResidualClosureIsFalse :
      subjectClosureAtDepth1ForcesClosureResidualClosure ≡ false
    deeperAuditDepthMeansHigherTruthValue : Bool
    deeperAuditDepthMeansHigherTruthValueIsFalse :
      deeperAuditDepthMeansHigherTruthValue ≡ false
    filtrationDepthIsHistoricalTime : Bool
    filtrationDepthIsHistoricalTimeIsFalse :
      filtrationDepthIsHistoricalTime ≡ false
    closedConsumerCanRemainClosedWhileOtherConsumersNeedMoreInformation : Bool
    closedConsumerCanRemainClosedWhileOtherConsumersNeedMoreInformationIsTrue :
      closedConsumerCanRemainClosedWhileOtherConsumersNeedMoreInformation ≡ true

canonicalSpacy369MultiConsumerCoverageFiltrationBoundary :
  Spacy369MultiConsumerCoverageFiltrationBoundary
canonicalSpacy369MultiConsumerCoverageFiltrationBoundary =
  spacy369MultiConsumerCoverageFiltrationBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

module DASHI.Interop.IntrospectiveProofLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Interop.DialecticalMaterialProofSearchExperimentLoopExact as Loop
import DASHI.Interop.DialecticalMaterialSourceDiligenceReopeningExact as MaterialSource
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as Diligence
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- INTROSPECTIVE PROOF LOOP
--
-- This module formalises the repository workflow used when inspecting a live
-- proof/search implementation:
--
--   model the current carrier -> visualise the actual data/proof flow ->
--   inspect the visual for mismatches -> encode only the mismatch that survives
--   inspection -> recompute the consumer-relative proof state.
--
-- The visual is diagnostic only.  It creates neither evidence nor closure.
------------------------------------------------------------------------

private
  variable
    system : Fibre.ConsumerIndexedFibreSystem

------------------------------------------------------------------------
-- ZKP-shaped audit frame.  These are references to the already-existing owners,
-- not a second ontology for them.
------------------------------------------------------------------------

record ZKPFrame : Set where
  constructor zkp-frame
  field
    organizationReference : String
    requestOrRFPReference : String
    codeReference : String
    stateReference : String
    observerOrLatticeReference : String
    proposalReference : String
    goalReference : String
    liveGapFunctionReference : String

open ZKPFrame public

------------------------------------------------------------------------
-- The generic refinement scheduler intentionally leaves MissingCoordinate and
-- Producer application-defined.  A source route therefore needs an explicit
-- adapter into the existing source-diligence/search vocabulary.
------------------------------------------------------------------------

record SourceRouteAlignment
    {system : Fibre.ConsumerIndexedFibreSystem}
    (schedule : Scheduler.RefinementSchedule system) : Set₁ where
  constructor source-route-alignment
  field
    sourceGapFor :
      Scheduler.MissingCoordinate schedule →
      Diligence.SourceDiligenceGap

    producerToSearch :
      Scheduler.Producer schedule →
      Search.ProducerClass

    scheduledProducerAgrees :
      (coordinate : Scheduler.MissingCoordinate schedule) →
      producerToSearch (Scheduler.producerFor schedule coordinate) ≡
      Diligence.producerForSourceDiligenceGap (sourceGapFor coordinate)

open SourceRouteAlignment public

------------------------------------------------------------------------
-- Finding from the visual audit: the existing experiment route carries the
-- concrete consumer residual, but the source-reopening constructor is otherwise
-- independent of that residual.  This demand binds a source reopening back to
-- the exact live missing coordinate and scheduled producer.
------------------------------------------------------------------------

record ConsumerDefectSourceDemand
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (alignment : SourceRouteAlignment schedule)
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer) : Set₁ where
  constructor consumer-defect-source-demand
  field
    reopening : MaterialSource.DialecticalSourceReopening

    reopeningGapMatchesResidual :
      MaterialSource.firstMissingSourceCoordinate reopening ≡
      sourceGapFor alignment (Scheduler.missingCoordinate liveResidual)

    reopeningProducerMatchesResidual :
      MaterialSource.requiredProducer reopening ≡
      producerToSearch alignment (Scheduler.producer liveResidual)

open ConsumerDefectSourceDemand public

sourceRoutePaysScheduledGap :
  ∀ {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    {alignment : SourceRouteAlignment schedule}
    {liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer} →
  (demand : ConsumerDefectSourceDemand alignment liveResidual) →
  MaterialSource.firstMissingSourceCoordinate (reopening demand) ≡
  sourceGapFor alignment (Scheduler.missingCoordinate liveResidual)
sourceRoutePaysScheduledGap = reopeningGapMatchesResidual

sourceRouteUsesScheduledProducer :
  ∀ {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    {alignment : SourceRouteAlignment schedule}
    {liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer} →
  (demand : ConsumerDefectSourceDemand alignment liveResidual) →
  MaterialSource.requiredProducer (reopening demand) ≡
  producerToSearch alignment (Scheduler.producer liveResidual)
sourceRouteUsesScheduledProducer = reopeningProducerMatchesResidual

------------------------------------------------------------------------
-- The experiment route already carries a residual.  For an introspective round
-- we additionally require that it is the same live residual currently under
-- review, rather than merely another defect for the same consumer.
------------------------------------------------------------------------

record ConsumerDefectExperimentBinding
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer) : Set₂ where
  constructor consumer-defect-experiment-binding
  field
    demand : Loop.ConsumerDefectExperimentDemand schedule consumer
    demandResidualMatchesLiveResidual :
      Loop.residual demand ≡ liveResidual

open ConsumerDefectExperimentBinding public

------------------------------------------------------------------------
-- A reviewed visual may expose a formal mismatch, but the finding itself does
-- not count as proof progress.  Progress is represented only by one of the three
-- typed routes below.
------------------------------------------------------------------------

data VisualAuditFinding : Set where
  sourceRouteNeedsLiveResidualBinding : VisualAuditFinding
  noAdditionalFormalMismatchObserved : VisualAuditFinding

record ReviewedVisualization : Set where
  constructor reviewed-visualization
  field
    visualizationReference : String
    finding : VisualAuditFinding
    plainLanguageWalkthroughReference : String

open ReviewedVisualization public

data IntrospectiveProgress
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (alignment : SourceRouteAlignment schedule)
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer) : Set₂ where

  progressByBoundSource :
    ConsumerDefectSourceDemand alignment liveResidual →
    IntrospectiveProgress alignment liveResidual

  progressByBoundExperiment :
    ConsumerDefectExperimentBinding liveResidual →
    IntrospectiveProgress alignment liveResidual

  progressByConsumerClosure :
    Fibre.ConsumerRefinementReceipt system consumer →
    IntrospectiveProgress alignment liveResidual

record VerifiedIntrospectiveRound
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (alignment : SourceRouteAlignment schedule)
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer) : Set₂ where
  constructor verified-introspective-round
  field
    frame : ZKPFrame
    visualReview : ReviewedVisualization
    progress : IntrospectiveProgress alignment liveResidual

open VerifiedIntrospectiveRound public

------------------------------------------------------------------------
-- Firewalls: explanatory artefacts and audit metadata cannot manufacture a
-- successful formal step.
------------------------------------------------------------------------

data VisualizationCreatesEvidencePermission : Set where

data VisualizationCreatesConsumerClosurePermission : Set where
data AuditFindingCreatesProgressPermission : Set where

visualizationDoesNotCreateEvidence : VisualizationCreatesEvidencePermission → ⊥
visualizationDoesNotCreateEvidence ()

visualizationDoesNotCreateConsumerClosure :
  VisualizationCreatesConsumerClosurePermission → ⊥
visualizationDoesNotCreateConsumerClosure ()

auditFindingDoesNotCreateProgress : AuditFindingCreatesProgressPermission → ⊥
auditFindingDoesNotCreateProgress ()

record IntrospectiveProofLoopBoundary : Set where
  constructor introspective-proof-loop-boundary
  field
    visualizationIsDiagnosticOnly : Bool
    sourceRouteMustBindLiveResidual : Bool
    experimentRouteMustBindLiveResidual : Bool
    consumerClosureStillNeedsRefinementReceipt : Bool
    visualAuditMayRevealFormalMismatch : Bool

canonicalIntrospectiveProofLoopBoundary : IntrospectiveProofLoopBoundary
canonicalIntrospectiveProofLoopBoundary =
  introspective-proof-loop-boundary true true true true true

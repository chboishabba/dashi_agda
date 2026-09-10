module DASHI.Interop.IntrospectiveProofLoopExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.BoundAcquisitionDemandExact as Bound
import DASHI.Core.ConsumerIndexedTrajectoryFibreAdequacyExact as Fibre
import DASHI.Core.ConsumerFibreRefinementSchedulerExact as Scheduler
import DASHI.Interop.DialecticalMaterialProofSearchExperimentLoopExact as Loop
import DASHI.Interop.DialecticalMaterialSourceDiligenceReopeningExact as MaterialSource
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as Diligence
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- INTROSPECTIVE PROOF LOOP
------------------------------------------------------------------------

private
  variable
    system : Fibre.ConsumerIndexedFibreSystem

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
-- Application adapter from generic refinement coordinates into the source
-- diligence/search vocabulary.
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

sourceAcquisitionAlignment :
  ∀ {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system} →
  SourceRouteAlignment schedule →
  Bound.AcquisitionAlignment
    (Scheduler.MissingCoordinate schedule)
    Diligence.SourceDiligenceGap
    Search.ProducerClass
    MaterialSource.DialecticalSourceReopening
sourceAcquisitionAlignment {schedule = schedule} alignment =
  Bound.acquisition-alignment
    (sourceGapFor alignment)
    (λ coordinate → producerToSearch alignment (Scheduler.producerFor schedule coordinate))
    MaterialSource.firstMissingSourceCoordinate
    MaterialSource.requiredProducer

------------------------------------------------------------------------
-- Preferred source-demand surface.  Core owns exact requirement/residual/
-- producer binding; this wrapper owns the stronger consumer-residual indexing.
------------------------------------------------------------------------

record ConsumerDefectSourceDemand
    {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    (alignment : SourceRouteAlignment schedule)
    (liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer) : Set₁ where
  constructor consumer-defect-source-demand
  field
    boundDemand :
      Bound.BoundAcquisitionDemand
        (sourceAcquisitionAlignment alignment)
        (Scheduler.missingCoordinate liveResidual)
        (sourceGapFor alignment (Scheduler.missingCoordinate liveResidual))

open ConsumerDefectSourceDemand public

reopening :
  ∀ {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    {alignment : SourceRouteAlignment schedule}
    {liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer} →
  ConsumerDefectSourceDemand alignment liveResidual →
  MaterialSource.DialecticalSourceReopening
reopening demand = Bound.acquisition (boundDemand demand)

sourceRoutePaysScheduledGap :
  ∀ {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    {alignment : SourceRouteAlignment schedule}
    {liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer} →
  (demand : ConsumerDefectSourceDemand alignment liveResidual) →
  MaterialSource.firstMissingSourceCoordinate (reopening demand) ≡
  sourceGapFor alignment (Scheduler.missingCoordinate liveResidual)
sourceRoutePaysScheduledGap demand =
  Bound.acquisitionPaysSelectedResidual (boundDemand demand)

sourceRouteUsesScheduledProducer :
  ∀ {system : Fibre.ConsumerIndexedFibreSystem}
    {schedule : Scheduler.RefinementSchedule system}
    {consumer : Fibre.Consumer system}
    {alignment : SourceRouteAlignment schedule}
    {liveResidual : Scheduler.ConsumerRefinementResidual schedule consumer} →
  (demand : ConsumerDefectSourceDemand alignment liveResidual) →
  MaterialSource.requiredProducer (reopening demand) ≡
  producerToSearch alignment (Scheduler.producer liveResidual)
sourceRouteUsesScheduledProducer {alignment = alignment} {liveResidual = liveResidual} demand =
  trans
    (Bound.acquisitionUsesSelectedProducer (boundDemand demand))
    (sym (cong (producerToSearch alignment)
      (Scheduler.producerIsScheduled liveResidual)))

------------------------------------------------------------------------
-- The experiment route already carries a residual.  For an introspective round
-- require that it is the same live residual currently under review.
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
-- R270 / NS-R592 LESSON: A PROOF TACTIC IS NOT A MANDATORY RESIDUAL.
--
-- A route may be useful, elegant, or currently preferred without being a
-- prerequisite of the consumer.  To label a route mandatory one must prove the
-- universal factorisation statement: EVERY admissible payment of the consumer
-- passes through that route.  A single valid direct bypass refutes mandatory
-- status.  This prevents proof search from growing a decomposition/tactic into
-- a fake theorem debt merely because previous rounds happened to use it.
------------------------------------------------------------------------

record ConsumerRouteAudit
    (Route Payment : Set) : Set₁ where
  field
    PaysConsumer : Payment → Set
    UsesRoute : Route → Payment → Set

open ConsumerRouteAudit public

record MandatoryRoute
    {Route Payment : Set}
    (audit : ConsumerRouteAudit Route Payment)
    (route : Route) : Set₁ where
  field
    everyConsumerPaymentUsesRoute :
      ∀ payment → PaysConsumer audit payment → UsesRoute audit route payment

open MandatoryRoute public

record DirectRouteBypass
    {Route Payment : Set}
    (audit : ConsumerRouteAudit Route Payment)
    (route : Route) : Set₁ where
  field
    directPayment : Payment
    directPaymentPaysConsumer : PaysConsumer audit directPayment
    directPaymentDoesNotUseRoute : UsesRoute audit route directPayment → ⊥

open DirectRouteBypass public

mandatoryRouteContradictsDirectBypass :
  ∀ {Route Payment}
    {audit : ConsumerRouteAudit Route Payment}
    {route : Route} →
  MandatoryRoute audit route →
  DirectRouteBypass audit route →
  ⊥
mandatoryRouteContradictsDirectBypass mandatory bypass =
  directPaymentDoesNotUseRoute bypass
    (everyConsumerPaymentUsesRoute mandatory
      (directPayment bypass)
      (directPaymentPaysConsumer bypass))

data ProofSearchTargetRole : Set where
  canonicalConsumerResidual : ProofSearchTargetRole
  optionalProducerTactic : ProofSearchTargetRole
  compilerConsequence : ProofSearchTargetRole
  verificationOrSubmissionStatus : ProofSearchTargetRole

------------------------------------------------------------------------
-- Closure is multi-coordinate, but metadata cannot pay theorem content.
-- Typechecking, CI, submission, review and external acceptance are important
-- coordinates after theorem content exists; none constructs the missing proof.
------------------------------------------------------------------------

data ClosureCoordinate : Set where
  theoremContent : ClosureCoordinate
  typechecked : ClosureCoordinate
  submitted : ClosureCoordinate
  reviewed : ClosureCoordinate
  externallyAccepted : ClosureCoordinate

record ClosureLedger : Set where
  constructor closure-ledger
  field
    theoremContentClosed : Bool
    typecheckedClosed : Bool
    submittedClosed : Bool
    reviewedClosed : Bool
    externallyAcceptedClosed : Bool

open ClosureLedger public

data StatusCreatesTheoremContentPermission : Set where

statusDoesNotCreateTheoremContent : StatusCreatesTheoremContentPermission → ⊥
statusDoesNotCreateTheoremContent ()

------------------------------------------------------------------------
-- Visual diagnosis remains non-promoting.
------------------------------------------------------------------------

data VisualAuditFinding : Set where
  sourceRouteNeedsLiveResidualBinding : VisualAuditFinding
  producerTacticMistakenForMandatoryResidual : VisualAuditFinding
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
-- Firewalls.
------------------------------------------------------------------------

data VisualizationCreatesEvidencePermission : Set where
data VisualizationCreatesConsumerClosurePermission : Set where
data AuditFindingCreatesProgressPermission : Set where

data PreferredTacticCreatesMandatoryResidualPermission : Set where

visualizationDoesNotCreateEvidence : VisualizationCreatesEvidencePermission → ⊥
visualizationDoesNotCreateEvidence ()

visualizationDoesNotCreateConsumerClosure :
  VisualizationCreatesConsumerClosurePermission → ⊥
visualizationDoesNotCreateConsumerClosure ()

auditFindingDoesNotCreateProgress : AuditFindingCreatesProgressPermission → ⊥
auditFindingDoesNotCreateProgress ()

preferredTacticDoesNotCreateMandatoryResidual :
  PreferredTacticCreatesMandatoryResidualPermission → ⊥
preferredTacticDoesNotCreateMandatoryResidual ()

record IntrospectiveProofLoopBoundary : Set where
  constructor introspective-proof-loop-boundary
  field
    visualizationIsDiagnosticOnly : Bool
    sourceRouteMustBindLiveResidual : Bool
    experimentRouteMustBindLiveResidual : Bool
    consumerClosureStillNeedsRefinementReceipt : Bool
    visualAuditMayRevealFormalMismatch : Bool
    mandatoryRouteNeedsUniversalConsumerFactorization : Bool
    verificationStatusDoesNotCreateTheoremContent : Bool

canonicalIntrospectiveProofLoopBoundary : IntrospectiveProofLoopBoundary
canonicalIntrospectiveProofLoopBoundary =
  introspective-proof-loop-boundary true true true true true true true

module DASHI.Core.HistoricalProducerNextBestActionCompilerBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.CostedMixedConsumerClosingObservationSearchBidiExact as Mixed
import DASHI.Core.HistoricalResponsibilityLineageTraceBidiExact as Historical
import DASHI.Core.HistoricalFirstFailureTraceBidiExact as History
import DASHI.Core.QueryPromotionResidualBidiExact as QueryPromotion
import DASHI.Core.LeastCostConsumerClosingExperimentBidiExact as Closing
import DASHI.Core.DeliberativeCyberneticLoopBidiExact as Delib
import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Core.ProjectionHierarchyCompatibleFibreBidiExact as Projection
import DASHI.Core.FibreRefinementExperimentSelectionBidiExact as Fibre
import DASHI.Core.CostedFibreEliminationChoiceBidiExact as Costed

------------------------------------------------------------------------
-- HISTORICAL PRODUCER -> NEXT-BEST CONSUMER-CLOSING ACTION
--
-- A historical responsibility trace identifies the producer kind currently
-- required by the first missing promotion stage. Candidate information moves
-- enter the search only if an application supplies a separate proof that the
-- candidate can pay that producer obligation. Consumer closure and producer
-- payment remain independent receipts.
------------------------------------------------------------------------

record ProducerActionProblem {Hidden Experiment Decision : Set}
    (prior : Bidi.ResidualFibre Hidden)
    (consumer : Hidden → Decision) : Set₁ where
  constructor producer-action-problem
  field
    snapshot : History.HistoricalPromotionSnapshot
    historicalTrace : Historical.HistoricalResponsibilityLineage snapshot
    Declared : Mixed.MixedClosingCandidate {Hidden} {Experiment} prior consumer → Set
    CanPay :
      Mixed.MixedClosingCandidate {Hidden} {Experiment} prior consumer →
      QueryPromotion.ProducerKind → Set
    paymentPolicyReference : String
    consumerReference : String

open ProducerActionProblem public

requiredProducer :
  ∀ {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision} →
  ProducerActionProblem {Hidden} {Experiment} prior consumer →
  QueryPromotion.ProducerKind
requiredProducer problem =
  Historical.currentProducerKind (historicalTrace problem)

record ProducerEligibleCandidate {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision}
    (problem : ProducerActionProblem {Hidden} {Experiment} prior consumer) : Set₁ where
  constructor producer-eligible-candidate
  field
    candidate : Mixed.MixedClosingCandidate {Hidden} {Experiment} prior consumer
    declared : Declared problem candidate
    paysRequiredProducer : CanPay problem candidate (requiredProducer problem)
    producerPaymentReference : String

open ProducerEligibleCandidate public

record NextBestProducerActionChoice {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision}
    (problem : ProducerActionProblem {Hidden} {Experiment} prior consumer) : Set₁ where
  constructor next-best-producer-action-choice
  field
    selected : ProducerEligibleCandidate problem
    minimalCost :
      (alternative : ProducerEligibleCandidate problem) →
      Mixed.cost (candidate selected) ≤ Mixed.cost (candidate alternative)
    selectionReference : String

open NextBestProducerActionChoice public

selectedNextBestActionClosesConsumer :
  ∀ {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision}
    {problem : ProducerActionProblem {Hidden} {Experiment} prior consumer} →
  (choice : NextBestProducerActionChoice problem) →
  Bidi.PointIdentifies
    (Fibre.posterior
      (Costed.refinement
        (Closing.costed
          (Mixed.closing (candidate (selected choice))))))
    consumer
selectedNextBestActionClosesConsumer choice =
  Closing.closesConsumer (Mixed.closing (candidate (selected choice)))

selectedNextBestActionPaysHistoricalProducer :
  ∀ {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision}
    {problem : ProducerActionProblem {Hidden} {Experiment} prior consumer} →
  (choice : NextBestProducerActionChoice problem) →
  CanPay problem
    (candidate (selected choice))
    (requiredProducer problem)
selectedNextBestActionPaysHistoricalProducer choice =
  paysRequiredProducer (selected choice)

------------------------------------------------------------------------
-- Exact closed-world calibration.
--
-- Reuse the historical missing-transport trace and the existing coarse->middle
-- consumer-closing candidate.  The application-specific payment policy below
-- explicitly licenses that candidate for `proveTransport`; the compiler does
-- not infer this fact from the move label.
------------------------------------------------------------------------

middleMixedClosing :
  Mixed.MixedClosingCandidate
    {Projection.Hidden}
    {Fibre.ToyExperiment}
    Projection.coarseFibre
    Projection.middleDecision
middleMixedClosing =
  Mixed.instrumentalClosingCandidate
    Closing.middleClosingCandidate
    (Delib.baseMove Loop.lookMove)
    1
    "synthetic calibrated look/measurement route"

fineMixedClosing :
  Mixed.MixedClosingCandidate
    {Projection.Hidden}
    {Fibre.ToyExperiment}
    Projection.coarseFibre
    Projection.middleDecision
fineMixedClosing =
  Mixed.instrumentalClosingCandidate
    Closing.fineClosingCandidate
    (Delib.baseMove Loop.lookMove)
    2
    "synthetic finer calibrated look/measurement route"

DeclaredCalibration :
  Mixed.MixedClosingCandidate
    {Projection.Hidden}
    {Fibre.ToyExperiment}
    Projection.coarseFibre
    Projection.middleDecision → Set
DeclaredCalibration candidate = ⊤

CalibrationCanPay :
  Mixed.MixedClosingCandidate
    {Projection.Hidden}
    {Fibre.ToyExperiment}
    Projection.coarseFibre
    Projection.middleDecision →
  QueryPromotion.ProducerKind → Set
CalibrationCanPay candidate QueryPromotion.proveTransport = ⊤
CalibrationCanPay candidate _ = ⊥

calibrationProblem :
  ProducerActionProblem
    {Projection.Hidden}
    {Fibre.ToyExperiment}
    Projection.coarseFibre
    Projection.middleDecision
calibrationProblem =
  producer-action-problem
    History.earlierMissingTransport
    Historical.earlierTransportReportedLineage
    DeclaredCalibration
    CalibrationCanPay
    "synthetic policy explicitly licenses calibrated observation routes as transport-payment candidates"
    "middleDecision consumer"

middleEligible : ProducerEligibleCandidate calibrationProblem
middleEligible =
  producer-eligible-candidate
    middleMixedClosing
    tt
    tt
    "explicit calibration policy says middle route can pay proveTransport"

fineEligible : ProducerEligibleCandidate calibrationProblem
fineEligible =
  producer-eligible-candidate
    fineMixedClosing
    tt
    tt
    "explicit calibration policy says fine route can pay proveTransport"

middleEligibleCostsNoMoreThanFine :
  Mixed.cost (candidate middleEligible) ≤ Mixed.cost (candidate fineEligible)
middleEligibleCostsNoMoreThanFine = s≤s z≤n

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data ProducerKindAutomaticallyDeterminesAction : Set where
data ClosingConsumerAutomaticallyPaysProducer : Set where
data CheapestProducerActionCreatesAuthority : Set where

aProducerKindDoesNotAutomaticallyDetermineAction :
  ProducerKindAutomaticallyDeterminesAction → ⊥
aProducerKindDoesNotAutomaticallyDetermineAction ()

consumerClosureDoesNotAutomaticallyPayProducer :
  ClosingConsumerAutomaticallyPaysProducer → ⊥
consumerClosureDoesNotAutomaticallyPayProducer ()

cheapestProducerActionDoesNotCreateAuthority :
  CheapestProducerActionCreatesAuthority → ⊥
cheapestProducerActionDoesNotCreateAuthority ()

record HistoricalProducerActionBoundary : Set where
  constructor historical-producer-action-boundary
  field
    historicalFailureDeterminesRequiredProducer : Bool
    candidateNeedsSeparateProducerPaymentReceipt : Bool
    candidateAlsoMustCloseConsumer : Bool
    producerKindAloneDeterminesAction : Bool
    cheapestChoiceCreatesActionAuthority : Bool

canonicalHistoricalProducerActionBoundary : HistoricalProducerActionBoundary
canonicalHistoricalProducerActionBoundary =
  historical-producer-action-boundary true true true false false

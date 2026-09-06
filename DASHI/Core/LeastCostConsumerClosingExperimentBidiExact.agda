module DASHI.Core.LeastCostConsumerClosingExperimentBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.FibreRefinementExperimentSelectionBidiExact as Fibre
import DASHI.Core.CostedFibreEliminationChoiceBidiExact as Costed
import DASHI.Core.ActionabilityCostedExperimentChoiceExact as Cost
import DASHI.Core.MinimalObservationLevelPerConsumerBidiExact as Minimal
import DASHI.Core.ProjectionHierarchyCompatibleFibreBidiExact as Projection

------------------------------------------------------------------------
-- LEAST-COST CONSUMER-CLOSING EXPERIMENT
------------------------------------------------------------------------

record ConsumerClosingCandidate {Hidden Experiment Decision : Set}
    (prior : Bidi.ResidualFibre Hidden)
    (consumer : Hidden → Decision) : Set₁ where
  constructor consumer-closing-candidate
  field
    costed : Costed.CostedRefinementCandidate {Hidden} {Experiment} prior
    closesConsumer :
      Bidi.PointIdentifies
        (Fibre.posterior (Costed.refinement costed))
        consumer
    closureReference : String

open ConsumerClosingCandidate public

record LeastCostConsumerClosingChoice {Hidden Experiment Decision : Set}
    (prior : Bidi.ResidualFibre Hidden)
    (consumer : Hidden → Decision)
    (Declared : ConsumerClosingCandidate {Hidden} {Experiment} prior consumer → Set)
    : Set₁ where
  constructor least-cost-consumer-closing-choice
  field
    selected : ConsumerClosingCandidate {Hidden} {Experiment} prior consumer
    selectedDeclared : Declared selected
    selectedStrict :
      Fibre.grade (Costed.refinement (costed selected)) ≡ Fibre.strictRefinement
    minimalCost :
      (alternative : ConsumerClosingCandidate {Hidden} {Experiment} prior consumer) →
      Declared alternative →
      Fibre.grade (Costed.refinement (costed alternative)) ≡ Fibre.strictRefinement →
      Cost.cost (Costed.move (costed selected)) ≤
      Cost.cost (Costed.move (costed alternative))
    comparisonReference : String

open LeastCostConsumerClosingChoice public

selectedChoiceClosesConsumer :
  ∀ {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision}
    {Declared : ConsumerClosingCandidate {Hidden} {Experiment} prior consumer → Set} →
  (choice : LeastCostConsumerClosingChoice prior consumer Declared) →
  Bidi.PointIdentifies
    (Fibre.posterior (Costed.refinement (costed (selected choice))))
    consumer
selectedChoiceClosesConsumer choice = closesConsumer (selected choice)

selectedChoiceEliminatesPriorCandidate :
  ∀ {Hidden Experiment Decision : Set}
    {prior : Bidi.ResidualFibre Hidden}
    {consumer : Hidden → Decision}
    {Declared : ConsumerClosingCandidate {Hidden} {Experiment} prior consumer → Set} →
  (choice : LeastCostConsumerClosingChoice prior consumer Declared) →
  Σ Hidden
    (λ hidden →
      prior hidden ×
      ¬ (Fibre.posterior (Costed.refinement (costed (selected choice))) hidden))
selectedChoiceEliminatesPriorCandidate choice =
  Fibre.strictReceiptEliminatesPriorCandidate
    (Costed.refinement (costed (selected choice)))
    (selectedStrict choice)

------------------------------------------------------------------------
-- Exact finite calibration: both a middle observation and a finer observation
-- close the same consumer from the coarse prior, but the middle move is cheaper.
------------------------------------------------------------------------

coarseToFineReceipt : Fibre.ExperimentRefinementReceipt Projection.coarseFibre
coarseToFineReceipt =
  Fibre.experiment-refinement-receipt
    Fibre.addFineObservation
    Projection.fineFibre
    (Bidi.fibreRefinesTrans Projection.fineRefinesMiddle Projection.middleRefinesCoarse)
    Fibre.strictRefinement
    (λ _ → Projection.h1 , (tt , (λ x → x)))
    "synthetic fine observation from coarse prior"
    "exact finite coarse-to-fine calibration"

middleMove : Cost.InformationMove
middleMove = Cost.informationMove
  Cost.takeMeasurement 1
  "middle-level observation"
  "unit synthetic resource cost"
  "declared calibrated observation"

fineMove : Cost.InformationMove
fineMove = Cost.informationMove
  Cost.takeMeasurement 2
  "fine-level observation"
  "two-unit synthetic resource cost"
  "declared calibrated observation"

middleCostedCandidate :
  Costed.CostedRefinementCandidate Projection.coarseFibre
middleCostedCandidate =
  Costed.costed-refinement-candidate
    Fibre.coarseToMiddleReceipt
    middleMove
    "middle observation realizes coarse-to-middle refinement"
    "synthetic admitted middle observation"

fineCostedCandidate :
  Costed.CostedRefinementCandidate Projection.coarseFibre
fineCostedCandidate =
  Costed.costed-refinement-candidate
    coarseToFineReceipt
    fineMove
    "fine observation realizes coarse-to-fine refinement"
    "synthetic admitted fine observation"

middleClosingCandidate :
  ConsumerClosingCandidate Projection.coarseFibre Projection.middleDecision
middleClosingCandidate =
  consumer-closing-candidate
    middleCostedCandidate
    Projection.middleConsumerClosed
    "middle posterior already closes the decision consumer"

fineClosingCandidate :
  ConsumerClosingCandidate Projection.coarseFibre Projection.middleDecision
fineClosingCandidate =
  consumer-closing-candidate
    fineCostedCandidate
    Minimal.middleDecisionClosedAtFine
    "fine posterior also closes the same decision consumer"

middleCostsNoMoreThanFine :
  Cost.cost (Costed.move (costed middleClosingCandidate)) ≤
  Cost.cost (Costed.move (costed fineClosingCandidate))
middleCostsNoMoreThanFine = s≤s z≤n

middleAlreadyClosesCalibrationConsumer :
  Minimal.ConsumerClosedAtLevel Projection.middleDecision Minimal.middleLevel
middleAlreadyClosesCalibrationConsumer = Minimal.middleDecisionClosedAtMiddle

middleStillNotPointSingleton = Minimal.middleClosureStillNotPointSingleton

data ConsumerClosureRequiresFinestObservation : Set where
data LeastCostClosingChoiceMustMaximiseIdentification : Set where
data ClosureReceiptCreatesActionAuthority : Set where

consumerClosureDoesNotRequireFinestObservation :
  ConsumerClosureRequiresFinestObservation → ⊥
consumerClosureDoesNotRequireFinestObservation ()

leastCostClosingNeedNotMaximiseIdentification :
  LeastCostClosingChoiceMustMaximiseIdentification → ⊥
leastCostClosingNeedNotMaximiseIdentification ()

closureReceiptDoesNotCreateActionAuthority :
  ClosureReceiptCreatesActionAuthority → ⊥
closureReceiptDoesNotCreateActionAuthority ()

record LeastCostConsumerClosingBoundary : Set where
  constructor least-cost-consumer-closing-boundary
  field
    objectiveIsConsumerClosureNotPointIdentification : Bool
    selectedExperimentMustCloseConsumer : Bool
    selectedStrictExperimentStillEliminatesCandidate : Bool
    cheaperMiddleMayCloseBeforeFineIdentification : Bool
    finestObservationAlwaysRequired : Bool
    closureCreatesAuthority : Bool

canonicalLeastCostConsumerClosingBoundary : LeastCostConsumerClosingBoundary
canonicalLeastCostConsumerClosingBoundary =
  least-cost-consumer-closing-boundary true true true true false false

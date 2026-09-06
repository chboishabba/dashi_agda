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
--
-- Cross-weld of consumer-relative observation thresholds and costed fibre
-- elimination.  The objective is not maximal identification.  It is the least
-- declared cost among experiments whose posterior fibre is already sufficient
-- to close the selected consumer.
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
-- Exact calibration: the middle observation level already closes the existing
-- decision consumer while remaining non-singleton.  Therefore a policy whose
-- target is this consumer has no logical need to demand the fine singleton
-- fibre merely because it is more identifying.
------------------------------------------------------------------------

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
    finestObservationAlwaysRequired : Bool
    closureCreatesAuthority : Bool

canonicalLeastCostConsumerClosingBoundary : LeastCostConsumerClosingBoundary
canonicalLeastCostConsumerClosingBoundary =
  least-cost-consumer-closing-boundary true true true false false

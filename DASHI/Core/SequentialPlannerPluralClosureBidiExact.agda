module DASHI.Core.SequentialPlannerPluralClosureBidiExact where

open import DASHI.Core.Prelude

import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.ReformulationClosureWithoutFibreRefinementBidiExact as Reform
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Method

------------------------------------------------------------------------
-- SEQUENTIAL EXPERIMENT PLANNING <-> PLURAL CLOSURE
--
-- The existing planner closes when the selected consumer is constant on the
-- current compatible set.  The plural methodology adds a second terminal route:
-- reformulate the consumer so that it becomes constant on the same fibre.
------------------------------------------------------------------------

reformulatedTerminalPlan :
  Planner.SequentialConsumerPlan
    (Reform.answer Reform.reformulatedQuestion)
    Reform.liveFibre
reformulatedTerminalPlan =
  Planner.closeConsumer Reform.reformulatedQuestionClosed

oldQuestionCannotCloseOnSameFibre :
  (∀ left right →
    Reform.liveFibre left →
    Reform.liveFibre right →
    Reform.answer Reform.oldQuestion left ≡ Reform.answer Reform.oldQuestion right) → ⊥
oldQuestionCannotCloseOnSameFibre = Reform.oldQuestionNotClosed

reformulatedPlanLeavesCompatibleFibreUnchanged :
  Reform.fibreAfter ≡ Reform.fibreBefore
reformulatedPlanLeavesCompatibleFibreUnchanged =
  Reform.reformulationLeavesFibreUntouched

reformulationIsRecognisedProgressRoute : Method.EpistemicProgressRoute
reformulationIsRecognisedProgressRoute = Method.reformulateQuestion

data SequentialClosureAlwaysRequiresMeasurement : Set where
data TerminalPlanImpliesFullWorldIdentity : Set where

sequentialClosureNeedNotRequireMeasurement :
  SequentialClosureAlwaysRequiresMeasurement → ⊥
sequentialClosureNeedNotRequireMeasurement ()

terminalPlanDoesNotImplyFullWorldIdentity : TerminalPlanImpliesFullWorldIdentity → ⊥
terminalPlanDoesNotImplyFullWorldIdentity ()

record SequentialPluralClosureBoundary : Set where
  constructor sequential-plural-closure-boundary
  field
    terminalClosureMayFollowMeasurement : Bool
    terminalClosureMayFollowReformulation : Bool
    reformulationMayLeaveFibreUnchanged : Bool
    terminalClosureRequiresFullWorldIdentity : Bool
    reformulationCreatesDeploymentAuthority : Bool

canonicalSequentialPluralClosureBoundary : SequentialPluralClosureBoundary
canonicalSequentialPluralClosureBoundary =
  sequential-plural-closure-boundary true true true false false

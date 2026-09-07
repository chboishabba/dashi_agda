module DASHI.Core.SequentialOutcomeBackpropagationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.SequentialConsumerExperimentPlannerExact as Planner
import DASHI.Core.SequentialPlannerPluralClosureBidiExact as PluralPlanner
import DASHI.Core.ReformulationClosureWithoutFibreRefinementBidiExact as Reform
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Backprop
import DASHI.Core.DependencySensitiveClosureReopeningBidiExact as Closure
import DASHI.Core.PluralEpistemicProgressMethodologyBidiExact as Progress

------------------------------------------------------------------------
-- RESULT-SENSITIVE SEQUENTIAL BACKPROPAGATION
--
-- A sequential plan can terminate at consumer closure, but terminal does not
-- mean irreversible.  Later adverse/indeterminate evidence is diagnosed, routed
-- to a typed upstream coordinate, and propagated only through closures that
-- actually depend on that coordinate.
------------------------------------------------------------------------

data RevisionAction : Set where
  retainClosure : RevisionAction
  reacquireObservation : RevisionAction
  rechartRepresentation : RevisionAction
  inspectPremise : RevisionAction
  inspectRule : RevisionAction
  reviseModel : RevisionAction
  reformulateConsumer : RevisionAction
  acquireIndependentProvenance : RevisionAction
  seekAuthorityReceipt : RevisionAction


revisionFor : Backprop.ReopenCoordinate → RevisionAction
revisionFor Backprop.noReopen = retainClosure
revisionFor Backprop.reopenObservation = reacquireObservation
revisionFor Backprop.reopenFrame = rechartRepresentation
revisionFor Backprop.reopenPremise = inspectPremise
revisionFor Backprop.reopenRule = inspectRule
revisionFor Backprop.reopenModel = reviseModel
revisionFor Backprop.reopenConsumer = reformulateConsumer
revisionFor Backprop.reopenProvenance = acquireIndependentProvenance
revisionFor Backprop.reopenAuthorityBoundary = seekAuthorityReceipt

record SequentialBackpropagationStep : Set where
  constructor sequential-backpropagation-step
  field
    result : Closure.ResultAssessment
    closureSurface : Closure.ClosureDependencySurface
    affected : Closure.AffectsClosure closureSurface result
    action : RevisionAction
    actionCorrect : action ≡ revisionFor (Closure.target result)
    backpropReference : String

open SequentialBackpropagationStep public

------------------------------------------------------------------------
-- Exact steps.
------------------------------------------------------------------------

measurementModelBackprop : SequentialBackpropagationStep
measurementModelBackprop =
  sequential-backpropagation-step
    Closure.adverseModelResult
    Closure.measurementClosureSurface
    Closure.adverseModelReopensMeasurementClosure
    reviseModel refl
    "adverse model conflict backpropagates through a measurement-derived closure"

measurementIndeterminateBackprop : SequentialBackpropagationStep
measurementIndeterminateBackprop =
  sequential-backpropagation-step
    Closure.indeterminateResolutionResult
    Closure.measurementClosureSurface
    Closure.indeterminateResolutionReopensMeasurementClosure
    reacquireObservation refl
    "indeterminate resolution reopens the observation seam"

reformulationConsumerBackprop : SequentialBackpropagationStep
reformulationConsumerBackprop =
  sequential-backpropagation-step
    Closure.adverseConsumerResult
    Closure.reformulationClosureSurface
    Closure.consumerMismatchReopensReformulationClosure
    reformulateConsumer refl
    "consumer mismatch reopens a reformulation-derived terminal closure"

------------------------------------------------------------------------
-- Existing terminal plan remains a legitimate terminal plan; the new layer
-- controls what happens when later evidence touches one of its dependencies.
------------------------------------------------------------------------

reformulatedTerminalPlanStillExists :
  Planner.SequentialConsumerPlan
    (Reform.answer Reform.reformulatedQuestion)
    Reform.liveFibre
reformulatedTerminalPlanStillExists = PluralPlanner.reformulatedTerminalPlan

adverseModelDoesNotByItselfInvalidateReformulationTerminal :
  Closure.AffectsClosure
    Closure.reformulationClosureSurface Closure.adverseModelResult → ⊥
adverseModelDoesNotByItselfInvalidateReformulationTerminal =
  Closure.adverseModelDoesNotReopenReformulationClosure

indeterminateObservationDoesNotByItselfInvalidateReformulationTerminal :
  Closure.AffectsClosure
    Closure.reformulationClosureSurface Closure.indeterminateResolutionResult → ⊥
indeterminateObservationDoesNotByItselfInvalidateReformulationTerminal =
  Closure.indeterminateResolutionDoesNotReopenReformulationClosure

consumerMismatchDoesInvalidateReformulationDependency :
  Closure.AffectsClosure
    Closure.reformulationClosureSurface Closure.adverseConsumerResult
consumerMismatchDoesInvalidateReformulationDependency =
  Closure.consumerMismatchReopensReformulationClosure

------------------------------------------------------------------------
-- Backprop actions connect back to the forward methodology without identifying
-- revision with progress.
------------------------------------------------------------------------

reacquisitionCanFeedAddedCoordinateProgress : Progress.EpistemicProgressRoute
reacquisitionCanFeedAddedCoordinateProgress = Progress.addNewCoordinate

consumerRevisionCanFeedReformulationProgress : Progress.EpistemicProgressRoute
consumerRevisionCanFeedReformulationProgress = Progress.reformulateQuestion

provenanceRevisionCanFeedProvenanceProgress : Progress.EpistemicProgressRoute
provenanceRevisionCanFeedProvenanceProgress = Progress.establishIndependentProvenance

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data TerminalMeansIrreversible : Set where
data AdverseMeansChooseOppositeConclusion : Set where
data IndeterminateMeansDiscardWholePlan : Set where
data RevisionActionIsAlreadyProgressReceipt : Set where
data UnaffectedDependencyMustReopen : Set where

terminalDoesNotMeanIrreversible : TerminalMeansIrreversible → ⊥
terminalDoesNotMeanIrreversible ()

adverseDoesNotChooseOppositeConclusion : AdverseMeansChooseOppositeConclusion → ⊥
adverseDoesNotChooseOppositeConclusion ()

indeterminateDoesNotDiscardWholePlan : IndeterminateMeansDiscardWholePlan → ⊥
indeterminateDoesNotDiscardWholePlan ()

revisionIsNotAutomaticallyProgress : RevisionActionIsAlreadyProgressReceipt → ⊥
revisionIsNotAutomaticallyProgress ()

unaffectedDependencyDoesNotHaveToReopen : UnaffectedDependencyMustReopen → ⊥
unaffectedDependencyDoesNotHaveToReopen ()

record SequentialBackpropagationBoundary : Set where
  constructor sequential-backpropagation-boundary
  field
    terminalClosureMayReopen : Bool
    reopeningIsDependencySensitive : Bool
    adverseResultChoosesOppositeConclusion : Bool
    indeterminateResultErasesPlanHistory : Bool
    revisionMayFeedForwardProgress : Bool
    authorityReopeningCreatesAuthorityReceipt : Bool

canonicalSequentialBackpropagationBoundary : SequentialBackpropagationBoundary
canonicalSequentialBackpropagationBoundary =
  sequential-backpropagation-boundary true true false false true false

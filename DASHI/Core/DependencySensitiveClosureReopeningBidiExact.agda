module DASHI.Core.DependencySensitiveClosureReopeningBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Backprop
import DASHI.Core.ReformulationClosureWithoutFibreRefinementBidiExact as Reform

------------------------------------------------------------------------
-- DEPENDENCY-SENSITIVE CLOSURE REOPENING
--
-- A terminal consumer closure is not an irreversible sink.  Later evidence may
-- reopen it, but only through a dependency on which that closure actually
-- relied.  Outcome polarity alone is insufficient: diagnosis selects a target,
-- and the closure's dependency surface decides whether that target propagates.
------------------------------------------------------------------------

record ClosureDependencySurface : Set₁ where
  constructor closure-dependency-surface
  field
    dependsOn : Backprop.ReopenCoordinate → Set
    closureReference : String
    dependencyReference : String

open ClosureDependencySurface public

record ResultAssessment : Set where
  constructor result-assessment
  field
    outcome : Backprop.ExperimentalOutcome
    diagnosis : Backprop.OutcomeDiagnosis
    target : Backprop.ReopenCoordinate
    targetCorrect : target ≡ Backprop.reopenFor outcome diagnosis
    resultReference : String

open ResultAssessment public

AffectsClosure : ClosureDependencySurface → ResultAssessment → Set
AffectsClosure surface result = dependsOn surface (target result)

record ClosureReopeningReceipt
    (surface : ClosureDependencySurface)
    (result : ResultAssessment) : Set where
  constructor closure-reopening-receipt
  field
    affected : AffectsClosure surface result
    reopenReference : String

open ClosureReopeningReceipt public

------------------------------------------------------------------------
-- Two exact closure surfaces.
--
-- Measurement-derived closure depends on observation/frame/model/premise.
-- Reformulation-derived closure depends on the declared consumer but not on a
-- measurement/model result merely because that result is adverse.
------------------------------------------------------------------------

measurementDependency : Backprop.ReopenCoordinate → Set
measurementDependency Backprop.reopenObservation = ⊤
measurementDependency Backprop.reopenFrame = ⊤
measurementDependency Backprop.reopenPremise = ⊤
measurementDependency Backprop.reopenRule = ⊤
measurementDependency Backprop.reopenModel = ⊤
measurementDependency Backprop.reopenConsumer = ⊥
measurementDependency Backprop.reopenProvenance = ⊤
measurementDependency Backprop.reopenAuthorityBoundary = ⊥
measurementDependency Backprop.noReopen = ⊥

reformulationDependency : Backprop.ReopenCoordinate → Set
reformulationDependency Backprop.reopenObservation = ⊥
reformulationDependency Backprop.reopenFrame = ⊥
reformulationDependency Backprop.reopenPremise = ⊥
reformulationDependency Backprop.reopenRule = ⊥
reformulationDependency Backprop.reopenModel = ⊥
reformulationDependency Backprop.reopenConsumer = ⊤
reformulationDependency Backprop.reopenProvenance = ⊥
reformulationDependency Backprop.reopenAuthorityBoundary = ⊥
reformulationDependency Backprop.noReopen = ⊥

measurementClosureSurface : ClosureDependencySurface
measurementClosureSurface =
  closure-dependency-surface measurementDependency
    "consumer closure produced by a measurement/refinement route"
    "observation, frame, premise, rule, model and provenance are live dependencies"

reformulationClosureSurface : ClosureDependencySurface
reformulationClosureSurface =
  closure-dependency-surface reformulationDependency
    "consumer closure produced by reformulating the declared question"
    "closure depends on the reformulated consumer declaration, not on measurement shrinkage"

------------------------------------------------------------------------
-- Exact result assessments.
------------------------------------------------------------------------

adverseModelResult : ResultAssessment
adverseModelResult =
  result-assessment Backprop.adverse Backprop.modelConflict Backprop.reopenModel refl
    "adverse result diagnosed as conflict with the model"

adverseConsumerResult : ResultAssessment
adverseConsumerResult =
  result-assessment Backprop.adverse Backprop.consumerMismatch Backprop.reopenConsumer refl
    "adverse result diagnosed as mismatch between result and declared consumer"

indeterminateResolutionResult : ResultAssessment
indeterminateResolutionResult =
  result-assessment Backprop.indeterminate Backprop.insufficientResolution
    Backprop.reopenObservation refl
    "indeterminate result diagnosed as insufficient observational resolution"

adverseModelReopensMeasurementClosure :
  AffectsClosure measurementClosureSurface adverseModelResult
adverseModelReopensMeasurementClosure = tt

adverseModelDoesNotReopenReformulationClosure :
  AffectsClosure reformulationClosureSurface adverseModelResult → ⊥
adverseModelDoesNotReopenReformulationClosure ()

consumerMismatchReopensReformulationClosure :
  AffectsClosure reformulationClosureSurface adverseConsumerResult
consumerMismatchReopensReformulationClosure = tt

indeterminateResolutionReopensMeasurementClosure :
  AffectsClosure measurementClosureSurface indeterminateResolutionResult
indeterminateResolutionReopensMeasurementClosure = tt

indeterminateResolutionDoesNotReopenReformulationClosure :
  AffectsClosure reformulationClosureSurface indeterminateResolutionResult → ⊥
indeterminateResolutionDoesNotReopenReformulationClosure ()

------------------------------------------------------------------------
-- The reformulated consumer itself remains closed on the same fibre unless its
-- own dependency is reopened.  A model-conflict result cannot syntactically
-- manufacture failure of that theorem.
------------------------------------------------------------------------

reformulatedQuestionStillClosedOnSameFibre :
  Reform.QuestionClosed Reform.reformulatedQuestion
reformulatedQuestionStillClosedOnSameFibre = Reform.reformulatedQuestionClosed

reformulatedFibreStillUnchanged : Reform.fibreAfter ≡ Reform.fibreBefore
reformulatedFibreStillUnchanged = Reform.reformulationLeavesFibreUntouched

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data AnyNegativeResultReopensEveryClosure : Set where
data AnyIndeterminateResultReopensEveryClosure : Set where
data ClosedOnceMeansNeverReopen : Set where
data ResultPolarityAloneDeterminesDependency : Set where

negativeResultDoesNotReopenEveryClosure :
  AnyNegativeResultReopensEveryClosure → ⊥
negativeResultDoesNotReopenEveryClosure ()

indeterminateResultDoesNotReopenEveryClosure :
  AnyIndeterminateResultReopensEveryClosure → ⊥
indeterminateResultDoesNotReopenEveryClosure ()

closureIsNotIrreversibleSink : ClosedOnceMeansNeverReopen → ⊥
closureIsNotIrreversibleSink ()

polarityDoesNotDetermineDependency : ResultPolarityAloneDeterminesDependency → ⊥
polarityDoesNotDetermineDependency ()

record DependencySensitiveClosureBoundary : Set where
  constructor dependency-sensitive-closure-boundary
  field
    terminalClosureMayLaterReopen : Bool
    reopeningRequiresAffectedDependency : Bool
    adverseResultReopensEveryClosure : Bool
    indeterminateResultReopensEveryClosure : Bool
    reformulationClosureMaySurviveModelConflict : Bool
    consumerMismatchMayReopenReformulationClosure : Bool

canonicalDependencySensitiveClosureBoundary : DependencySensitiveClosureBoundary
canonicalDependencySensitiveClosureBoundary =
  dependency-sensitive-closure-boundary true true false false true true

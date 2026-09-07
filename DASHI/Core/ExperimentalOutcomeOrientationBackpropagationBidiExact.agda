module DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ArgumentObstructionCore as Argument
import DASHI.Core.TypedProvenanceDependencyGraphExact as Dependency

------------------------------------------------------------------------
-- EXPERIMENTAL OUTCOME ORIENTATION / BACKPROPAGATION
--
-- A result can orient a local comparison without becoming a truth oracle.
-- This mirrors the determinant-as-compass reading: sign/orientation is always
-- relative to a chosen frame.  A negative orientation is therefore not by
-- itself the geometric opposite of the hidden object or the logical negation
-- of the current conclusion.
------------------------------------------------------------------------

data ExperimentalOutcome : Set where
  supportive adverse indeterminate : ExperimentalOutcome

data OrientationReading : Set where
  positiveOrientation negativeOrientation degenerateOrientation : OrientationReading

orientationOf : ExperimentalOutcome → OrientationReading
orientationOf supportive = positiveOrientation
orientationOf adverse = negativeOrientation
orientationOf indeterminate = degenerateOrientation

data ReopenCoordinate : Set where
  noReopen
  reopenObservation
  reopenFrame
  reopenPremise
  reopenRule
  reopenModel
  reopenConsumer
  reopenProvenance
  reopenAuthorityBoundary
  : ReopenCoordinate

data OutcomeDiagnosis : Set where
  observationConflict
  frameConflict
  premiseConflict
  ruleConflict
  modelConflict
  consumerMismatch
  provenanceConflict
  authorityMismatch
  insufficientResolution
  : OutcomeDiagnosis

reopenFor : ExperimentalOutcome → OutcomeDiagnosis → ReopenCoordinate
reopenFor supportive observationConflict = noReopen
reopenFor supportive frameConflict = reopenFrame
reopenFor supportive premiseConflict = reopenPremise
reopenFor supportive ruleConflict = reopenRule
reopenFor supportive modelConflict = reopenModel
reopenFor supportive consumerMismatch = reopenConsumer
reopenFor supportive provenanceConflict = reopenProvenance
reopenFor supportive authorityMismatch = reopenAuthorityBoundary
reopenFor supportive insufficientResolution = reopenObservation
reopenFor adverse observationConflict = reopenObservation
reopenFor adverse frameConflict = reopenFrame
reopenFor adverse premiseConflict = reopenPremise
reopenFor adverse ruleConflict = reopenRule
reopenFor adverse modelConflict = reopenModel
reopenFor adverse consumerMismatch = reopenConsumer
reopenFor adverse provenanceConflict = reopenProvenance
reopenFor adverse authorityMismatch = reopenAuthorityBoundary
reopenFor adverse insufficientResolution = reopenObservation
reopenFor indeterminate observationConflict = reopenObservation
reopenFor indeterminate frameConflict = reopenFrame
reopenFor indeterminate premiseConflict = reopenPremise
reopenFor indeterminate ruleConflict = reopenRule
reopenFor indeterminate modelConflict = reopenModel
reopenFor indeterminate consumerMismatch = reopenConsumer
reopenFor indeterminate provenanceConflict = reopenProvenance
reopenFor indeterminate authorityMismatch = reopenAuthorityBoundary
reopenFor indeterminate insufficientResolution = reopenObservation

------------------------------------------------------------------------
-- Same observed polarity can backpropagate to different seams.
------------------------------------------------------------------------

adverseModelReopensModel :
  reopenFor adverse modelConflict ≡ reopenModel
adverseModelReopensModel = refl

adversePremiseReopensPremise :
  reopenFor adverse premiseConflict ≡ reopenPremise
adversePremiseReopensPremise = refl

adverseFrameReopensFrame :
  reopenFor adverse frameConflict ≡ reopenFrame
adverseFrameReopensFrame = refl

indeterminateResolutionReopensObservation :
  reopenFor indeterminate insufficientResolution ≡ reopenObservation
indeterminateResolutionReopensObservation = refl

indeterminateFrameConflictReopensFrame :
  reopenFor indeterminate frameConflict ≡ reopenFrame
indeterminateFrameConflictReopensFrame = refl

modelAndPremiseTargetsDiffer : reopenModel ≡ reopenPremise → ⊥
modelAndPremiseTargetsDiffer ()

sameAdverseResultNeedNotHaveSameBackpropTarget :
  reopenFor adverse modelConflict ≡ reopenFor adverse premiseConflict → ⊥
sameAdverseResultNeedNotHaveSameBackpropTarget = modelAndPremiseTargetsDiffer

------------------------------------------------------------------------
-- Dependency graph bridge: reopening is typed by what the edge contributed.
------------------------------------------------------------------------

reopenForRole : Dependency.DependencyRole → ReopenCoordinate
reopenForRole Dependency.definitionRole = reopenModel
reopenForRole Dependency.theoremRole = reopenRule
reopenForRole Dependency.evidenceRole = reopenObservation
reopenForRole Dependency.vocabularyRole = reopenFrame
reopenForRole Dependency.projectionRole = reopenFrame
reopenForRole Dependency.reconstructionRole = reopenModel
reopenForRole Dependency.residualRole = reopenObservation
reopenForRole Dependency.rechartRole = reopenFrame
reopenForRole Dependency.counterexampleRole = reopenPremise
reopenForRole Dependency.alignmentRole = reopenFrame
reopenForRole Dependency.acquisitionRole = reopenObservation
reopenForRole Dependency.authorityBoundaryRole = reopenAuthorityBoundary
reopenForRole Dependency.validationRole = reopenObservation
reopenForRole Dependency.historicalMotivationRole = reopenProvenance

record BackpropagationReceipt : Set where
  constructor backpropagation-receipt
  field
    outcome : ExperimentalOutcome
    diagnosis : OutcomeDiagnosis
    target : ReopenCoordinate
    targetCorrect : target ≡ reopenFor outcome diagnosis
    implicatedDependencyRole : Dependency.DependencyRole
    roleTarget : ReopenCoordinate
    roleTargetCorrect : roleTarget ≡ reopenForRole implicatedDependencyRole
    resultReference : String
    diagnosisReference : String

open BackpropagationReceipt public

------------------------------------------------------------------------
-- Negative orientation / obstruction is not conclusion negation.
------------------------------------------------------------------------

data NegativeOrientationRefutesConclusion : Set where
data IndeterminateMeansOppositeConclusion : Set where
data AdverseResultDeterminesOneUniversalReopenTarget : Set where

negativeOrientationDoesNotRefuteConclusion :
  NegativeOrientationRefutesConclusion → ⊥
negativeOrientationDoesNotRefuteConclusion ()

indeterminateDoesNotMeanOppositeConclusion :
  IndeterminateMeansOppositeConclusion → ⊥
indeterminateDoesNotMeanOppositeConclusion ()

adverseResultDoesNotDetermineUniversalTarget :
  AdverseResultDeterminesOneUniversalReopenTarget → ⊥
adverseResultDoesNotDetermineUniversalTarget ()

obstructionMayLeaveTargetTrue :
  {core : Argument.ArgumentCore} →
  Argument.Obstruction core → Bool
obstructionMayLeaveTargetTrue = Argument.fallacyDoesNotRefuteConclusion

record ExperimentalOutcomeBackpropagationBoundary : Set where
  constructor experimental-outcome-backpropagation-boundary
  field
    determinantLikeSignIsOrientationNotVerdict : Bool
    adverseResultMayReopenDifferentDependencies : Bool
    indeterminateResultMayReopenRepresentation : Bool
    obstructionAutomaticallyRefutesTarget : Bool
    negativeOrientationMeansGeometricOpposite : Bool
    outcomeAloneDeterminesBackpropTarget : Bool

canonicalExperimentalOutcomeBackpropagationBoundary :
  ExperimentalOutcomeBackpropagationBoundary
canonicalExperimentalOutcomeBackpropagationBoundary =
  experimental-outcome-backpropagation-boundary
    true true true false false false

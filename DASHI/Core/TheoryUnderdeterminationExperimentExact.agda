module DASHI.Core.TheoryUnderdeterminationExperimentExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.WorldRepresentationSeparationExact as World
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Core.MechanismModelDiscriminationExact as Discrimination
import DASHI.Core.EpistemicSuspensionExact as Suspension
import DASHI.Core.MeasurementBoundaryNonfactorabilityExact as Measurement
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust

------------------------------------------------------------------------
-- THEORY UNDERDETERMINATION / DISCRIMINATING EXPERIMENT
--
-- Two theories may agree on the currently observed/query-relevant fibre while
-- differing elsewhere. Agreement on that fibre is observational equivalence,
-- not identity of theories and not identity with the world.
------------------------------------------------------------------------

data TheoryCandidate : Set where
  theoryA : TheoryCandidate
  theoryB : TheoryCandidate

data TestWorld : Set where
  sharedRegime : TestWorld
  discriminatingRegime : TestWorld

data TestObservation : Set where
  samePrediction : TestObservation
  predictionA : TestObservation
  predictionB : TestObservation

predict : TheoryCandidate → TestWorld → TestObservation
predict theoryA sharedRegime = samePrediction
predict theoryB sharedRegime = samePrediction
predict theoryA discriminatingRegime = predictionA
predict theoryB discriminatingRegime = predictionB

sharedRegimeAgreement :
  predict theoryA sharedRegime ≡ predict theoryB sharedRegime
sharedRegimeAgreement = refl

discriminatingRegimeSeparates :
  predict theoryA discriminatingRegime ≡
  predict theoryB discriminatingRegime → ⊥
discriminatingRegimeSeparates ()

data TheoryIdentityFromSharedPredictionPermission : Set where

sharedPredictionDoesNotIdentifyTheories :
  TheoryIdentityFromSharedPredictionPermission → ⊥
sharedPredictionDoesNotIdentifyTheories ()

------------------------------------------------------------------------
-- Evidence fibre: before the discriminating observation both candidates remain
-- live. A stronger measurement can close the prediction envelope for the
-- declared consumer without claiming metaphysical identity with the world.
------------------------------------------------------------------------

data TheoryEvidence : Set where
  coarseEvidence : TheoryEvidence
  discriminatingEvidenceA : TheoryEvidence
  discriminatingEvidenceB : TheoryEvidence

CompatibleTheory : Envelope.Compatible TheoryEvidence TheoryCandidate
CompatibleTheory coarseEvidence theoryA = ⊤
CompatibleTheory coarseEvidence theoryB = ⊤
CompatibleTheory discriminatingEvidenceA theoryA = ⊤
CompatibleTheory discriminatingEvidenceA theoryB = ⊥
CompatibleTheory discriminatingEvidenceB theoryA = ⊥
CompatibleTheory discriminatingEvidenceB theoryB = ⊤

theoryConsumer : TheoryCandidate → TestObservation
theoryConsumer theoryA = predictionA
theoryConsumer theoryB = predictionB

coarseEvidenceNotPointIdentifiable :
  Envelope.PointIdentifiable CompatibleTheory theoryConsumer coarseEvidence → ⊥
coarseEvidenceNotPointIdentifiable identifiable =
  discriminatingRegimeSeparates
    (identifiable theoryA theoryB tt tt)

discriminatingEvidenceAIsPointIdentifiable :
  Envelope.PointIdentifiable
    CompatibleTheory theoryConsumer discriminatingEvidenceA
discriminatingEvidenceAIsPointIdentifiable theoryA theoryA left right = refl
discriminatingEvidenceAIsPointIdentifiable theoryA theoryB left ()
discriminatingEvidenceAIsPointIdentifiable theoryB theoryA () right
discriminatingEvidenceAIsPointIdentifiable theoryB theoryB () right

------------------------------------------------------------------------
-- Suspension is the appropriate disposition while multiple observationally
-- compatible candidates remain live; it is not a third truth value.
------------------------------------------------------------------------

unresolvedTheoryDisposition : Suspension.EpistemicDisposition
unresolvedTheoryDisposition = Suspension.suspendAndRefine

------------------------------------------------------------------------
-- Existing discrimination and robust-action machinery remain separate:
-- failure to discriminate does not imply "no action", and a discriminating
-- experiment does not manufacture world-completeness or authority.
------------------------------------------------------------------------

discriminationBoundary : Discrimination.ModelDiscriminationBoundary
discriminationBoundary = Discrimination.canonicalModelDiscriminationBoundary

robustBoundary : Robust.RobustInterventionBoundary
robustBoundary = Robust.canonicalRobustInterventionBoundary

measurementBoundary : Measurement.MeasurementBoundaryPrinciple
measurementBoundary = Measurement.canonicalMeasurementBoundaryPrinciple

worldBoundary : World.WorldRepresentationBoundary
worldBoundary = World.canonicalWorldRepresentationBoundary

record TheoryUnderdeterminationBoundary : Set where
  constructor theory-underdetermination-boundary
  field
    samePredictionImpliesSameTheory : Bool
    samePredictionImpliesSameTheoryIsFalse :
      samePredictionImpliesSameTheory ≡ false
    samePredictionImpliesSameOntology : Bool
    samePredictionImpliesSameOntologyIsFalse :
      samePredictionImpliesSameOntology ≡ false
    unresolvedCandidatesRequireForcedBinaryChoice : Bool
    unresolvedCandidatesRequireForcedBinaryChoiceIsFalse :
      unresolvedCandidatesRequireForcedBinaryChoice ≡ false
    discriminatingMeasurementCanRefineLiveTheoryFibre : Bool
    discriminatingMeasurementCanRefineLiveTheoryFibreIsTrue :
      discriminatingMeasurementCanRefineLiveTheoryFibre ≡ true
    discriminatingMeasurementProvesWorldCompleteness : Bool
    discriminatingMeasurementProvesWorldCompletenessIsFalse :
      discriminatingMeasurementProvesWorldCompleteness ≡ false
    unresolvedTheoryAlwaysForbidsRobustAction : Bool
    unresolvedTheoryAlwaysForbidsRobustActionIsFalse :
      unresolvedTheoryAlwaysForbidsRobustAction ≡ false

open TheoryUnderdeterminationBoundary public

canonicalTheoryUnderdeterminationBoundary : TheoryUnderdeterminationBoundary
canonicalTheoryUnderdeterminationBoundary =
  theory-underdetermination-boundary
    false refl
    false refl
    false refl
    true refl
    false refl
    false refl

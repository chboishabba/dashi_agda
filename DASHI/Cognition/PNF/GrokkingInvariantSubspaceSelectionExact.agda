module DASHI.Cognition.PNF.GrokkingInvariantSubspaceSelectionExact where

------------------------------------------------------------------------
-- GROKKING AS INVARIANT-REPRESENTATION SELECTION
--
-- SOURCES
-- Alethea Power, Yuri Burda, Harri Edwards, Igor Babuschkin, Vedant Misra,
-- "Grokking: Generalization Beyond Overfitting on Small Algorithmic Datasets",
-- arXiv:2201.02177.  No DOI asserted.
-- Neel Nanda, Lawrence Chan, Tom Lieberum, Jess Smith, Jacob Steinhardt,
-- "Progress measures for grokking via mechanistic interpretability",
-- arXiv:2301.05217.  No DOI asserted.
-- Andrey Gromov, "Grokking modular arithmetic", arXiv:2301.02679.
-- No DOI asserted.
--
-- The theorem below does not claim training dynamics minimize this score.  It
-- proves that among the two existing rules with identical training fit, the
-- structural character rule is exactly selected by zero task-action defect.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.GrokkingEquivarianceDefectGeometryExact as Defect
import DASHI.Cognition.PNF.ModularFourierGrokkingC3Exact as Grok
import DASHI.Physics.Closure.SSPPrimeLane369DepthWheelCantorBridge as Wheel

data RepresentationCandidate : Set where
  memorizer characterRule : RepresentationCandidate

candidateRule :
  RepresentationCandidate → Grok.InputPair → Wheel.DepthWheelPhase
candidateRule memorizer = Grok.memorizerRule
candidateRule characterRule = Grok.algorithmicRule

algorithmicTrainingEquivalent :
  Grok.TrainingEquivalent Grok.algorithmicRule Grok.algorithmicRule
algorithmicTrainingEquivalent =
  Grok.trainingEquivalent (λ pair witness → refl)

candidateFitsTraining :
  (candidate : RepresentationCandidate) →
  Grok.TrainingEquivalent (candidateRule candidate) Grok.algorithmicRule
candidateFitsTraining memorizer = Grok.memorizerAndAlgorithmTrainingEquivalent
candidateFitsTraining characterRule = algorithmicTrainingEquivalent

invarianceDefect : RepresentationCandidate → Nat
invarianceDefect candidate = Defect.equivarianceDefect (candidateRule candidate)

characterDefectIsZero : invarianceDefect characterRule ≡ 0
characterDefectIsZero = Defect.algorithmicEquivarianceDefectIsZero

memorizerDefectIsTwo : invarianceDefect memorizer ≡ 2
memorizerDefectIsTwo = Defect.memorizerEquivarianceDefectIsTwo

characterStrictlyImprovesInvariantGeometry :
  invarianceDefect characterRule < invarianceDefect memorizer
characterStrictlyImprovesInvariantGeometry =
  Defect.characterGeometryStrictlyImprovesTaskActionDefect

characterIsMinimumDefectTrainingFit :
  (candidate : RepresentationCandidate) →
  invarianceDefect characterRule ≤ invarianceDefect candidate
characterIsMinimumDefectTrainingFit memorizer = z≤n
characterIsMinimumDefectTrainingFit characterRule = ≤-refl

zeroDefectSelectsCharacter :
  (candidate : RepresentationCandidate) →
  invarianceDefect candidate ≡ 0 → candidate ≡ characterRule
zeroDefectSelectsCharacter memorizer ()
zeroDefectSelectsCharacter characterRule proof = refl

trainingFitDoesNotSelectInvariantGeometry :
  Grok.TrainingEquivalent (candidateRule memorizer) Grok.algorithmicRule
  × Grok.TrainingEquivalent (candidateRule characterRule) Grok.algorithmicRule
  × invarianceDefect characterRule < invarianceDefect memorizer
trainingFitDoesNotSelectInvariantGeometry =
  candidateFitsTraining memorizer
  , candidateFitsTraining characterRule
  , characterStrictlyImprovesInvariantGeometry

------------------------------------------------------------------------
-- In this finite regression, generalization corresponds to selecting the rule
-- that realizes the cyclic task action exactly, not merely one that interpolates
-- the observed support.  The result is an exact model-selection statement on
-- the two declared candidates, not a universal theory of grokking optimization.
------------------------------------------------------------------------

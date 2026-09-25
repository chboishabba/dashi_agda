module DASHI.Cognition.PNF.TrialecticMemoryLearningHyperfabricExact where

------------------------------------------------------------------------
-- TRIALECTIC SUBJECT / MEMORY / LEARNING HYPERFABRIC
--
-- DASHI CONTRIBUTION
--
-- This owner cross-welds the new relational/trialectic carrier to the
-- repository's existing memory, learning, decision, trauma, logical
-- qualification and zero-residual machinery.  It deliberately keeps the
-- empirical question "does trauma preferentially populate these states?"
-- separate from the representation theorem "these states can be retained
-- without collapse".
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ArgumentResponseNonGeometricOppositeBidiExact as Opposition
import DASHI.Core.RelationalSelfStalkExact as Self
import DASHI.Core.RelationalSelfDescentExact as SelfDescent
import DASHI.Core.RelationalTrialecticSourceAtlasExact as Sources
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Matrix
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Cognition.PNF.TrialecticMentalizingCalibrationExact as Mentalizing
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as ActionNF
import DASHI.Cognition.PNF.DecisionActionFibreMultiplicityExact as ActionFibre
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as TraumaMemory
import DASHI.Reasoning.TraumaAttractorBranchRegulationExact as TraumaBranch
import DASHI.Foundations.Base369CompletedRelationalDigitExact as Completed
import DASHI.Foundations.Base369PhaseCompletionAndNestedEvaluationExact as Phase
import DASHI.Reasoning.TernarySynthesisLogicQualificationExact as Logic

data ThreatSensitivity : Set where
  ordinaryThreatSensitivity : ThreatSensitivity
  elevatedThreatSensitivity : ThreatSensitivity

data MediationAction : Set where
  mediateAction : MediationAction
  withdrawAction : MediationAction

data MediationMotive : Set where
  integrativeUnderstanding : MediationMotive
  threatAppeasement : MediationMotive
  roleObligation : MediationMotive
  autonomousChoice : MediationMotive

record TrialecticSubjectHyperform (View : Set) : Set₁ where
  constructor trialectic-subject-hyperform
  field
    observerMatrix : Matrix.ObserverMatrix3 View
    trialecticState : Face.TrialecticState
    relationalSelf : Self.RelationalSelfFamily View
    descentState : SelfDescent.RelationalDescentState View
    mentalizingState : Mentalizing.MentalizingCalibrationState
    memory : Memory.MemoryFibre
    learningReceipt : Learning.LearningReceipt
    threatSensitivity : ThreatSensitivity
    mediationAction : MediationAction
    mediationMotive : MediationMotive

open TrialecticSubjectHyperform public

------------------------------------------------------------------------
-- Same emitted mediation action, distinct motives.
------------------------------------------------------------------------

data MediationEpisode : Set where
  integratedMediation : MediationEpisode
  appeasingMediation : MediationEpisode
  obligatedMediation : MediationEpisode

observedMediationAction : MediationEpisode → MediationAction
observedMediationAction integratedMediation = mediateAction
observedMediationAction appeasingMediation = mediateAction
observedMediationAction obligatedMediation = mediateAction

mediationMotiveOf : MediationEpisode → MediationMotive
mediationMotiveOf integratedMediation = integrativeUnderstanding
mediationMotiveOf appeasingMediation = threatAppeasement
mediationMotiveOf obligatedMediation = roleObligation

mediationMotiveWitness :
  Descent.ConsumerNonDescentWitness
    observedMediationAction mediationMotiveOf
mediationMotiveWitness =
  Descent.consumerNonDescentWitness
    integratedMediation appeasingMediation refl (λ ())

mediationMotiveDoesNotFactorThroughAction :
  Descent.FactorsThrough observedMediationAction mediationMotiveOf → ⊥
mediationMotiveDoesNotFactorThroughAction =
  Descent.nonDescentWitnessBlocksFactorization mediationMotiveWitness

didMediate : MediationEpisode → Bool
didMediate integratedMediation = true
didMediate appeasingMediation = true
didMediate obligatedMediation = true

didMediateFactorsThroughObservedAction :
  Descent.FactorsThrough observedMediationAction didMediate
didMediateFactorsThroughObservedAction =
  Factorized.factorizedRefinement
    actionSaysMediated
    proof
  where
    actionSaysMediated : MediationAction → Bool
    actionSaysMediated mediateAction = true
    actionSaysMediated withdrawAction = false

    proof :
      (episode : MediationEpisode) →
      didMediate episode
      ≡ actionSaysMediated (observedMediationAction episode)
    proof integratedMediation = refl
    proof appeasingMediation = refl
    proof obligatedMediation = refl


------------------------------------------------------------------------
-- Three relational zero kinds reuse the existing Base369 distinction.
------------------------------------------------------------------------

data RelationalZeroKind : Set where
  noAvailableRelation : RelationalZeroKind
  balancedActiveCancellation : RelationalZeroKind
  stableInvariantNeutral : RelationalZeroKind

data CoarseRelationalZero : Set where
  coarseZero : CoarseRelationalZero

observeRelationalZero : RelationalZeroKind → CoarseRelationalZero
observeRelationalZero _ = coarseZero

recoverZeroKind : RelationalZeroKind → RelationalZeroKind
recoverZeroKind kind = kind

zeroKindWitness :
  Descent.ConsumerNonDescentWitness
    observeRelationalZero recoverZeroKind
zeroKindWitness =
  Descent.consumerNonDescentWitness
    noAvailableRelation balancedActiveCancellation refl (λ ())

zeroKindDoesNotFactorThroughCoarseZero :
  Descent.FactorsThrough observeRelationalZero recoverZeroKind → ⊥
zeroKindDoesNotFactorThroughCoarseZero =
  Descent.nonDescentWitnessBlocksFactorization zeroKindWitness

emptyZeroDonor : Completed.RelationalZeroWitness
emptyZeroDonor = Phase.emptyZeroWitness

balancedCancellationDonor : Completed.RelationalZeroWitness
balancedCancellationDonor = Phase.cancelledOrbitZeroWitness

stableNeutralDonor : Completed.RelationalZeroWitness
stableNeutralDonor = Phase.fixedNeutralZeroWitness

------------------------------------------------------------------------
-- Threat-specific salience and general mentalizing remain independent.
------------------------------------------------------------------------

data GeneralMentalizing : Set where
  lowerGeneralMentalizing : GeneralMentalizing
  higherGeneralMentalizing : GeneralMentalizing

data ThreatMentalizingEpisode : Set where
  highThreatLowerMentalizing : ThreatMentalizingEpisode
  highThreatHigherMentalizing : ThreatMentalizingEpisode

threatObserver : ThreatMentalizingEpisode → ThreatSensitivity
threatObserver _ = elevatedThreatSensitivity

generalMentalizingConsumer :
  ThreatMentalizingEpisode → GeneralMentalizing
generalMentalizingConsumer highThreatLowerMentalizing = lowerGeneralMentalizing
generalMentalizingConsumer highThreatHigherMentalizing = higherGeneralMentalizing

threatMentalizingWitness :
  Descent.ConsumerNonDescentWitness
    threatObserver generalMentalizingConsumer
threatMentalizingWitness =
  Descent.consumerNonDescentWitness
    highThreatLowerMentalizing highThreatHigherMentalizing refl (λ ())

generalMentalizingDoesNotFactorThroughThreatSensitivity :
  Descent.FactorsThrough threatObserver generalMentalizingConsumer → ⊥
generalMentalizingDoesNotFactorThroughThreatSensitivity =
  Descent.nonDescentWitnessBlocksFactorization threatMentalizingWitness

------------------------------------------------------------------------
-- Experience validity, world truth, evidence support and interpretation are
-- distinct typed coordinates.
------------------------------------------------------------------------

data ExperienceValidity : Set where
  experienceInvalid : ExperienceValidity
  experienceValid : ExperienceValidity

data WorldTruth : Set where
  worldFalse : WorldTruth
  worldTrue : WorldTruth

data EvidenceSupport : Set where
  unsupported : EvidenceSupport
  supported : EvidenceSupport

data InterpretiveAdequacy : Set where
  inadequateInterpretation : InterpretiveAdequacy
  adequateInterpretation : InterpretiveAdequacy

data TwoValidExperiencesForceContradictoryWorldTruth : Set where

validExperienceDoesNotForceContradictoryWorldTruth :
  TwoValidExperiencesForceContradictoryWorldTruth → ⊥
validExperienceDoesNotForceContradictoryWorldTruth ()

------------------------------------------------------------------------
-- Empirical/causal non-promotion firewalls.
------------------------------------------------------------------------

data TraumaExposureImpliesEnhancedIntegration : Set where
data AdaptiveCapacityImpliesBeneficialExposure : Set where
data ThreatSensitivityImpliesThreatTruth : Set where
data MediationBehaviourImpliesSecureCapacity : Set where

traumaExposureDoesNotImplyEnhancedIntegration :
  TraumaExposureImpliesEnhancedIntegration → ⊥
traumaExposureDoesNotImplyEnhancedIntegration ()

adaptiveCapacityDoesNotMakeExposureBeneficial :
  AdaptiveCapacityImpliesBeneficialExposure → ⊥
adaptiveCapacityDoesNotMakeExposureBeneficial ()

threatSensitivityDoesNotEstablishThreatTruth :
  ThreatSensitivityImpliesThreatTruth → ⊥
threatSensitivityDoesNotEstablishThreatTruth ()

mediationBehaviourDoesNotEstablishSecureCapacity :
  MediationBehaviourImpliesSecureCapacity → ⊥
mediationBehaviourDoesNotEstablishSecureCapacity ()

------------------------------------------------------------------------
-- Donor theorem surfaces retained explicitly.
------------------------------------------------------------------------

threeDyadsDoNotRecoverFace :
  Descent.FactorsThrough Face.boundaryObserver Face.faceConsumer → ⊥
threeDyadsDoNotRecoverFace =
  Face.triadicFaceCannotFactorThroughThreeEdges

actionDoesNotRecoverFineDecisionState :
  NF.FactorsThrough ActionNF.observedAction ActionNF.fineDecisionState → ⊥
actionDoesNotRecoverFineDecisionState =
  ActionNF.actionCannotRecoverFineDecisionState

alternativeExplanationIsNotAntipode :
  Opposition.AlternativeExplanationIsGeometricAntipode → ⊥
alternativeExplanationIsNotAntipode =
  Opposition.alternativeExplanationIsNotGeometricAntipode

record TrialecticMemoryLearningBoundary : Set where
  constructor trialectic-memory-learning-boundary
  field
    representationTheoremIsTraumaCausalTheorem : Bool
    actionRecoversMotive : Bool
    coarseZeroRecoversZeroKind : Bool
    threatSensitivityRecoversGeneralMentalizing : Bool
    validExperiencesForceContradictoryWorldTruth : Bool
    adaptiveCapacityMakesExposureBeneficial : Bool
    rememberedContentEqualsCurrentActionPolicy : Bool
    tetralemmaReplacesTernaryCarrier : Bool
    citedSourcesCreateClinicalAuthority : Bool

canonicalTrialecticMemoryLearningBoundary :
  TrialecticMemoryLearningBoundary
canonicalTrialecticMemoryLearningBoundary =
  trialectic-memory-learning-boundary
    false false false false false false false false false

module DASHI.Education.EducationSituatedInvestmentTrajectoryExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.BenefitBurdenExternalityDistributionExact as Distribution
import DASHI.Core.ConsentTemporalExternalityExact as Temporal
import DASHI.Core.RepresentationSubjectPositionNonfactorabilityExact as Subject
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.DecisionAutonomyExact as Autonomy
import DASHI.Cognition.PNF.TraumaMemoryHypervoxelBridge as Trauma

------------------------------------------------------------------------
-- SITUATED EDUCATION / INVESTMENT TRAJECTORY
--
-- The primary carrier is not ROI.  Economic return is a downstream observer
-- over a richer education trajectory that keeps learning, memory, autonomy,
-- benefit, burden, externality, voice, authority and temporal incidence
-- available to independent consumers.
--
-- This file adds no empirical claim that a named pedagogy causes trauma,
-- political behaviour or a particular economic return.  Imported psychology,
-- critical-theory and governance owners retain their own authority boundaries.
------------------------------------------------------------------------

data ReturnKind : Set where
  programmeInternalRateOfReturn : ReturnKind
  benefitCostRatio : ReturnKind
  privateEarningsReturn : ReturnKind
  socialFiscalReturn : ReturnKind

data ValuationState : Set where
  measuredZero : ValuationState
  measuredNonzero : ValuationState
  observedUnmonetised : ValuationState
  monetisableUnvalued : ValuationState
  structurallyMissing : ValuationState
  unknown : ValuationState
  notApplicable : ValuationState

data TrajectoryCoordinate : Set where
  pedagogicalOutcome : TrajectoryCoordinate
  capability : TrajectoryCoordinate
  recognition : TrajectoryCoordinate
  reachability : TrajectoryCoordinate
  contestability : TrajectoryCoordinate
  counterfactualContext : TrajectoryCoordinate
  memoryRevision : TrajectoryCoordinate
  evidenceProvenance : TrajectoryCoordinate
  sourceIndependence : TrajectoryCoordinate
  decisionAutonomy : TrajectoryCoordinate
  benefitIncidence : TrajectoryCoordinate
  burdenIncidence : TrajectoryCoordinate
  externalityIncidence : TrajectoryCoordinate
  voiceAuthority : TrajectoryCoordinate
  controlMediation : TrajectoryCoordinate
  practicalExit : TrajectoryCoordinate
  lifecyclePosition : TrajectoryCoordinate
  temporalPosition : TrajectoryCoordinate
  economicReturn : TrajectoryCoordinate

trajectoryCoordinates : List TrajectoryCoordinate
trajectoryCoordinates =
  pedagogicalOutcome
  ∷ capability
  ∷ recognition
  ∷ reachability
  ∷ contestability
  ∷ counterfactualContext
  ∷ memoryRevision
  ∷ evidenceProvenance
  ∷ sourceIndependence
  ∷ decisionAutonomy
  ∷ benefitIncidence
  ∷ burdenIncidence
  ∷ externalityIncidence
  ∷ voiceAuthority
  ∷ controlMediation
  ∷ practicalExit
  ∷ lifecyclePosition
  ∷ temporalPosition
  ∷ economicReturn
  ∷ []

record EconomicReturnObservation : Set where
  constructor economic-return-observation
  field
    returnKind : ReturnKind
    reportedValue : String
    populationReference : String
    interventionReference : String
    comparatorReference : String
    timeHorizonReference : String
    valuationMethodReference : String
    discountingReference : String
    uncertaintyReference : String
    sourceOrModelReceipt : String

open EconomicReturnObservation public

record SituatedEducationTrajectory : Set where
  constructor situated-education-trajectory
  field
    trajectoryInterventionReference : String
    trajectoryPopulationReference : String
    trajectoryContextReference : String

    learningReceipt : Learning.LearningReceipt
    capabilityReference : String
    recognitionReference : String
    reachabilityReference : String
    contestabilityReference : String
    counterfactualReference : String
    evidenceProvenanceReference : String
    sourceIndependenceReference : String
    autonomyAxes : Autonomy.AutonomyAxes

    benefitReference : String
    burdenReference : String
    externalityReference : String
    voiceAuthorityReference : String
    controlMediationReference : String
    exitReference : String
    lifecycleReference : String
    temporalReference : String

    economicObservation : EconomicReturnObservation
    valuationStateReference : ValuationState

open SituatedEducationTrajectory public

------------------------------------------------------------------------
-- Existing memory / learning / autonomy owners remain canonical.
------------------------------------------------------------------------

memoryExtinctionPreservesRememberedEvent :
  (memory : Memory.MemoryFibre) →
  Memory.rememberedEvent (Memory.extinguishActionDominance memory)
  ≡ Memory.rememberedEvent memory
memoryExtinctionPreservesRememberedEvent =
  Memory.extinctionPreservesRememberedEvent

contextGeneralisationRemainsNonAutomatic :
  (receipt : Learning.ContextGeneralisationReceipt) →
  Learning.generalisationIsAutomatic receipt ≡ false
contextGeneralisationRemainsNonAutomatic =
  Learning.generalisationIsAutomaticIsFalse

canonicalAutonomyBoundary : Autonomy.AutonomyBoundary
canonicalAutonomyBoundary = Autonomy.canonicalAutonomyBoundary

canonicalTraumaAuthorityBoundary :
  Trauma.TraumaMemoryHypervoxelAuthorityBoundary
canonicalTraumaAuthorityBoundary =
  Trauma.canonicalTraumaMemoryHypervoxelAuthorityBoundary

canonicalDistributionBoundary : Distribution.BenefitBurdenExternalityBoundary
canonicalDistributionBoundary =
  Distribution.canonicalBenefitBurdenExternalityBoundary

canonicalTemporalExternalityBoundary :
  Temporal.ConsentTemporalExternalityBoundary
canonicalTemporalExternalityBoundary =
  Temporal.canonicalConsentTemporalExternalityBoundary

canonicalSubjectPositionBoundary :
  Subject.RepresentationSubjectPositionBoundary
canonicalSubjectPositionBoundary =
  Subject.canonicalRepresentationSubjectPositionBoundary

------------------------------------------------------------------------
-- Same economic return can hide different autonomy / burden / voice states.
-- Synthetic finite witness only; no named intervention is assigned either
-- state.
------------------------------------------------------------------------

data ReturnWorld : Set where
  sameReturnRevisableLowBurden : ReturnWorld
  sameReturnConstrainedHighBurden : ReturnWorld

data CoarseReturn : Set where
  sameReportedEconomicReturn : CoarseReturn

data RevisionAutonomy : Set where
  revisionOpen : RevisionAutonomy
  revisionConstrained : RevisionAutonomy

data BurdenState : Set where
  lowerBurden : BurdenState
  higherBurden : BurdenState

data VoiceState : Set where
  voicePresent : VoiceState
  voiceMissing : VoiceState

returnObserver : ReturnWorld → CoarseReturn
returnObserver _ = sameReportedEconomicReturn

revisionAutonomy : ReturnWorld → RevisionAutonomy
revisionAutonomy sameReturnRevisableLowBurden = revisionOpen
revisionAutonomy sameReturnConstrainedHighBurden = revisionConstrained

burdenState : ReturnWorld → BurdenState
burdenState sameReturnRevisableLowBurden = lowerBurden
burdenState sameReturnConstrainedHighBurden = higherBurden

voiceState : ReturnWorld → VoiceState
voiceState sameReturnRevisableLowBurden = voicePresent
voiceState sameReturnConstrainedHighBurden = voiceMissing

sameReturnCannotRecoverRevisionAutonomy :
  INF.FactorsThrough returnObserver revisionAutonomy → ⊥
sameReturnCannotRecoverRevisionAutonomy =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameReturnRevisableLowBurden
      sameReturnConstrainedHighBurden
      refl
      (λ ()))

sameReturnCannotRecoverBurden :
  INF.FactorsThrough returnObserver burdenState → ⊥
sameReturnCannotRecoverBurden =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameReturnRevisableLowBurden
      sameReturnConstrainedHighBurden
      refl
      (λ ()))

sameReturnCannotRecoverVoice :
  INF.FactorsThrough returnObserver voiceState → ⊥
sameReturnCannotRecoverVoice =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      sameReturnRevisableLowBurden
      sameReturnConstrainedHighBurden
      refl
      (λ ()))

------------------------------------------------------------------------
-- Missing / unmonetised / unrepresented states are not measured zero.
------------------------------------------------------------------------

observedUnmonetisedIsNotMeasuredZero :
  observedUnmonetised ≡ measuredZero → ⊥
observedUnmonetisedIsNotMeasuredZero ()

structurallyMissingIsNotMeasuredZero :
  structurallyMissing ≡ measuredZero → ⊥
structurallyMissingIsNotMeasuredZero ()

unknownIsNotMeasuredZero :
  unknown ≡ measuredZero → ⊥
unknownIsNotMeasuredZero ()

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data EconomicReturnCreatesLearningTruth : Set where
data EconomicReturnCreatesAutonomy : Set where
data EconomicReturnCreatesTraumaDiagnosis : Set where
data EconomicReturnCreatesVoiceAuthority : Set where
data RememberedEventDeterminesActionProjection : Set where
data LearningReceiptCreatesPopulationTransport : Set where

economicReturnDoesNotCreateLearningTruth :
  EconomicReturnCreatesLearningTruth → ⊥
economicReturnDoesNotCreateLearningTruth ()

economicReturnDoesNotCreateAutonomy :
  EconomicReturnCreatesAutonomy → ⊥
economicReturnDoesNotCreateAutonomy ()

economicReturnDoesNotCreateTraumaDiagnosis :
  EconomicReturnCreatesTraumaDiagnosis → ⊥
economicReturnDoesNotCreateTraumaDiagnosis ()

economicReturnDoesNotCreateVoiceAuthority :
  EconomicReturnCreatesVoiceAuthority → ⊥
economicReturnDoesNotCreateVoiceAuthority ()

rememberedEventDoesNotDetermineActionProjection :
  RememberedEventDeterminesActionProjection → ⊥
rememberedEventDoesNotDetermineActionProjection ()

learningReceiptDoesNotCreatePopulationTransport :
  LearningReceiptCreatesPopulationTransport → ⊥
learningReceiptDoesNotCreatePopulationTransport ()

record SituatedInvestmentTrajectoryBoundary : Set where
  constructor situated-investment-trajectory-boundary
  field
    economicReturnIsDownstreamProjection : Bool
    economicReturnIsDownstreamProjectionIsTrue :
      economicReturnIsDownstreamProjection ≡ true

    sameReturnDeterminesAutonomy : Bool
    sameReturnDeterminesAutonomyIsFalse :
      sameReturnDeterminesAutonomy ≡ false

    sameReturnDeterminesBurden : Bool
    sameReturnDeterminesBurdenIsFalse :
      sameReturnDeterminesBurden ≡ false

    sameReturnDeterminesVoice : Bool
    sameReturnDeterminesVoiceIsFalse :
      sameReturnDeterminesVoice ≡ false

    rememberedEventDeterminesAction : Bool
    rememberedEventDeterminesActionIsFalse :
      rememberedEventDeterminesAction ≡ false

    learningGeneralisesAutomatically : Bool
    learningGeneralisesAutomaticallyIsFalse :
      learningGeneralisesAutomatically ≡ false

    returnCreatesTraumaDiagnosis : Bool
    returnCreatesTraumaDiagnosisIsFalse :
      returnCreatesTraumaDiagnosis ≡ false

    unmonetisedEqualsZero : Bool
    unmonetisedEqualsZeroIsFalse :
      unmonetisedEqualsZero ≡ false

canonicalSituatedInvestmentTrajectoryBoundary :
  SituatedInvestmentTrajectoryBoundary
canonicalSituatedInvestmentTrajectoryBoundary =
  situated-investment-trajectory-boundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

module DASHI.Physics.Closure.BidirectionalBrainObservationQuotient where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.BrainConnectomeFMRIObservationQuotient
  using (DASHIBrainBridge)

------------------------------------------------------------------------
-- Bidirectional brain / body observation quotient.
--
-- This module localizes the archive-backed claim that fMRI, perceptual
-- report, behavior, and whole-body resource readouts are complementary lossy
-- quotients of a latent brain/body process.
--
-- It deliberately does not promote any of these observations to latent state
-- recovery, qualia recovery, cognition closure, or empirical validation.

data ObservationChannel : Set where
  fMRIChannel :
    ObservationChannel

  perceptChannel :
    ObservationChannel

  behaviorChannel :
    ObservationChannel

  bodyResourceChannel :
    ObservationChannel

data WholeBodyResourceKind : Set where
  bloodFlow :
    WholeBodyResourceKind

  oxygen :
    WholeBodyResourceKind

  glucose :
    WholeBodyResourceKind

  thermalLoad :
    WholeBodyResourceKind

  cardiovascularWork :
    WholeBodyResourceKind

data BidirectionalObservationFirstMissing : Set where
  missingLatentStateModelReceipt :
    BidirectionalObservationFirstMissing

  missingFMRIQuotientCalibration :
    BidirectionalObservationFirstMissing

  missingPerceptReportBinding :
    BidirectionalObservationFirstMissing

  missingBehaviorPolicyBinding :
    BidirectionalObservationFirstMissing

  missingBodyResourceInstrumentation :
    BidirectionalObservationFirstMissing

  missingJointInferenceMetric :
    BidirectionalObservationFirstMissing

  missingKernelComplementarityReceipt :
    BidirectionalObservationFirstMissing

  missingEmpiricalComparisonRun :
    BidirectionalObservationFirstMissing

data NonPromotionBoundary : Set where
  fMRINotPercept :
    NonPromotionBoundary

  reportNotGroundTruth :
    NonPromotionBoundary

  noQualiaClosure :
    NonPromotionBoundary

  noCognitionClosure :
    NonPromotionBoundary

  noLatentStateRecovery :
    NonPromotionBoundary

  noBrainOnlyPhysiology :
    NonPromotionBoundary

record LatentBrainBodyCarrier : Setω where
  field
    Time :
      Set

    LatentState :
      Set

    BodyState :
      Set

    NeuralAdmissibility :
      Set

    ResourceSignal :
      Set

    ResourceDemand :
      Set

    ResourceSupply :
      Set

    sigmaAt :
      Time →
      LatentState

    bodyAt :
      Time →
      BodyState

    resourceSignal :
      WholeBodyResourceKind →
      BodyState →
      ResourceSignal

    resourceDemand :
      WholeBodyResourceKind →
      BodyState →
      LatentState →
      ResourceDemand

    resourceSupply :
      WholeBodyResourceKind →
      BodyState →
      ResourceSupply

    neuralAdmissibility :
      BodyState →
      LatentState →
      NeuralAdmissibility

    carrierMeaning :
      String

    sigmaMeaning :
      String

open LatentBrainBodyCarrier public

record LossyObservationQuotient
  (B : LatentBrainBodyCarrier) : Setω where
  field
    ObservationWindow :
      Set

    FMRIReadout :
      Set

    PerceptClass :
      Set

    BehaviorClass :
      Set

    BodyResourceReadout :
      Set

    piFMRI :
      LatentBrainBodyCarrier.LatentState B →
      ObservationWindow →
      FMRIReadout

    piPercept :
      LatentBrainBodyCarrier.LatentState B →
      PerceptClass

    piBehavior :
      LatentBrainBodyCarrier.LatentState B →
      BehaviorClass

    piBodyResource :
      LatentBrainBodyCarrier.BodyState B →
      BodyResourceReadout

    sameFMRIClass :
      LatentBrainBodyCarrier.LatentState B →
      LatentBrainBodyCarrier.LatentState B →
      Set

    samePerceptClass :
      LatentBrainBodyCarrier.LatentState B →
      LatentBrainBodyCarrier.LatentState B →
      Set

    sameBehaviorClass :
      LatentBrainBodyCarrier.LatentState B →
      LatentBrainBodyCarrier.LatentState B →
      Set

    sameBodyResourceClass :
      LatentBrainBodyCarrier.BodyState B →
      LatentBrainBodyCarrier.BodyState B →
      Set

    fMRIIsManyToOne :
      String

    perceptIsManyToOne :
      String

    behaviorIsManyToOne :
      String

    bodyResourceIsManyToOne :
      String

open LossyObservationQuotient public

record JointInferenceNarrowing
  (B : LatentBrainBodyCarrier)
  (Q : LossyObservationQuotient B) : Setω where
  field
    EquivalenceClass :
      Set

    ResidualWidth :
      Set

    _<W_ :
      ResidualWidth →
      ResidualWidth →
      Set

    classFromFMRI :
      LatentBrainBodyCarrier.LatentState B →
      EquivalenceClass

    classFromPercept :
      LatentBrainBodyCarrier.LatentState B →
      EquivalenceClass

    classFromBehavior :
      LatentBrainBodyCarrier.LatentState B →
      EquivalenceClass

    classFromBodyResource :
      LatentBrainBodyCarrier.LatentState B →
      LatentBrainBodyCarrier.BodyState B →
      EquivalenceClass

    jointClass :
      LatentBrainBodyCarrier.LatentState B →
      LatentBrainBodyCarrier.BodyState B →
      EquivalenceClass

    residualWidth :
      EquivalenceClass →
      ResidualWidth

    jointNarrowsFMRI :
      (sigma : LatentBrainBodyCarrier.LatentState B) →
      (body : LatentBrainBodyCarrier.BodyState B) →
      residualWidth (jointClass sigma body) <W
      residualWidth (classFromFMRI sigma)

    jointNarrowsPercept :
      (sigma : LatentBrainBodyCarrier.LatentState B) →
      (body : LatentBrainBodyCarrier.BodyState B) →
      residualWidth (jointClass sigma body) <W
      residualWidth (classFromPercept sigma)

    jointNarrowsBehavior :
      (sigma : LatentBrainBodyCarrier.LatentState B) →
      (body : LatentBrainBodyCarrier.BodyState B) →
      residualWidth (jointClass sigma body) <W
      residualWidth (classFromBehavior sigma)

    jointNarrowsBodyResource :
      (sigma : LatentBrainBodyCarrier.LatentState B) →
      (body : LatentBrainBodyCarrier.BodyState B) →
      residualWidth (jointClass sigma body) <W
      residualWidth (classFromBodyResource sigma body)

    jointClassIsStillQuotient :
      String

    noUniqueStateRecoveryFromJointClass :
      Bool

    noUniqueStateRecoveryFromJointClassIsTrue :
      noUniqueStateRecoveryFromJointClass ≡ true

open JointInferenceNarrowing public

record WholeBodyResourceConstraint
  (B : LatentBrainBodyCarrier) : Setω where
  field
    ResourceResidual :
      Set

    ResourceGate :
      Set

    resourceResidual :
      WholeBodyResourceKind →
      LatentBrainBodyCarrier.BodyState B →
      LatentBrainBodyCarrier.LatentState B →
      ResourceResidual

    resourceGate :
      ResourceResidual →
      ResourceGate

    resourceGateFeedsNeuralAdmissibility :
      WholeBodyResourceKind →
      (body : LatentBrainBodyCarrier.BodyState B) →
      (sigma : LatentBrainBodyCarrier.LatentState B) →
      ResourceGate →
      LatentBrainBodyCarrier.NeuralAdmissibility B →
      Set

    bloodOxygenGlucoseThermalCardioAreInScope :
      List WholeBodyResourceKind

    brainOnlyQuantitativePhysiologyIsForbidden :
      String

open WholeBodyResourceConstraint public

record BidirectionalBrainBodyObservationBridge : Setω where
  field
    baseBrainBridge :
      DASHIBrainBridge

    latentBrainBodyCarrier :
      LatentBrainBodyCarrier

    lossyObservationQuotient :
      LossyObservationQuotient latentBrainBodyCarrier

    jointInferenceNarrowing :
      JointInferenceNarrowing
        latentBrainBodyCarrier
        lossyObservationQuotient

    wholeBodyResourceConstraint :
      WholeBodyResourceConstraint latentBrainBodyCarrier

    kernelFMRI :
      Set

    kernelPercept :
      Set

    kernelBehavior :
      Set

    kernelBodyResource :
      Set

    complementaryKernelTarget :
      kernelFMRI →
      kernelPercept →
      kernelBehavior →
      kernelBodyResource →
      Set

    bridgeMeaning :
      String

open BidirectionalBrainBodyObservationBridge public

record BidirectionalBrainObservationBoundary : Set where
  field
    status :
      String

    pipeline :
      List String

    latentStateRole :
      String

    quotientRole :
      String

    jointInferenceRole :
      String

    wholeBodyResourceRole :
      String

    nonPromotionBoundaries :
      List NonPromotionBoundary

    exactFirstMissing :
      List BidirectionalObservationFirstMissing

    fMRIIsPercept :
      Bool

    fMRIIsPerceptIsFalse :
      fMRIIsPercept ≡ false

    reportIsGroundTruth :
      Bool

    reportIsGroundTruthIsFalse :
      reportIsGroundTruth ≡ false

    qualiaClosure :
      Bool

    qualiaClosureIsFalse :
      qualiaClosure ≡ false

    cognitionClosure :
      Bool

    cognitionClosureIsFalse :
      cognitionClosure ≡ false

    latentStateRecovery :
      Bool

    latentStateRecoveryIsFalse :
      latentStateRecovery ≡ false

    empiricalValidationClosed :
      Bool

    empiricalValidationClosedIsFalse :
      empiricalValidationClosed ≡ false

    allowedClaim :
      List String

    forbiddenClaim :
      List String

open BidirectionalBrainObservationBoundary public

canonicalBidirectionalBrainObservationBoundary :
  BidirectionalBrainObservationBoundary
canonicalBidirectionalBrainObservationBoundary =
  record
    { status =
        "bidirectional observation quotient target only; non-promoting"
    ; pipeline =
        "latent sigma_t brain/body state"
        ∷ "lossy fMRI, percept, behavior, and body-resource quotients"
        ∷ "joint inference narrows an observational equivalence class"
        ∷ "whole-body resource gates feed neural admissibility"
        ∷ "no latent recovery, qualia closure, or cognition closure"
        ∷ []
    ; latentStateRole =
        "sigma_t is a latent carrier used only through quotient families; it is not claimed as a uniquely recoverable canonical cognitive state"
    ; quotientRole =
        "pi_fMRI, pi_percept, pi_behavior, and pi_bodyResource are many-to-one observation maps"
    ; jointInferenceRole =
        "combined quotients may shrink the residual equivalence class [sigma], but the joint class remains a quotient"
    ; wholeBodyResourceRole =
        "blood, oxygen, glucose, thermal load, and cardiovascular work constrain neural admissibility before physiological claims are allowed"
    ; nonPromotionBoundaries =
        fMRINotPercept
        ∷ reportNotGroundTruth
        ∷ noQualiaClosure
        ∷ noCognitionClosure
        ∷ noLatentStateRecovery
        ∷ noBrainOnlyPhysiology
        ∷ []
    ; exactFirstMissing =
        missingLatentStateModelReceipt
        ∷ missingFMRIQuotientCalibration
        ∷ missingPerceptReportBinding
        ∷ missingBehaviorPolicyBinding
        ∷ missingBodyResourceInstrumentation
        ∷ missingJointInferenceMetric
        ∷ missingKernelComplementarityReceipt
        ∷ missingEmpiricalComparisonRun
        ∷ []
    ; fMRIIsPercept =
        false
    ; fMRIIsPerceptIsFalse =
        refl
    ; reportIsGroundTruth =
        false
    ; reportIsGroundTruthIsFalse =
        refl
    ; qualiaClosure =
        false
    ; qualiaClosureIsFalse =
        refl
    ; cognitionClosure =
        false
    ; cognitionClosureIsFalse =
        refl
    ; latentStateRecovery =
        false
    ; latentStateRecoveryIsFalse =
        refl
    ; empiricalValidationClosed =
        false
    ; empiricalValidationClosedIsFalse =
        refl
    ; allowedClaim =
        "fMRI, perceptual report, behavior, and body-resource readouts can be modeled as complementary lossy quotients of latent brain/body dynamics"
        ∷ "joint inference can narrow an observational equivalence class when complementarity receipts and metrics are supplied"
        ∷ "whole-body resource constraints must feed neural admissibility for quantitative physiological claims"
        ∷ []
    ; forbiddenClaim =
        "fMRI is not the percept"
        ∷ "subjective report is not ground truth"
        ∷ "joint inference is not latent-state recovery"
        ∷ "this module proves no qualia, cognition, consciousness, or empirical brain closure"
        ∷ "brain dynamics must not be isolated from body resource constraints for quantitative physiology"
        ∷ []
    }

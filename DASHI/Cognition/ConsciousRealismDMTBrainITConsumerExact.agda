module DASHI.Cognition.ConsciousRealismDMTBrainITConsumerExact where

-- Consumer-relative bridge, NOT an experimental Brain-IT/DMT result.
-- External Brain-IT source: Roman Beliy, Amit Zalcher, Jonathan Kogman,
-- Navve Wasserman, Michal Irani; Brain-IT: Image Reconstruction from fMRI
-- via Brain-Interaction Transformer; arXiv:2510.25976v2 (ICLR 2026).
-- DMT imaging: Timmermann, Roseman, Haridas, Rosas et al.,
-- Human brain effects of DMT assessed via EEG-fMRI (PNAS 2023),
-- DOI 10.1073/pnas.2218949120.
-- The invented finite case does not identify a human neural/qualia kernel.

open import DASHI.Core.Prelude
import DASHI.Core.CoarseFineFabricCalculusExact as Fabric
import DASHI.Cognition.ConsciousRealismDMTIdentifiabilityExact as DMT

data ViewedStimulus : Set where
  imageA imageB : ViewedStimulus

data ConcealedTarget : Set where
  targetA targetB : ConcealedTarget

record TrialWorld : Set where
  constructor trialWorld
  field
    viewed : ViewedStimulus
    concealed : ConcealedTarget
open TrialWorld public

-- A deliberately PERFECT observed stimulus, stronger than real human fMRI:
-- if even this cannot decode an independent secret, no Brain-IT performance
-- number by itself entails a target-transfer or conscious-entity result.
observedStimulus : TrialWorld → ViewedStimulus
observedStimulus = viewed

secretConsumer : TrialWorld → ConcealedTarget
secretConsumer = concealed

perfectViewedStimulusDecoder : ViewedStimulus → ViewedStimulus
perfectViewedStimulusDecoder stimulus = stimulus

perfectStimulusReconstruction :
  (world : TrialWorld) →
  perfectViewedStimulusDecoder (observedStimulus world) ≡ viewed world
perfectStimulusReconstruction _ = refl

sameViewedImageDifferentSecretA : TrialWorld
sameViewedImageDifferentSecretA = trialWorld imageA targetA

sameViewedImageDifferentSecretB : TrialWorld
sameViewedImageDifferentSecretB = trialWorld imageA targetB

concealedTargetsDistinct : targetA ≡ targetB → ⊥
concealedTargetsDistinct ()

-- The shared generic owner gives the collision / nonfactorability theorem.
-- This is not the unmerged Brain-IT branch's empirical V2C mapping.
secretProjectionCollision :
  Fabric.ProjectionCollision observedStimulus secretConsumer
secretProjectionCollision = record
  { Fabric.ProjectionCollision.left = sameViewedImageDifferentSecretA
  ; Fabric.ProjectionCollision.right = sameViewedImageDifferentSecretB
  ; Fabric.ProjectionCollision.sameProjection = refl
  ; Fabric.ProjectionCollision.consumerSeparates = concealedTargetsDistinct
  }

noUniversalConcealedTargetFromStimulus :
  (decode : ViewedStimulus → ConcealedTarget) →
  ((world : TrialWorld) →
    secretConsumer world ≡ decode (observedStimulus world)) → ⊥
noUniversalConcealedTargetFromStimulus decode recovers =
  Fabric.consumerCannotFactorThroughProjection
    secretProjectionCollision decode recovers

noUniversalOriginDecoderFromSharedLaw :
  {K : Set} (q : K) (decode : K → DMT.OriginHypothesis) →
  decode q ≡ DMT.endogenousModel →
  decode q ≡ DMT.independentAgentModel → ⊥
noUniversalOriginDecoderFromSharedLaw = DMT.noUniversalOriginDecoder

record BrainITDMTCrossLaneBoundary : Set where
  constructor brainITDMTCrossLaneBoundary
  field
    toyViewedStimulusExactlyDecodable : Bool
    toyViewedStimulusExactlyDecodableIsTrue :
      toyViewedStimulusExactlyDecodable ≡ true
    actualBOLDEqualsPerfectToyObservation : Bool
    actualBOLDEqualsPerfectToyObservationIsFalse :
      actualBOLDEqualsPerfectToyObservation ≡ false
    viewedDecodingProvesConcealedInformation : Bool
    viewedDecodingProvesConcealedInformationIsFalse :
      viewedDecodingProvesConcealedInformation ≡ false
    imageDecodingProvesConsciousOntology : Bool
    imageDecodingProvesConsciousOntologyIsFalse :
      imageDecodingProvesConsciousOntology ≡ false
    brainITAndDMTParticipantDataJointlyReplayed : Bool
    brainITAndDMTParticipantDataJointlyReplayedIsFalse :
      brainITAndDMTParticipantDataJointlyReplayed ≡ false

canonicalBrainITDMTCrossLaneBoundary : BrainITDMTCrossLaneBoundary
canonicalBrainITDMTCrossLaneBoundary =
  brainITDMTCrossLaneBoundary true refl false refl false refl false refl false refl

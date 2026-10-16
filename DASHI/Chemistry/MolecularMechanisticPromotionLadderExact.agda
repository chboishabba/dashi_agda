module DASHI.Chemistry.MolecularMechanisticPromotionLadderExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- REUSABLE MOLECULAR MECHANISTIC PROMOTION LADDER
--
-- Cross-pollinated from the NH3 max-cut without importing its molecule-specific
-- or Monster-specific claims. The ladder records increasing same-object depth:
-- identity -> structure/state -> Hamiltonian/PES -> dynamics -> literal released
-- artifact -> independent numerical replay. Causal/flux discrimination remains
-- an orthogonal consumer obligation.
------------------------------------------------------------------------

data PromotionStage : Set where
  reactionIdentity
  atomElectronBookkeeping
  sourceBackedStructure
  symbolicStateCarrier
  sourceBackedHamiltonianOrPES
  sourceBackedDynamics
  authorReleasedNumericalArtifact
  independentlyReplayedNumericalArtifact
  numericalStateCoefficients : PromotionStage

data ArtifactAuthority : Set where
  noArtifact
  primaryPaperArtifact
  authorReleasedArtifact
  independentReplicationArtifact
  dashiReconstructionArtifact : ArtifactAuthority

record MolecularMechanisticPromotion : Set where
  constructor molecularMechanisticPromotion
  field
    objectKey : String
    blockedConsumerReference : String
    highestPaidStage : PromotionStage
    structureReference : String
    stateCarrierReference : String
    hamiltonianOrPESReference : String
    dynamicsReference : String
    releasedArtifactReference : String
    independentReplayReference : String
    numericalCoefficientReference : String
    artifactAuthority : ArtifactAuthority
    sameObjectReference : String
    unpaidResidual : String
    promotionCreatesScientificAuthority : Bool
    promotionCreatesScientificAuthorityIsFalse : promotionCreatesScientificAuthority ≡ false
    promotionCreatesCausalFluxEvidence : Bool
    promotionCreatesCausalFluxEvidenceIsFalse : promotionCreatesCausalFluxEvidence ≡ false

open MolecularMechanisticPromotion public

record MolecularMechanisticPromotionBoundary : Set where
  constructor molecularMechanisticPromotionBoundary
  field
    structureCreatesWavefunction : Bool
    structureCreatesWavefunctionIsFalse : structureCreatesWavefunction ≡ false
    symbolicHamiltonianCreatesNumericalEigenvector : Bool
    symbolicHamiltonianCreatesNumericalEigenvectorIsFalse : symbolicHamiltonianCreatesNumericalEigenvector ≡ false
    authorReleasedArtifactEqualsIndependentAuthority : Bool
    authorReleasedArtifactEqualsIndependentAuthorityIsFalse : authorReleasedArtifactEqualsIndependentAuthority ≡ false
    independentlyReplayedArtifactEqualsPhysicalTruth : Bool
    independentlyReplayedArtifactEqualsPhysicalTruthIsFalse : independentlyReplayedArtifactEqualsPhysicalTruth ≡ false
    mechanisticPromotionPaysCausalFlux : Bool
    mechanisticPromotionPaysCausalFluxIsFalse : mechanisticPromotionPaysCausalFlux ≡ false
    deeperMicroscopicModelAlwaysHigherAcquisitionPriority : Bool
    deeperMicroscopicModelAlwaysHigherAcquisitionPriorityIsFalse :
      deeperMicroscopicModelAlwaysHigherAcquisitionPriority ≡ false
    consumerSpecificDiscriminatorControlsPriority : Bool
    consumerSpecificDiscriminatorControlsPriorityIsTrue :
      consumerSpecificDiscriminatorControlsPriority ≡ true

open MolecularMechanisticPromotionBoundary public

canonicalMolecularMechanisticPromotionBoundary : MolecularMechanisticPromotionBoundary
canonicalMolecularMechanisticPromotionBoundary =
  molecularMechanisticPromotionBoundary
    false refl false refl false refl false refl false refl false refl true refl

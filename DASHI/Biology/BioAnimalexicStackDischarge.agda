module DASHI.Biology.BioAnimalexicStackDischarge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Biology.CellDifferentiationCommunicationBridge as Cell
import DASHI.Biology.CrossSpeciesOntologyTranslationBridge as Cross
import DASHI.Biology.EmbodiedMotorMultisensoryBridge as Embodied

------------------------------------------------------------------------
-- Aggregate BioAnimalexic stack vocabulary.
--
-- This module does not construct a full biology closure.  It only records
-- that the new explicit physiology, embodied behaviour, and cross-species
-- ontology surfaces are inhabited and remain behind non-promotion gates.

data BioAnimalexicStackSector : Set where
  genomeRegulationSector : BioAnimalexicStackSector
  cellDifferentiationSector : BioAnimalexicStackSector
  cellCommunicationSector : BioAnimalexicStackSector
  metabolismCirculationSector : BioAnimalexicStackSector
  endocrineImmuneSector : BioAnimalexicStackSector
  tissueOrganSensorSector : BioAnimalexicStackSector
  motorPainBodySenseSector : BioAnimalexicStackSector
  multisensoryConnectomeSector : BioAnimalexicStackSector
  memorySocialEcologySector : BioAnimalexicStackSector
  crossSpeciesOntologySector : BioAnimalexicStackSector

data BioAnimalexicPromotionBoundary : Set where
  noDiseaseCausationClaim : BioAnimalexicPromotionBoundary
  noFullDevelopmentRecovery : BioAnimalexicPromotionBoundary
  noCellFatePredictionClaim : BioAnimalexicPromotionBoundary
  noBiologyClosureClaim : BioAnimalexicPromotionBoundary
  noIntentRecoveryClaim : BioAnimalexicPromotionBoundary
  noPainQualiaIdentityClaim : BioAnimalexicPromotionBoundary
  noFullMotorPolicyClaim : BioAnimalexicPromotionBoundary
  noSensorFusionClosureClaim : BioAnimalexicPromotionBoundary
  noQualiaIdentityClaim : BioAnimalexicPromotionBoundary
  noSpeciesIsomorphismClaim : BioAnimalexicPromotionBoundary
  noAnthropomorphicPromotionClaim : BioAnimalexicPromotionBoundary
  noContextFreeTranslationClaim : BioAnimalexicPromotionBoundary

canonicalBioAnimalexicSectors : List BioAnimalexicStackSector
canonicalBioAnimalexicSectors =
  genomeRegulationSector
  ∷ cellDifferentiationSector
  ∷ cellCommunicationSector
  ∷ metabolismCirculationSector
  ∷ endocrineImmuneSector
  ∷ tissueOrganSensorSector
  ∷ motorPainBodySenseSector
  ∷ multisensoryConnectomeSector
  ∷ memorySocialEcologySector
  ∷ crossSpeciesOntologySector
  ∷ []

canonicalBioAnimalexicBoundaries : List BioAnimalexicPromotionBoundary
canonicalBioAnimalexicBoundaries =
  noDiseaseCausationClaim
  ∷ noFullDevelopmentRecovery
  ∷ noCellFatePredictionClaim
  ∷ noBiologyClosureClaim
  ∷ noIntentRecoveryClaim
  ∷ noPainQualiaIdentityClaim
  ∷ noFullMotorPolicyClaim
  ∷ noSensorFusionClosureClaim
  ∷ noQualiaIdentityClaim
  ∷ noSpeciesIsomorphismClaim
  ∷ noAnthropomorphicPromotionClaim
  ∷ noContextFreeTranslationClaim
  ∷ []

------------------------------------------------------------------------
-- Aggregate discharge witness.

record BioAnimalexicStackDischarge : Set₁ where
  field
    sectors :
      List BioAnimalexicStackSector

    boundaries :
      List BioAnimalexicPromotionBoundary

    physiologyBridge :
      Cell.CellDifferentiationCommunicationBridge

    physiologyObservation :
      Cell.PhysiologyObservation physiologyBridge

    physiologyCandidate :
      Cell.CandidateIntegratedPhysiologyState
        physiologyBridge
        physiologyObservation

    physiologyReceipt :
      Cell.PhysiologyPromotionReceipt
        physiologyBridge
        physiologyObservation
        physiologyCandidate

    physiologyMeaning :
      Cell.PromotedBoundedPhysiologyMeaning
        physiologyBridge
        physiologyObservation
        physiologyCandidate
        physiologyReceipt

    physiologyNonPromotion :
      Cell.NonPromotionGuardCertificate physiologyBridge

    embodiedBridge :
      Embodied.EmbodiedMotorMultisensoryBridge
        Embodied.canonicalEmbodiedAnimalexicSurface

    embodiedObservation :
      Embodied.EmbodiedMultisensoryObservation
        (Embodied.surface embodiedBridge)

    embodiedIntegration :
      Embodied.MultisensoryBodyIntegration
        embodiedObservation

    embodiedPromotionGate :
      Embodied.EmbodiedAnimalexicPromotionGate
        embodiedBridge
        embodiedObservation
        embodiedIntegration

    embodiedNonPromotion :
      Embodied.EmbodiedNonPromotionCertificate embodiedBridge

    crossSpeciesBridge :
      Cross.CrossSpeciesOntologyTranslationBridge

    crossSpeciesNonPromotion :
      Cross.CrossSpeciesOntologyNonPromotionCertificate
        crossSpeciesBridge

    sectorsMatch :
      sectors ≡ canonicalBioAnimalexicSectors

    boundariesMatch :
      boundaries ≡ canonicalBioAnimalexicBoundaries

    nonPromoting :
      Bool

    nonPromotingIsTrue :
      nonPromoting ≡ true

    biologyClosureClaim :
      Bool

    biologyClosureClaimIsFalse :
      biologyClosureClaim ≡ false

    speciesUniversalDictionaryClaim :
      Bool

    speciesUniversalDictionaryClaimIsFalse :
      speciesUniversalDictionaryClaim ≡ false

    dischargeReading :
      String

open BioAnimalexicStackDischarge public

canonicalBioAnimalexicStackDischarge :
  BioAnimalexicStackDischarge
canonicalBioAnimalexicStackDischarge =
  record
    { sectors = canonicalBioAnimalexicSectors
    ; boundaries = canonicalBioAnimalexicBoundaries
    ; physiologyBridge =
        Cell.canonicalCellDifferentiationCommunicationBridge
    ; physiologyObservation =
        Cell.canonicalPhysiologyObservation
    ; physiologyCandidate =
        Cell.canonicalCandidateIntegratedPhysiologyState
    ; physiologyReceipt =
        Cell.canonicalPhysiologyPromotionReceipt
    ; physiologyMeaning =
        Cell.canonicalPromotedBoundedPhysiologyMeaning
    ; physiologyNonPromotion =
        Cell.canonicalNonPromotionGuardCertificate
    ; embodiedBridge =
        Embodied.canonicalEmbodiedMotorMultisensoryBridge
    ; embodiedObservation =
        Embodied.canonicalEmbodiedMultisensoryObservation
    ; embodiedIntegration =
        Embodied.canonicalMultisensoryBodyIntegration
    ; embodiedPromotionGate =
        Embodied.canonicalEmbodiedAnimalexicPromotionGate
    ; embodiedNonPromotion =
        Embodied.canonicalEmbodiedNonPromotionCertificateForToy
    ; crossSpeciesBridge =
        Cross.canonicalCrossSpeciesOntologyTranslationBridge
    ; crossSpeciesNonPromotion =
        Cross.canonicalCrossSpeciesOntologyNonPromotionCertificate
    ; sectorsMatch = refl
    ; boundariesMatch = refl
    ; nonPromoting = true
    ; nonPromotingIsTrue = refl
    ; biologyClosureClaim = false
    ; biologyClosureClaimIsFalse = refl
    ; speciesUniversalDictionaryClaim = false
    ; speciesUniversalDictionaryClaimIsFalse = refl
    ; dischargeReading =
        "BioAnimalexic is discharged as an inhabited, non-promoting stack from cell communication and physiology through embodied behaviour to context-bound cross-species ontology translation."
    }

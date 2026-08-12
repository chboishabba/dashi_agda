module DASHI.Crypto.MLKEMSecurityDependencyGraphExact where

------------------------------------------------------------------------
-- ML-KEM SECURITY DEPENDENCY GRAPH
--
-- Primary references:
-- NIST FIPS 203, "Module-Lattice-Based Key-Encapsulation Mechanism Standard",
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Gorjan Alagic, Elaine Barker, Lily Chen, Dustin Moody, Angela Robinson,
-- Hamilton Silberg, Noah Waller,
-- "Recommendations for Key-Encapsulation Mechanisms", NIST SP 800-227,
-- 2025. DOI: 10.6028/NIST.SP.800-227.
--
-- NIST SP 800-227 separates theoretical, implementation and deployment
-- security.  This file formalises the theoretical/protocol dependency surface
-- needed for blue-team reasoning.  No hardness assumption is proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Crypto.PublicSecretFactorisationAttackExact as Attack

------------------------------------------------------------------------
-- Named nodes are not claims.  Edges record which obligations support which
-- higher-level properties and make the assumption boundary explicit.
------------------------------------------------------------------------

data SecurityNode : Set where
  keyGenerationCorrect
  encapsulationCorrect
  decapsulationCorrect
  generatedKeyAgreement
  mlweSearchHard
  mlweDecisionHard
  parameterEstimatesAdequate
  hashXofAssumptionsHold
  ccaTransformSound
  implicitRejectionRouteHidden
  noExactPublicSecretRecovery
  noProtectedPredicateLeak
  challengeKeyIndistinguishable
  keyOwnershipBound
  transcriptIntegrityBound
  keyConfirmationPasses
  applicationKeyEstablished : SecurityNode

data DependsOn : SecurityNode → SecurityNode → Set where
  agreementOnKeyGen : DependsOn generatedKeyAgreement keyGenerationCorrect
  agreementOnEncapsulation : DependsOn generatedKeyAgreement encapsulationCorrect
  agreementOnDecapsulation : DependsOn generatedKeyAgreement decapsulationCorrect

  noRecoveryOnMLWESearch : DependsOn noExactPublicSecretRecovery mlweSearchHard
  noRecoveryOnParameters : DependsOn noExactPublicSecretRecovery parameterEstimatesAdequate

  indistinguishabilityOnMLWEDecision :
    DependsOn challengeKeyIndistinguishable mlweDecisionHard
  indistinguishabilityOnHashXof :
    DependsOn challengeKeyIndistinguishable hashXofAssumptionsHold
  indistinguishabilityOnCCA :
    DependsOn challengeKeyIndistinguishable ccaTransformSound
  indistinguishabilityOnImplicitRejection :
    DependsOn challengeKeyIndistinguishable implicitRejectionRouteHidden
  indistinguishabilityOnNoRecovery :
    DependsOn challengeKeyIndistinguishable noExactPublicSecretRecovery
  indistinguishabilityOnNoLeak :
    DependsOn challengeKeyIndistinguishable noProtectedPredicateLeak

  applicationOnAgreement : DependsOn applicationKeyEstablished generatedKeyAgreement
  applicationOnChallengeSecurity :
    DependsOn applicationKeyEstablished challengeKeyIndistinguishable
  applicationOnOwnership : DependsOn applicationKeyEstablished keyOwnershipBound
  applicationOnIntegrity : DependsOn applicationKeyEstablished transcriptIntegrityBound

  confirmationOnAgreement : DependsOn keyConfirmationPasses generatedKeyAgreement
  confirmationOnOwnership : DependsOn keyConfirmationPasses keyOwnershipBound
  confirmationOnIntegrity : DependsOn keyConfirmationPasses transcriptIntegrityBound

------------------------------------------------------------------------
-- Exact break witnesses.
------------------------------------------------------------------------

NoExactPublicSecretRecovery :
  Attack.SecretLabelledProjection → Set₁
NoExactPublicSecretRecovery system =
  Attack.ExactPublicSecretRecovery system → ⊥

NoPublicSecretFactorisation :
  Attack.SecretLabelledProjection → Set₁
NoPublicSecretFactorisation system =
  Attack.PublicSecretFactorisation system → ⊥

publicFactorisationBreaksNoRecovery :
  ∀ {system} →
  Attack.PublicSecretFactorisation system →
  NoExactPublicSecretRecovery system →
  ⊥
publicFactorisationBreaksNoRecovery factorisation noRecovery =
  noRecovery (Attack.factorisationImpliesExactRecovery factorisation)

fullInversionBreaksNoRecovery :
  ∀ {system} →
  Attack.FullPublicInversion system →
  NoExactPublicSecretRecovery system →
  ⊥
fullInversionBreaksNoRecovery inversion noRecovery =
  noRecovery (Attack.fullInversionImpliesSecretRecovery inversion)

------------------------------------------------------------------------
-- Statewise blue-team obligations.
--
-- These fields separate what can be tested as a state contract from what is a
-- cryptographic hardness premise.  Passing the state tests does not prove the
-- hardness premises; failing one identifies a concrete protocol-level break.
------------------------------------------------------------------------

record StatewiseBlueTeamContract : Set₁ where
  constructor statewiseBlueTeamContract
  field
    KeyState PublicState CipherState SharedSecret : Set

    keyStateWellFormed : KeyState → Set
    publicStateWellFormed : PublicState → Set
    cipherStateWellFormed : CipherState → Set

    publicDerivedFromKey : KeyState → PublicState
    decapsulatedSecret : KeyState → CipherState → SharedSecret

    generatedStateAgreement : Set
    malformedCipherStillReturnsSecretState : Set
    internalAcceptRejectRouteNotProtocolVisible : Set
    candidateKeyTestingSeparatedFromCandidateSearch : Set
    exactPublicSecretRecoveryAbsent : Set
    protectedPredicateLeakAbsent : Set

open StatewiseBlueTeamContract public

------------------------------------------------------------------------
-- Claim boundary.  The dependency graph itself proves neither MLWE hardness
-- nor IND-CCA security; it tells us exactly where a successful attack witness
-- would cut the graph.
------------------------------------------------------------------------

record MLKEMDependencyBoundary : Set where
  constructor mlkemDependencyBoundary
  field
    graphProvesMLWEHardness : Bool
    graphProvesMLWEHardnessIsFalse : graphProvesMLWEHardness ≡ false
    graphProvesINDCCA : Bool
    graphProvesINDCCAIsFalse : graphProvesINDCCA ≡ false
    exactFactorisationWouldBeBreakWitness : Bool
    exactFactorisationWouldBeBreakWitnessIsTrue :
      exactFactorisationWouldBeBreakWitness ≡ true

canonicalMLKEMDependencyBoundary : MLKEMDependencyBoundary
canonicalMLKEMDependencyBoundary =
  mlkemDependencyBoundary false refl false refl true refl

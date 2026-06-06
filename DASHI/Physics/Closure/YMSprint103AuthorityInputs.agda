module DASHI.Physics.Closure.YMSprint103AuthorityInputs where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.YMSprint102ProofObligationIndexReceipt
  as Sprint102

------------------------------------------------------------------------
-- Sprint 103 YM authority inputs, Worker A scope.
--
-- Sprint 102 indexed eight analytic obligations.  This module implements
-- authority inputs 1-3 only as inhabited records.  These are scoped external
-- analytic imports with source and proof-argument text; they are not native
-- Agda derivations of the Balaban estimates and do not promote Clay/YM.

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

balabanCMP98LocalOscillationBoundAuthorityAccepted : Bool
balabanCMP98LocalOscillationBoundAuthorityAccepted = true

balabanCMP98AveragingKernelIsProbabilityAuthorityAccepted : Bool
balabanCMP98AveragingKernelIsProbabilityAuthorityAccepted = true

balabanCMP116PolymerMassBoundAuthorityAccepted : Bool
balabanCMP116PolymerMassBoundAuthorityAccepted = true

authorityInputsImplemented : Bool
authorityInputsImplemented = true

downstreamObligationsStillOpen : Bool
downstreamObligationsStillOpen = true

record BalabanCMP98LocalOscillationBound : Set where
  constructor mkBalabanCMP98LocalOscillationBound
  field
    source :
      String
    proofArgument :
      String
    scopedClaim :
      String
    importedAsAuthority :
      balabanCMP98LocalOscillationBoundAuthorityAccepted ≡ true
    notNativeFormalDerivation :
      true ≡ true

record BalabanCMP98AveragingKernelIsProbability : Set where
  constructor mkBalabanCMP98AveragingKernelIsProbability
  field
    source :
      String
    proofArgument :
      String
    scopedClaim :
      String
    importedAsAuthority :
      balabanCMP98AveragingKernelIsProbabilityAuthorityAccepted ≡ true
    notNativeFormalDerivation :
      true ≡ true

record BalabanCMP116PolymerMassBound : Set where
  constructor mkBalabanCMP116PolymerMassBound
  field
    source :
      String
    proofArgument :
      String
    scopedClaim :
      String
    importedAsAuthority :
      balabanCMP116PolymerMassBoundAuthorityAccepted ≡ true
    notNativeFormalDerivation :
      true ≡ true

canonicalBalabanCMP98LocalOscillationBound :
  BalabanCMP98LocalOscillationBound
canonicalBalabanCMP98LocalOscillationBound =
  mkBalabanCMP98LocalOscillationBound
    "Balaban CMP 98 (1985), local regularity and averaging estimates for lattice gauge fields"
    "Use the finite-range Balaban block-averaging locality estimate for Q_hp: each spatial link has a bounded influence cone at scale k, yielding a local oscillation bound with the L^{-2k} decay required by the Sprint102 obligation."
    "BalabanCMP98LocalOscillationBound: local oscillation of Q_hp is uniformly bounded by a CMP98 constant times L^{-2k} on the scoped lattice-gauge input lane."
    refl
    refl

canonicalBalabanCMP98AveragingKernelIsProbability :
  BalabanCMP98AveragingKernelIsProbability
canonicalBalabanCMP98AveragingKernelIsProbability =
  mkBalabanCMP98AveragingKernelIsProbability
    "Balaban CMP 98 (1985), Haar-convolution averaging kernel used in the block-spin construction"
    "The averaging kernel is a normalized Haar-convolution probability kernel on the compact gauge group, so its total mass is one and the authority consequence C_avg <= 1 is available."
    "BalabanCMP98AveragingKernelIsProbability: the CMP98 averaging kernel is probability normalized, giving the Sprint102 C_avg <= 1 input."
    refl
    refl

canonicalBalabanCMP116PolymerMassBound :
  BalabanCMP116PolymerMassBound
canonicalBalabanCMP116PolymerMassBound =
  mkBalabanCMP116PolymerMassBound
    "Balaban CMP 116 (1988), small-field polymer expansion and mass lower bound"
    "The small-field polymer expansion supplies a positive polymer mass parameter and exponential polymer-weight decay, giving the mass positivity input required before the Dobrushin/WC3 chain."
    "BalabanCMP116PolymerMassBound: polymer activities in the scoped small-field regime carry a positive mass bound with exponential suppression."
    refl
    refl

record YMSprint103AuthorityInputs : Set₁ where
  field
    sprint102Index :
      Sprint102.YMSprint102ProofObligationIndexReceipt
    localOscillation :
      BalabanCMP98LocalOscillationBound
    averagingKernelProbability :
      BalabanCMP98AveragingKernelIsProbability
    polymerMass :
      BalabanCMP116PolymerMassBound
    localOscillationAccepted :
      balabanCMP98LocalOscillationBoundAuthorityAccepted ≡ true
    averagingKernelProbabilityAccepted :
      balabanCMP98AveragingKernelIsProbabilityAuthorityAccepted ≡ true
    polymerMassAccepted :
      balabanCMP116PolymerMassBoundAuthorityAccepted ≡ true
    implementedOnlyAuthorityInputsOneToThree :
      authorityInputsImplemented ≡ true
    laterSprint102ObligationsRemainOpen :
      downstreamObligationsStillOpen ≡ true
    noClayPromotion :
      clayYangMillsPromoted ≡ false

canonicalYMSprint103AuthorityInputs :
  YMSprint103AuthorityInputs
canonicalYMSprint103AuthorityInputs =
  record
    { sprint102Index =
        Sprint102.canonicalYMSprint102ProofObligationIndexReceipt
    ; localOscillation =
        canonicalBalabanCMP98LocalOscillationBound
    ; averagingKernelProbability =
        canonicalBalabanCMP98AveragingKernelIsProbability
    ; polymerMass =
        canonicalBalabanCMP116PolymerMassBound
    ; localOscillationAccepted =
        refl
    ; averagingKernelProbabilityAccepted =
        refl
    ; polymerMassAccepted =
        refl
    ; implementedOnlyAuthorityInputsOneToThree =
        refl
    ; laterSprint102ObligationsRemainOpen =
        refl
    ; noClayPromotion =
        refl
    }

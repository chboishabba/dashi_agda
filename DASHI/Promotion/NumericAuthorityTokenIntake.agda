module DASHI.Promotion.NumericAuthorityTokenIntake where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Promotion.NumericAndAuthorityObligations as Numeric
import DASHI.Promotion.NumericMeasuredAuthorityBinding as Binding

------------------------------------------------------------------------
-- Authority token intake for measured numeric constants.
--
-- NumericMeasuredAuthorityBinding names the measured slots and binds
-- complete metadata.  This module adds the next fail-closed surface:
-- typed token requests and responses for CODATA and PDG authority tokens.
-- It still does not load numeric values or promote measured numerics.

data NumericAuthorityProvider : Set where
  codataAuthorityProvider : NumericAuthorityProvider
  pdgAuthorityProvider : NumericAuthorityProvider

data TokenIntakeState : Set where
  tokenMissing : TokenIntakeState
  tokenMalformed : TokenIntakeState
  tokenAcceptedButValueNotLoaded : TokenIntakeState
  tokenAcceptedAndValueLoaded : TokenIntakeState

data TokenPayloadClass : Set where
  codataMeasuredConstantPayload : TokenPayloadClass
  pdgMeasuredConstantPayload : TokenPayloadClass

record NumericAuthorityTokenRequest : Set₁ where
  field
    requestLabel : String
    provider : NumericAuthorityProvider
    payloadClass : TokenPayloadClass
    measuredSlot : Binding.MeasuredConstantSlot
    consumerBinding : Binding.MeasuredConstantConsumerBinding
    requestedTokenName : String
    requestedValueIngestionReceiptName : String
    sourceBindingReceipt :
      Binding.NumericMeasuredAuthorityBindingReceipt
    sourceObligationIndex :
      Numeric.NumericAndAuthorityObligationIndex
    sourceRegistry : Registry.ConstantsRegistry
    metadataAlreadyBound : Bool
    metadataAlreadyBoundIsTrue : metadataAlreadyBound ≡ true
    tokenRequiredBeforeNumericUse : Bool
    tokenRequiredBeforeNumericUseIsTrue :
      tokenRequiredBeforeNumericUse ≡ true
    valueIngestionRequiredBeforePromotion : Bool
    valueIngestionRequiredBeforePromotionIsTrue :
      valueIngestionRequiredBeforePromotion ≡ true

open NumericAuthorityTokenRequest public

mkTokenRequest :
  String →
  NumericAuthorityProvider →
  TokenPayloadClass →
  Binding.MeasuredConstantSlot →
  Binding.MeasuredConstantConsumerBinding →
  String →
  String →
  NumericAuthorityTokenRequest
mkTokenRequest
  label provider payload slot binding tokenName ingestionName =
  record
    { requestLabel = label
    ; provider = provider
    ; payloadClass = payload
    ; measuredSlot = slot
    ; consumerBinding = binding
    ; requestedTokenName = tokenName
    ; requestedValueIngestionReceiptName = ingestionName
    ; sourceBindingReceipt =
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
    ; sourceObligationIndex =
        Numeric.canonicalNumericAndAuthorityObligationIndex
    ; sourceRegistry =
        Registry.repoWideConstantsRegistry
    ; metadataAlreadyBound =
        Binding.MeasuredConstantConsumerBinding.metadataBoundForConsumer
          binding
    ; metadataAlreadyBoundIsTrue =
        Binding.MeasuredConstantConsumerBinding.metadataBoundForConsumerIsTrue
          binding
    ; tokenRequiredBeforeNumericUse = true
    ; tokenRequiredBeforeNumericUseIsTrue = refl
    ; valueIngestionRequiredBeforePromotion = true
    ; valueIngestionRequiredBeforePromotionIsTrue = refl
    }

gTokenRequest : NumericAuthorityTokenRequest
gTokenRequest =
  mkTokenRequest
    "CODATA token request for Newtonian gravitational constant G"
    codataAuthorityProvider
    codataMeasuredConstantPayload
    Binding.newtonianGSlot
    Binding.gConsumerBinding
    "accepted-CODATA-G-authority-token"
    "G-numeric-value-ingestion-receipt"

alphaTokenRequest : NumericAuthorityTokenRequest
alphaTokenRequest =
  mkTokenRequest
    "CODATA token request for fine-structure constant alpha"
    codataAuthorityProvider
    codataMeasuredConstantPayload
    Binding.fineStructureAlphaSlot
    Binding.alphaConsumerBinding
    "accepted-CODATA-alpha-authority-token"
    "alpha-numeric-value-ingestion-receipt"

electronMassTokenRequest : NumericAuthorityTokenRequest
electronMassTokenRequest =
  mkTokenRequest
    "CODATA token request for electron rest mass m_e"
    codataAuthorityProvider
    codataMeasuredConstantPayload
    Binding.electronMassSlot
    Binding.electronMassConsumerBinding
    "accepted-CODATA-m_e-authority-token"
    "m_e-numeric-value-ingestion-receipt"

protonMassTokenRequest : NumericAuthorityTokenRequest
protonMassTokenRequest =
  mkTokenRequest
    "CODATA token request for proton rest mass m_p"
    codataAuthorityProvider
    codataMeasuredConstantPayload
    Binding.protonMassSlot
    Binding.protonMassConsumerBinding
    "accepted-CODATA-m_p-authority-token"
    "m_p-numeric-value-ingestion-receipt"

epsilonZeroTokenRequest : NumericAuthorityTokenRequest
epsilonZeroTokenRequest =
  mkTokenRequest
    "CODATA token request for vacuum permittivity epsilon_0"
    codataAuthorityProvider
    codataMeasuredConstantPayload
    Binding.vacuumPermittivitySlot
    Binding.epsilonZeroConsumerBinding
    "accepted-CODATA-epsilon_0-authority-token"
    "epsilon_0-numeric-value-ingestion-receipt"

muZeroTokenRequest : NumericAuthorityTokenRequest
muZeroTokenRequest =
  mkTokenRequest
    "CODATA token request for vacuum permeability mu_0"
    codataAuthorityProvider
    codataMeasuredConstantPayload
    Binding.vacuumPermeabilitySlot
    Binding.muZeroConsumerBinding
    "accepted-CODATA-mu_0-authority-token"
    "mu_0-numeric-value-ingestion-receipt"

rydbergTokenRequest : NumericAuthorityTokenRequest
rydbergTokenRequest =
  mkTokenRequest
    "CODATA token request for Rydberg constant R_infinity"
    codataAuthorityProvider
    codataMeasuredConstantPayload
    Binding.rydbergConstantSlot
    Binding.rydbergConsumerBinding
    "accepted-CODATA-R_infinity-authority-token"
    "R_infinity-numeric-value-ingestion-receipt"

higgsMassTokenRequest : NumericAuthorityTokenRequest
higgsMassTokenRequest =
  mkTokenRequest
    "PDG token request for Higgs boson mass m_H"
    pdgAuthorityProvider
    pdgMeasuredConstantPayload
    Binding.higgsMassSlot
    Binding.higgsMassConsumerBinding
    "accepted-PDG-m_H-authority-token"
    "m_H-numeric-value-ingestion-receipt"

alphaSTokenRequest : NumericAuthorityTokenRequest
alphaSTokenRequest =
  mkTokenRequest
    "PDG token request for strong coupling alpha_s"
    pdgAuthorityProvider
    pdgMeasuredConstantPayload
    Binding.strongCouplingSlot
    Binding.alphaSConsumerBinding
    "accepted-PDG-alpha_s-authority-token"
    "alpha_s-numeric-value-ingestion-receipt"

canonicalTokenRequests : List NumericAuthorityTokenRequest
canonicalTokenRequests =
  gTokenRequest
  ∷ alphaTokenRequest
  ∷ electronMassTokenRequest
  ∷ protonMassTokenRequest
  ∷ epsilonZeroTokenRequest
  ∷ muZeroTokenRequest
  ∷ rydbergTokenRequest
  ∷ higgsMassTokenRequest
  ∷ alphaSTokenRequest
  ∷ []

canonicalCODATATokenRequests : List NumericAuthorityTokenRequest
canonicalCODATATokenRequests =
  gTokenRequest
  ∷ alphaTokenRequest
  ∷ electronMassTokenRequest
  ∷ protonMassTokenRequest
  ∷ epsilonZeroTokenRequest
  ∷ muZeroTokenRequest
  ∷ rydbergTokenRequest
  ∷ []

canonicalPDGTokenRequests : List NumericAuthorityTokenRequest
canonicalPDGTokenRequests =
  higgsMassTokenRequest
  ∷ alphaSTokenRequest
  ∷ []

record NumericAuthorityTokenResponse : Set₁ where
  field
    responseLabel : String
    request : NumericAuthorityTokenRequest
    intakeState : TokenIntakeState
    responsePayloadClass : TokenPayloadClass
    rawTokenReference : String
    tokenStatusReason : String
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    numericValueLoaded : Bool
    numericValueLoadedIsFalse : numericValueLoaded ≡ false
    numericValuePromoted : Bool
    numericValuePromotedIsFalse : numericValuePromoted ≡ false
    noFabricatedNumericValue : Bool
    noFabricatedNumericValueIsTrue :
      noFabricatedNumericValue ≡ true

open NumericAuthorityTokenResponse public

missingTokenResponse :
  NumericAuthorityTokenRequest →
  String →
  TokenPayloadClass →
  NumericAuthorityTokenResponse
missingTokenResponse request label payload =
  record
    { responseLabel = label
    ; request = request
    ; intakeState = tokenMissing
    ; responsePayloadClass = payload
    ; rawTokenReference = "none"
    ; tokenStatusReason =
        "authority token absent; numeric value not loaded"
    ; acceptedAuthorityTokenPresent =
        Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresent
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; acceptedAuthorityTokenPresentIsFalse =
        Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresentIsFalse
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; numericValueLoaded = false
    ; numericValueLoadedIsFalse = refl
    ; numericValuePromoted =
        Registry.AuthorityConsumptionPolicyReceipt.numericValuePromoted
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; numericValuePromotedIsFalse =
        Registry.AuthorityConsumptionPolicyReceipt.numericValuePromotedIsFalse
          Registry.canonicalAuthorityConsumptionPolicyReceipt
    ; noFabricatedNumericValue = true
    ; noFabricatedNumericValueIsTrue = refl
    }

gMissingTokenResponse : NumericAuthorityTokenResponse
gMissingTokenResponse =
  missingTokenResponse
    gTokenRequest
    "missing CODATA authority token for G"
    codataMeasuredConstantPayload

alphaMissingTokenResponse : NumericAuthorityTokenResponse
alphaMissingTokenResponse =
  missingTokenResponse
    alphaTokenRequest
    "missing CODATA authority token for alpha"
    codataMeasuredConstantPayload

electronMassMissingTokenResponse : NumericAuthorityTokenResponse
electronMassMissingTokenResponse =
  missingTokenResponse
    electronMassTokenRequest
    "missing CODATA authority token for m_e"
    codataMeasuredConstantPayload

protonMassMissingTokenResponse : NumericAuthorityTokenResponse
protonMassMissingTokenResponse =
  missingTokenResponse
    protonMassTokenRequest
    "missing CODATA authority token for m_p"
    codataMeasuredConstantPayload

epsilonZeroMissingTokenResponse : NumericAuthorityTokenResponse
epsilonZeroMissingTokenResponse =
  missingTokenResponse
    epsilonZeroTokenRequest
    "missing CODATA authority token for epsilon_0"
    codataMeasuredConstantPayload

muZeroMissingTokenResponse : NumericAuthorityTokenResponse
muZeroMissingTokenResponse =
  missingTokenResponse
    muZeroTokenRequest
    "missing CODATA authority token for mu_0"
    codataMeasuredConstantPayload

rydbergMissingTokenResponse : NumericAuthorityTokenResponse
rydbergMissingTokenResponse =
  missingTokenResponse
    rydbergTokenRequest
    "missing CODATA authority token for R_infinity"
    codataMeasuredConstantPayload

higgsMassMissingTokenResponse : NumericAuthorityTokenResponse
higgsMassMissingTokenResponse =
  missingTokenResponse
    higgsMassTokenRequest
    "missing PDG authority token for m_H"
    pdgMeasuredConstantPayload

alphaSMissingTokenResponse : NumericAuthorityTokenResponse
alphaSMissingTokenResponse =
  missingTokenResponse
    alphaSTokenRequest
    "missing PDG authority token for alpha_s"
    pdgMeasuredConstantPayload

canonicalMissingTokenResponses :
  List NumericAuthorityTokenResponse
canonicalMissingTokenResponses =
  gMissingTokenResponse
  ∷ alphaMissingTokenResponse
  ∷ electronMassMissingTokenResponse
  ∷ protonMassMissingTokenResponse
  ∷ epsilonZeroMissingTokenResponse
  ∷ muZeroMissingTokenResponse
  ∷ rydbergMissingTokenResponse
  ∷ higgsMassMissingTokenResponse
  ∷ alphaSMissingTokenResponse
  ∷ []

canonicalMalformedTokenResponses :
  List NumericAuthorityTokenResponse
canonicalMalformedTokenResponses = []

canonicalAcceptedButNotLoadedTokenResponses :
  List NumericAuthorityTokenResponse
canonicalAcceptedButNotLoadedTokenResponses = []

canonicalAcceptedAndLoadedTokenResponses :
  List NumericAuthorityTokenResponse
canonicalAcceptedAndLoadedTokenResponses = []

canonicalAcceptedTokenResponses :
  List NumericAuthorityTokenResponse
canonicalAcceptedTokenResponses =
  canonicalAcceptedButNotLoadedTokenResponses

canonicalTokenIntakeStates : List TokenIntakeState
canonicalTokenIntakeStates =
  tokenMissing
  ∷ tokenMalformed
  ∷ tokenAcceptedButValueNotLoaded
  ∷ tokenAcceptedAndValueLoaded
  ∷ []

listCount : ∀ {a : Level} {A : Set a} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

record NumericAuthorityTokenIntakeReceipt : Set₁ where
  field
    receiptLabel : String
    sourceRegistry : Registry.ConstantsRegistry
    sourceAuthorityPolicy :
      Registry.AuthorityConsumptionPolicyReceipt
    sourceBindingReceipt :
      Binding.NumericMeasuredAuthorityBindingReceipt
    sourceObligationIndex :
      Numeric.NumericAndAuthorityObligationIndex
    tokenStatesRepresented : List TokenIntakeState
    tokenRequests : List NumericAuthorityTokenRequest
    codataTokenRequests : List NumericAuthorityTokenRequest
    pdgTokenRequests : List NumericAuthorityTokenRequest
    missingTokenResponses : List NumericAuthorityTokenResponse
    malformedTokenResponses : List NumericAuthorityTokenResponse
    acceptedButNotLoadedTokenResponses :
      List NumericAuthorityTokenResponse
    acceptedAndLoadedTokenResponses :
      List NumericAuthorityTokenResponse
    acceptedTokenResponses : List NumericAuthorityTokenResponse
    requestedTokenCount : Nat
    requestedTokenCountIs9 : requestedTokenCount ≡ 9
    codataRequestedTokenCount : Nat
    codataRequestedTokenCountIs7 : codataRequestedTokenCount ≡ 7
    pdgRequestedTokenCount : Nat
    pdgRequestedTokenCountIs2 : pdgRequestedTokenCount ≡ 2
    missingTokenCount : Nat
    missingTokenCountIs9 : missingTokenCount ≡ 9
    malformedTokenCount : Nat
    malformedTokenCountIs0 : malformedTokenCount ≡ 0
    acceptedButNotLoadedTokenCount : Nat
    acceptedButNotLoadedTokenCountIs0 :
      acceptedButNotLoadedTokenCount ≡ 0
    acceptedAndLoadedTokenCount : Nat
    acceptedAndLoadedTokenCountIs0 :
      acceptedAndLoadedTokenCount ≡ 0
    acceptedTokenCount : Nat
    acceptedTokenCountIs0 : acceptedTokenCount ≡ 0
    loadedTokenCount : Nat
    loadedTokenCountIs0 : loadedTokenCount ≡ 0
    allRequestedSlotsHaveMissingResponses : Bool
    allRequestedSlotsHaveMissingResponsesIsTrue :
      allRequestedSlotsHaveMissingResponses ≡ true
    noNumericValuesFabricated : Bool
    noNumericValuesFabricatedIsTrue :
      noNumericValuesFabricated ≡ true
    acceptedAuthorityTokenPresent : Bool
    acceptedAuthorityTokenPresentIsFalse :
      acceptedAuthorityTokenPresent ≡ false
    bindingReceiptAcceptedAuthorityTokenPresent : Bool
    bindingReceiptAcceptedAuthorityTokenPresentIsFalse :
      bindingReceiptAcceptedAuthorityTokenPresent ≡ false
    numericValuePromoted : Bool
    numericValuePromotedIsFalse :
      numericValuePromoted ≡ false
    bindingReceiptNumericValuePromoted : Bool
    bindingReceiptNumericValuePromotedIsFalse :
      bindingReceiptNumericValuePromoted ≡ false
    obligationIndexNumericValuePromoted : Bool
    obligationIndexNumericValuePromotedIsFalse :
      obligationIndexNumericValuePromoted ≡ false

open NumericAuthorityTokenIntakeReceipt public

canonicalNumericAuthorityTokenIntakeReceipt :
  NumericAuthorityTokenIntakeReceipt
canonicalNumericAuthorityTokenIntakeReceipt = record
  { receiptLabel =
      "numeric measured constant authority token intake surface"
  ; sourceRegistry =
      Registry.repoWideConstantsRegistry
  ; sourceAuthorityPolicy =
      Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; sourceBindingReceipt =
      Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; sourceObligationIndex =
      Numeric.canonicalNumericAndAuthorityObligationIndex
  ; tokenStatesRepresented =
      canonicalTokenIntakeStates
  ; tokenRequests =
      canonicalTokenRequests
  ; codataTokenRequests =
      canonicalCODATATokenRequests
  ; pdgTokenRequests =
      canonicalPDGTokenRequests
  ; missingTokenResponses =
      canonicalMissingTokenResponses
  ; malformedTokenResponses =
      canonicalMalformedTokenResponses
  ; acceptedButNotLoadedTokenResponses =
      canonicalAcceptedButNotLoadedTokenResponses
  ; acceptedAndLoadedTokenResponses =
      canonicalAcceptedAndLoadedTokenResponses
  ; acceptedTokenResponses =
      canonicalAcceptedTokenResponses
  ; requestedTokenCount =
      listCount canonicalTokenRequests
  ; requestedTokenCountIs9 = refl
  ; codataRequestedTokenCount =
      listCount canonicalCODATATokenRequests
  ; codataRequestedTokenCountIs7 = refl
  ; pdgRequestedTokenCount =
      listCount canonicalPDGTokenRequests
  ; pdgRequestedTokenCountIs2 = refl
  ; missingTokenCount =
      listCount canonicalMissingTokenResponses
  ; missingTokenCountIs9 = refl
  ; malformedTokenCount =
      listCount canonicalMalformedTokenResponses
  ; malformedTokenCountIs0 = refl
  ; acceptedButNotLoadedTokenCount =
      listCount canonicalAcceptedButNotLoadedTokenResponses
  ; acceptedButNotLoadedTokenCountIs0 = refl
  ; acceptedAndLoadedTokenCount =
      listCount canonicalAcceptedAndLoadedTokenResponses
  ; acceptedAndLoadedTokenCountIs0 = refl
  ; acceptedTokenCount =
      listCount canonicalAcceptedTokenResponses
  ; acceptedTokenCountIs0 = refl
  ; loadedTokenCount =
      listCount canonicalAcceptedAndLoadedTokenResponses
  ; loadedTokenCountIs0 = refl
  ; allRequestedSlotsHaveMissingResponses =
      true
  ; allRequestedSlotsHaveMissingResponsesIsTrue =
      refl
  ; noNumericValuesFabricated =
      true
  ; noNumericValuesFabricatedIsTrue =
      refl
  ; acceptedAuthorityTokenPresent =
      Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresent
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; acceptedAuthorityTokenPresentIsFalse =
      Registry.AuthorityConsumptionPolicyReceipt.acceptedAuthorityTokenPresentIsFalse
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; bindingReceiptAcceptedAuthorityTokenPresent =
      Binding.NumericMeasuredAuthorityBindingReceipt.acceptedAuthorityTokenPresent
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; bindingReceiptAcceptedAuthorityTokenPresentIsFalse =
      Binding.NumericMeasuredAuthorityBindingReceipt.acceptedAuthorityTokenPresentIsFalse
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; numericValuePromoted =
      Registry.AuthorityConsumptionPolicyReceipt.numericValuePromoted
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; numericValuePromotedIsFalse =
      Registry.AuthorityConsumptionPolicyReceipt.numericValuePromotedIsFalse
        Registry.canonicalAuthorityConsumptionPolicyReceipt
  ; bindingReceiptNumericValuePromoted =
      Binding.NumericMeasuredAuthorityBindingReceipt.numericValuePromoted
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; bindingReceiptNumericValuePromotedIsFalse =
      Binding.NumericMeasuredAuthorityBindingReceipt.numericValuePromotedIsFalse
        Binding.canonicalNumericMeasuredAuthorityBindingReceipt
  ; obligationIndexNumericValuePromoted =
      Numeric.NumericAndAuthorityObligationIndex.numericValuePromoted
        Numeric.canonicalNumericAndAuthorityObligationIndex
  ; obligationIndexNumericValuePromotedIsFalse =
      Numeric.NumericAndAuthorityObligationIndex.numericValuePromotedIsFalse
        Numeric.canonicalNumericAndAuthorityObligationIndex
  }

canonicalRequestedTokenCountIs9 :
  NumericAuthorityTokenIntakeReceipt.requestedTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 9
canonicalRequestedTokenCountIs9 = refl

canonicalCODATARequestedTokenCountIs7 :
  NumericAuthorityTokenIntakeReceipt.codataRequestedTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 7
canonicalCODATARequestedTokenCountIs7 = refl

canonicalPDGRequestedTokenCountIs2 :
  NumericAuthorityTokenIntakeReceipt.pdgRequestedTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 2
canonicalPDGRequestedTokenCountIs2 = refl

canonicalMissingTokenCountIs9 :
  NumericAuthorityTokenIntakeReceipt.missingTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 9
canonicalMissingTokenCountIs9 = refl

canonicalMalformedTokenCountIs0 :
  NumericAuthorityTokenIntakeReceipt.malformedTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 0
canonicalMalformedTokenCountIs0 = refl

canonicalAcceptedButNotLoadedTokenCountIs0 :
  NumericAuthorityTokenIntakeReceipt.acceptedButNotLoadedTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 0
canonicalAcceptedButNotLoadedTokenCountIs0 = refl

canonicalAcceptedAndLoadedTokenCountIs0 :
  NumericAuthorityTokenIntakeReceipt.acceptedAndLoadedTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 0
canonicalAcceptedAndLoadedTokenCountIs0 = refl

canonicalAcceptedTokenCountIs0 :
  NumericAuthorityTokenIntakeReceipt.acceptedTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 0
canonicalAcceptedTokenCountIs0 = refl

canonicalLoadedTokenCountIs0 :
  NumericAuthorityTokenIntakeReceipt.loadedTokenCount
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ 0
canonicalLoadedTokenCountIs0 = refl

canonicalNumericAuthorityTokenIntakeNumericValuePromotedIsFalse :
  NumericAuthorityTokenIntakeReceipt.numericValuePromoted
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ false
canonicalNumericAuthorityTokenIntakeNumericValuePromotedIsFalse = refl

canonicalNumericAuthorityTokenIntakeBindingNumericValuePromotedIsFalse :
  NumericAuthorityTokenIntakeReceipt.bindingReceiptNumericValuePromoted
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ false
canonicalNumericAuthorityTokenIntakeBindingNumericValuePromotedIsFalse =
  refl

canonicalNumericAuthorityTokenIntakeObligationNumericValuePromotedIsFalse :
  NumericAuthorityTokenIntakeReceipt.obligationIndexNumericValuePromoted
    canonicalNumericAuthorityTokenIntakeReceipt
  ≡ false
canonicalNumericAuthorityTokenIntakeObligationNumericValuePromotedIsFalse =
  refl

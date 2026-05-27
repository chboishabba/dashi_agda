module DASHI.Physics.Closure.PenguinDecaySMBaselineAuthority where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PenguinDecayObservableContract as Contract
import DASHI.Physics.Closure.PenguinDecayProjectionDefectReceipt as Penguin

------------------------------------------------------------------------
-- Standard-Model baseline authority request for b -> s mu+ mu-.
--
-- This module is a concrete diagnostic and request surface only.  It consumes
-- the local penguin projection-defect receipt and records the exact external
-- Standard-Model baseline authorities required before any empirical comparison
-- of b -> s mu+ mu- can be interpreted.  No accepted token, comparison result,
-- anomaly claim, or promotion path is constructed here.

data SMBaselineAuthorityStatus : Set where
  blockedAwaitingAcceptedSMBaselineAuthority :
    SMBaselineAuthorityStatus

data SMBaselineObservableContractImport : Set where
  physicsObservableContractImported :
    SMBaselineObservableContractImport

data TargetLeptonPair : Set where
  muPlusMuMinus :
    TargetLeptonPair

data SMBaselineComparisonTarget : Set where
  bToSMuPlusMuMinus :
    SMBaselineComparisonTarget

targetDecay :
  SMBaselineComparisonTarget →
  Penguin.RarePenguinDecay
targetDecay bToSMuPlusMuMinus =
  Penguin.bToSLeptonPair

targetLeptonPair :
  SMBaselineComparisonTarget →
  TargetLeptonPair
targetLeptonPair bToSMuPlusMuMinus =
  muPlusMuMinus

data SMBaselineAuthorityField : Set where
  wilsonCoefficientAuthorityField :
    SMBaselineAuthorityField
  baselineSourceAuthority :
    SMBaselineAuthorityField
  theoryUncertaintyAuthority :
    SMBaselineAuthorityField
  charmingPenguinAuthority :
    SMBaselineAuthorityField
  systematicsAuthority :
    SMBaselineAuthorityField

canonicalSMBaselineAuthorityFields :
  List SMBaselineAuthorityField
canonicalSMBaselineAuthorityFields =
  wilsonCoefficientAuthorityField
  ∷ baselineSourceAuthority
  ∷ theoryUncertaintyAuthority
  ∷ charmingPenguinAuthority
  ∷ systematicsAuthority
  ∷ []

data SMBaselineMissingAuthority : Set where
  missingAcceptedWilsonCoefficientSet :
    SMBaselineMissingAuthority
  missingAcceptedBaselineSource :
    SMBaselineMissingAuthority
  missingAcceptedTheoryUncertaintyBudget :
    SMBaselineMissingAuthority
  missingAcceptedCharmingPenguinTreatment :
    SMBaselineMissingAuthority
  missingAcceptedExperimentalSystematicsMap :
    SMBaselineMissingAuthority
  missingObservableContractBinding :
    SMBaselineMissingAuthority
  missingNoManualFitAttestation :
    SMBaselineMissingAuthority

canonicalSMBaselineMissingAuthorities :
  List SMBaselineMissingAuthority
canonicalSMBaselineMissingAuthorities =
  missingAcceptedWilsonCoefficientSet
  ∷ missingAcceptedBaselineSource
  ∷ missingAcceptedTheoryUncertaintyBudget
  ∷ missingAcceptedCharmingPenguinTreatment
  ∷ missingAcceptedExperimentalSystematicsMap
  ∷ missingObservableContractBinding
  ∷ missingNoManualFitAttestation
  ∷ []

data SMBaselineProviderPayloadField : Set where
  providerName :
    SMBaselineProviderPayloadField
  providerRole :
    SMBaselineProviderPayloadField
  targetProcess :
    SMBaselineProviderPayloadField
  wilsonCoefficientScheme :
    SMBaselineProviderPayloadField
  wilsonCoefficientValues :
    SMBaselineProviderPayloadField
  renormalizationScaleLaw :
    SMBaselineProviderPayloadField
  effectiveHamiltonianConvention :
    SMBaselineProviderPayloadField
  baselineSourceCitation :
    SMBaselineProviderPayloadField
  formFactorSource :
    SMBaselineProviderPayloadField
  theoryUncertaintyBudget :
    SMBaselineProviderPayloadField
  charmingPenguinModel :
    SMBaselineProviderPayloadField
  experimentalSystematicsMap :
    SMBaselineProviderPayloadField
  covarianceAndBinMap :
    SMBaselineProviderPayloadField
  observableContractBinding :
    SMBaselineProviderPayloadField
  noManualFitAttestation :
    SMBaselineProviderPayloadField
  responseStatus :
    SMBaselineProviderPayloadField

canonicalSMBaselineProviderPayloadFields :
  List SMBaselineProviderPayloadField
canonicalSMBaselineProviderPayloadFields =
  providerName
  ∷ providerRole
  ∷ targetProcess
  ∷ wilsonCoefficientScheme
  ∷ wilsonCoefficientValues
  ∷ renormalizationScaleLaw
  ∷ effectiveHamiltonianConvention
  ∷ baselineSourceCitation
  ∷ formFactorSource
  ∷ theoryUncertaintyBudget
  ∷ charmingPenguinModel
  ∷ experimentalSystematicsMap
  ∷ covarianceAndBinMap
  ∷ observableContractBinding
  ∷ noManualFitAttestation
  ∷ responseStatus
  ∷ []

data SMBaselineAcceptedAuthorityToken : Set where

smBaselineAcceptedAuthorityTokenImpossibleHere :
  SMBaselineAcceptedAuthorityToken →
  ⊥
smBaselineAcceptedAuthorityTokenImpossibleHere ()

record SMBaselineAuthorityRequestDiagnostic : Set where
  field
    status :
      SMBaselineAuthorityStatus

    penguinReceipt :
      Penguin.PenguinDecayProjectionDefectReceipt

    penguinReceiptIsCanonical :
      penguinReceipt
      ≡
      Penguin.canonicalPenguinDecayProjectionDefectReceipt

    observableContractImport :
      SMBaselineObservableContractImport

    observableContract :
      Contract.PenguinDecayObservableContract

    observableContractIsCanonical :
      observableContract
      ≡
      Contract.canonicalPenguinDecayObservableContract

    wilsonProviderNameText :
      String

    wilsonProviderNameTextIsFlavio :
      wilsonProviderNameText ≡ "flavio"

    wilsonProviderVersionText :
      String

    wilsonProviderVersionTextIsCanonical :
      wilsonProviderVersionText ≡ "2.7.0"

    wilsonAuthorityDigestSlot :
      String

    wilsonAuthorityDigestSlotIsRequired :
      wilsonAuthorityDigestSlot
      ≡
      "required: provider-supplied Wilson coefficient authority digest"

    wilsonAuthorityNamesFlavio :
      wilsonProviderNameText
      ≡
      "flavio"

    wilsonAuthorityAcceptedTokenConstructedHere :
      Bool

    wilsonAuthorityStillFailClosed :
      wilsonAuthorityAcceptedTokenConstructedHere
      ≡
      false

    comparisonTarget :
      SMBaselineComparisonTarget

    comparisonTargetIsBToSMuMu :
      comparisonTarget
      ≡
      bToSMuPlusMuMinus

    decay :
      Penguin.RarePenguinDecay

    decayIsBToSLeptonPair :
      decay
      ≡
      Penguin.bToSLeptonPair

    leptonPair :
      TargetLeptonPair

    leptonPairIsMuPlusMuMinus :
      leptonPair
      ≡
      muPlusMuMinus

    smTransport :
      List Penguin.TransportRoute

    smTransportIsLoopOnly :
      smTransport
      ≡
      (Penguin.penguinLoopRoute ∷ Penguin.boxLoopRoute ∷ [])

    requiredAuthorityFields :
      List SMBaselineAuthorityField

    requiredAuthorityFieldsAreCanonical :
      requiredAuthorityFields
      ≡
      canonicalSMBaselineAuthorityFields

    missingAuthorities :
      List SMBaselineMissingAuthority

    missingAuthoritiesAreCanonical :
      missingAuthorities
      ≡
      canonicalSMBaselineMissingAuthorities

    providerPayloadFields :
      List SMBaselineProviderPayloadField

    providerPayloadFieldsAreCanonical :
      providerPayloadFields
      ≡
      canonicalSMBaselineProviderPayloadFields

    providerPayloadFieldLabels :
      List String

    requestSummary :
      List String

    acceptedAuthorityTokenConstructible :
      Bool

    acceptedAuthorityTokenConstructibleIsFalse :
      acceptedAuthorityTokenConstructible
      ≡
      false

    empiricalComparisonConstructible :
      Bool

    empiricalComparisonConstructibleIsFalse :
      empiricalComparisonConstructible
      ≡
      false

    promotionConstructed :
      Bool

    promotionConstructedIsFalse :
      promotionConstructed
      ≡
      false

    acceptedAuthorityTokenImpossible :
      SMBaselineAcceptedAuthorityToken →
      ⊥

open SMBaselineAuthorityRequestDiagnostic public

canonicalSMBaselineAuthorityRequestDiagnostic :
  SMBaselineAuthorityRequestDiagnostic
canonicalSMBaselineAuthorityRequestDiagnostic =
  record
    { status =
        blockedAwaitingAcceptedSMBaselineAuthority
    ; penguinReceipt =
        Penguin.canonicalPenguinDecayProjectionDefectReceipt
    ; penguinReceiptIsCanonical =
        refl
    ; observableContractImport =
        physicsObservableContractImported
    ; observableContract =
        Contract.canonicalPenguinDecayObservableContract
    ; observableContractIsCanonical =
        refl
    ; wilsonProviderNameText =
        "flavio"
    ; wilsonProviderNameTextIsFlavio =
        refl
    ; wilsonProviderVersionText =
        "2.7.0"
    ; wilsonProviderVersionTextIsCanonical =
        refl
    ; wilsonAuthorityDigestSlot =
        "required: provider-supplied Wilson coefficient authority digest"
    ; wilsonAuthorityDigestSlotIsRequired =
        refl
    ; wilsonAuthorityNamesFlavio =
        refl
    ; wilsonAuthorityAcceptedTokenConstructedHere =
        false
    ; wilsonAuthorityStillFailClosed =
        refl
    ; comparisonTarget =
        bToSMuPlusMuMinus
    ; comparisonTargetIsBToSMuMu =
        refl
    ; decay =
        Penguin.bToSLeptonPair
    ; decayIsBToSLeptonPair =
        refl
    ; leptonPair =
        muPlusMuMinus
    ; leptonPairIsMuPlusMuMinus =
        refl
    ; smTransport =
        Penguin.acceptedSMTransport Penguin.bToSLeptonPair
    ; smTransportIsLoopOnly =
        refl
    ; requiredAuthorityFields =
        canonicalSMBaselineAuthorityFields
    ; requiredAuthorityFieldsAreCanonical =
        refl
    ; missingAuthorities =
        canonicalSMBaselineMissingAuthorities
    ; missingAuthoritiesAreCanonical =
        refl
    ; providerPayloadFields =
        canonicalSMBaselineProviderPayloadFields
    ; providerPayloadFieldsAreCanonical =
        refl
    ; providerPayloadFieldLabels =
        "provider_name"
        ∷ "provider_role"
        ∷ "target_process=b -> s mu+ mu-"
        ∷ "wilson_coefficient_scheme"
        ∷ "wilson_coefficient_values"
        ∷ "renormalization_scale_law"
        ∷ "effective_hamiltonian_convention"
        ∷ "baseline_source_citation"
        ∷ "form_factor_source"
        ∷ "theory_uncertainty_budget"
        ∷ "charming_penguin_model"
        ∷ "experimental_systematics_map"
        ∷ "covariance_and_bin_map"
        ∷ "observable_contract_binding"
        ∷ "no_manual_fit_attestation"
        ∷ "response_status accepted/rejected/insufficient"
        ∷ []
    ; requestSummary =
        "Before comparing DASHI residuals with b -> s mu+ mu-, provide an accepted Standard-Model baseline for the same observable contract and bin map"
        ∷ "Required authorities are Wilson coefficients, baseline source, theory uncertainty, charming-penguin treatment, and experimental systematics"
        ∷ "The local penguin receipt supplies only the loop-only projection-defect detector; it does not supply accepted empirical baseline authority"
        ∷ "This diagnostic is fail-closed: no accepted authority token, empirical comparison, anomaly claim, or promotion is constructed"
        ∷ []
    ; acceptedAuthorityTokenConstructible =
        false
    ; acceptedAuthorityTokenConstructibleIsFalse =
        refl
    ; empiricalComparisonConstructible =
        false
    ; empiricalComparisonConstructibleIsFalse =
        refl
    ; promotionConstructed =
        false
    ; promotionConstructedIsFalse =
        refl
    ; acceptedAuthorityTokenImpossible =
        smBaselineAcceptedAuthorityTokenImpossibleHere
    }

canonicalSMBaselineAuthorityRequestStillBlocked :
  SMBaselineAuthorityRequestDiagnostic.status
    canonicalSMBaselineAuthorityRequestDiagnostic
    ≡
  blockedAwaitingAcceptedSMBaselineAuthority
canonicalSMBaselineAuthorityRequestStillBlocked =
  refl

canonicalSMBaselineAuthorityRequestTarget :
  SMBaselineAuthorityRequestDiagnostic.decay
    canonicalSMBaselineAuthorityRequestDiagnostic
    ≡
  Penguin.bToSLeptonPair
canonicalSMBaselineAuthorityRequestTarget =
  refl

canonicalSMBaselineAuthorityRequestMissingList :
  SMBaselineAuthorityRequestDiagnostic.missingAuthorities
    canonicalSMBaselineAuthorityRequestDiagnostic
    ≡
  canonicalSMBaselineMissingAuthorities
canonicalSMBaselineAuthorityRequestMissingList =
  refl

canonicalSMBaselineAuthorityRequestNoComparison :
  SMBaselineAuthorityRequestDiagnostic.empiricalComparisonConstructible
    canonicalSMBaselineAuthorityRequestDiagnostic
    ≡
  false
canonicalSMBaselineAuthorityRequestNoComparison =
  refl

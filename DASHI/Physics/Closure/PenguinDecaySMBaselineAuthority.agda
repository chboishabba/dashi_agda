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
  bZeroToKStarMuPlusMuMinusP5Prime :
    SMBaselineComparisonTarget

targetDecay :
  SMBaselineComparisonTarget →
  Penguin.RarePenguinDecay
targetDecay bToSMuPlusMuMinus =
  Penguin.bToSLeptonPair
targetDecay bZeroToKStarMuPlusMuMinusP5Prime =
  Penguin.bToSLeptonPair

targetLeptonPair :
  SMBaselineComparisonTarget →
  TargetLeptonPair
targetLeptonPair bToSMuPlusMuMinus =
  muPlusMuMinus
targetLeptonPair bZeroToKStarMuPlusMuMinusP5Prime =
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

data P5PrimeSMBaselineAuthorityStatus : Set where
  p5PrimeFlavioBaselineBoundFailClosed :
    P5PrimeSMBaselineAuthorityStatus

data P5PrimeQ2Bin : Set where
  q2Bin4To6 :
    P5PrimeQ2Bin
  q2Bin6To8 :
    P5PrimeQ2Bin

canonicalP5PrimeQ2Bins :
  List P5PrimeQ2Bin
canonicalP5PrimeQ2Bins =
  q2Bin4To6
  ∷ q2Bin6To8
  ∷ []

data P5PrimeAuthorityBinding : Set where
  flavio270RuntimeAuthority :
    P5PrimeAuthorityBinding
  c9SMC10SMWilsonCoefficientAuthority :
    P5PrimeAuthorityBinding
  bsz2015FormFactorAuthority :
    P5PrimeAuthorityBinding
  perBinTheoryUncertaintyAuthority :
    P5PrimeAuthorityBinding
  qcdfNonlocalCharmEstimateAuthority :
    P5PrimeAuthorityBinding
  noPosteriorTuningAttestationAuthority :
    P5PrimeAuthorityBinding

canonicalP5PrimeAuthorityBindings :
  List P5PrimeAuthorityBinding
canonicalP5PrimeAuthorityBindings =
  flavio270RuntimeAuthority
  ∷ c9SMC10SMWilsonCoefficientAuthority
  ∷ bsz2015FormFactorAuthority
  ∷ perBinTheoryUncertaintyAuthority
  ∷ qcdfNonlocalCharmEstimateAuthority
  ∷ noPosteriorTuningAttestationAuthority
  ∷ []

data P5PrimeAuthorityIncompleteFlag : Set where
  noAcceptedC9C10AuthorityToken :
    P5PrimeAuthorityIncompleteFlag
  noIndependentEOSCrossCheckBound :
    P5PrimeAuthorityIncompleteFlag
  qcdfAboveSixGeVSquaredWarning :
    P5PrimeAuthorityIncompleteFlag
  noAcceptedP5PrimeResidualVector :
    P5PrimeAuthorityIncompleteFlag
  noAcceptedP5PrimeCovarianceMatrix :
    P5PrimeAuthorityIncompleteFlag

canonicalP5PrimeAuthorityIncompleteFlags :
  List P5PrimeAuthorityIncompleteFlag
canonicalP5PrimeAuthorityIncompleteFlags =
  noAcceptedC9C10AuthorityToken
  ∷ noIndependentEOSCrossCheckBound
  ∷ qcdfAboveSixGeVSquaredWarning
  ∷ noAcceptedP5PrimeResidualVector
  ∷ noAcceptedP5PrimeCovarianceMatrix
  ∷ []

record P5PrimeBinTheoryAuthority : Set where
  constructor mkP5PrimeBinTheoryAuthority
  field
    q2Bin :
      P5PrimeQ2Bin

    q2RangeGeVSquared :
      String

    flavioObservableKey :
      String

    centralValue :
      String

    oneSigmaTheoryUncertainty :
      String

    uncertaintySource :
      String

open P5PrimeBinTheoryAuthority public

p5Prime4To6TheoryAuthority :
  P5PrimeBinTheoryAuthority
p5Prime4To6TheoryAuthority =
  mkP5PrimeBinTheoryAuthority
    q2Bin4To6
    "[4,6] GeV^2"
    "<P5p>(B0->K*mumu)"
    "-0.7583138786902011"
    "0.07524646089051247"
    "flavio.sm_uncertainty('<P5p>(B0->K*mumu)', 4, 6)"

p5Prime6To8TheoryAuthority :
  P5PrimeBinTheoryAuthority
p5Prime6To8TheoryAuthority =
  mkP5PrimeBinTheoryAuthority
    q2Bin6To8
    "[6,8] GeV^2"
    "<P5p>(B0->K*mumu)"
    "-0.8342430145843444"
    "0.06092804199708315"
    "flavio.sm_uncertainty('<P5p>(B0->K*mumu)', 6, 8)"

canonicalP5PrimeBinTheoryAuthorities :
  List P5PrimeBinTheoryAuthority
canonicalP5PrimeBinTheoryAuthorities =
  p5Prime4To6TheoryAuthority
  ∷ p5Prime6To8TheoryAuthority
  ∷ []

record P5PrimeSMBaselineAuthorityChain : Set where
  field
    p5PrimeBaselineStatus :
      P5PrimeSMBaselineAuthorityStatus

    p5PrimeBaselineTarget :
      SMBaselineComparisonTarget

    targetIsP5Prime :
      p5PrimeBaselineTarget ≡ bZeroToKStarMuPlusMuMinusP5Prime

    p5PrimeTargetProcessText :
      String

    p5PrimeTargetProcessTextIsCanonical :
      p5PrimeTargetProcessText ≡ "B0 -> K*0 mu+ mu- P5'"

    p5PrimeFlavioProviderName :
      String

    p5PrimeFlavioProviderNameIsCanonical :
      p5PrimeFlavioProviderName ≡ "flavio"

    flavioProviderVersion :
      String

    flavioProviderVersionIsCanonical :
      flavioProviderVersion ≡ "2.7.0"

    flavioWheelSHA256 :
      String

    flavioWheelSHA256IsCanonical :
      flavioWheelSHA256
      ≡
      "3d5aaeb5a9df7c479949e4641ccbd2dc662cb010aabf9dda5f725a8a80813b4f"

    flavioSdistSHA256 :
      String

    flavioSdistSHA256IsCanonical :
      flavioSdistSHA256
      ≡
      "08c9c9608ae2ee76d4097b5836e7ca2479f59f9478d0fdddb2cf01b7da4e796e"

    wilsonPackageVersion :
      String

    wilsonPackageVersionIsCanonical :
      wilsonPackageVersion ≡ "2.5.2"

    wilsonPackageWheelSHA256 :
      String

    wilsonPackageWheelSHA256IsCanonical :
      wilsonPackageWheelSHA256
      ≡
      "959e3dbd6bfefb43b3769fe07e2d8e59c153abe6796851fb91c4d18b7981799a"

    c9SMKey :
      String

    c9SMKeyIsCanonical :
      c9SMKey ≡ "C9_bsll"

    c10SMKey :
      String

    c10SMKeyIsCanonical :
      c10SMKey ≡ "C10_bsll"

    p5PrimeFormFactorSourceText :
      String

    p5PrimeFormFactorSourceTextIsBSZ :
      p5PrimeFormFactorSourceText
      ≡
      "Bharucha-Straub-Zwicky B -> V l+l- LCSR form factors"

    formFactorDOI :
      String

    formFactorDOIIsBSZ :
      formFactorDOI ≡ "10.1007/JHEP08(2016)098"

    formFactorArXiv :
      String

    formFactorArXivIsCanonical :
      formFactorArXiv ≡ "arXiv:1503.05534"

    q2Bins :
      List P5PrimeQ2Bin

    q2BinsAreCanonical :
      q2Bins ≡ canonicalP5PrimeQ2Bins

    binTheoryAuthorities :
      List P5PrimeBinTheoryAuthority

    binTheoryAuthoritiesAreCanonical :
      binTheoryAuthorities ≡ canonicalP5PrimeBinTheoryAuthorities

    p5PrimeCharmingPenguinEstimate :
      String

    p5PrimeCharmingPenguinEstimateIsCanonical :
      p5PrimeCharmingPenguinEstimate
      ≡
      "flavio bvll QCDF/nonlocal-charm interpolation; qcdf_interpolate.py sha256 df2748de08a59a55f6584bf128b65c3a8ce62dcfa0baffc81b1e4c94997304f6; runtime warns QCDF corrections should not be trusted for q2 above 6 GeV^2"

    authorityBindings :
      List P5PrimeAuthorityBinding

    authorityBindingsAreCanonical :
      authorityBindings ≡ canonicalP5PrimeAuthorityBindings

    incompleteFlags :
      List P5PrimeAuthorityIncompleteFlag

    incompleteFlagsAreCanonical :
      incompleteFlags ≡ canonicalP5PrimeAuthorityIncompleteFlags

    separatedFromBsToMuMuBaseline :
      Bool

    separatedFromBsToMuMuBaselineIsTrue :
      separatedFromBsToMuMuBaseline ≡ true

    p5PrimeAcceptedAuthorityTokenConstructedHere :
      Bool

    p5PrimeAcceptedAuthorityTokenConstructedHereIsFalse :
      p5PrimeAcceptedAuthorityTokenConstructedHere ≡ false

open P5PrimeSMBaselineAuthorityChain public

canonicalP5PrimeSMBaselineAuthorityChain :
  P5PrimeSMBaselineAuthorityChain
canonicalP5PrimeSMBaselineAuthorityChain =
  record
    { p5PrimeBaselineStatus =
        p5PrimeFlavioBaselineBoundFailClosed
    ; p5PrimeBaselineTarget =
        bZeroToKStarMuPlusMuMinusP5Prime
    ; targetIsP5Prime =
        refl
    ; p5PrimeTargetProcessText =
        "B0 -> K*0 mu+ mu- P5'"
    ; p5PrimeTargetProcessTextIsCanonical =
        refl
    ; p5PrimeFlavioProviderName =
        "flavio"
    ; p5PrimeFlavioProviderNameIsCanonical =
        refl
    ; flavioProviderVersion =
        "2.7.0"
    ; flavioProviderVersionIsCanonical =
        refl
    ; flavioWheelSHA256 =
        "3d5aaeb5a9df7c479949e4641ccbd2dc662cb010aabf9dda5f725a8a80813b4f"
    ; flavioWheelSHA256IsCanonical =
        refl
    ; flavioSdistSHA256 =
        "08c9c9608ae2ee76d4097b5836e7ca2479f59f9478d0fdddb2cf01b7da4e796e"
    ; flavioSdistSHA256IsCanonical =
        refl
    ; wilsonPackageVersion =
        "2.5.2"
    ; wilsonPackageVersionIsCanonical =
        refl
    ; wilsonPackageWheelSHA256 =
        "959e3dbd6bfefb43b3769fe07e2d8e59c153abe6796851fb91c4d18b7981799a"
    ; wilsonPackageWheelSHA256IsCanonical =
        refl
    ; c9SMKey =
        "C9_bsll"
    ; c9SMKeyIsCanonical =
        refl
    ; c10SMKey =
        "C10_bsll"
    ; c10SMKeyIsCanonical =
        refl
    ; p5PrimeFormFactorSourceText =
        "Bharucha-Straub-Zwicky B -> V l+l- LCSR form factors"
    ; p5PrimeFormFactorSourceTextIsBSZ =
        refl
    ; formFactorDOI =
        "10.1007/JHEP08(2016)098"
    ; formFactorDOIIsBSZ =
        refl
    ; formFactorArXiv =
        "arXiv:1503.05534"
    ; formFactorArXivIsCanonical =
        refl
    ; q2Bins =
        canonicalP5PrimeQ2Bins
    ; q2BinsAreCanonical =
        refl
    ; binTheoryAuthorities =
        canonicalP5PrimeBinTheoryAuthorities
    ; binTheoryAuthoritiesAreCanonical =
        refl
    ; p5PrimeCharmingPenguinEstimate =
        "flavio bvll QCDF/nonlocal-charm interpolation; qcdf_interpolate.py sha256 df2748de08a59a55f6584bf128b65c3a8ce62dcfa0baffc81b1e4c94997304f6; runtime warns QCDF corrections should not be trusted for q2 above 6 GeV^2"
    ; p5PrimeCharmingPenguinEstimateIsCanonical =
        refl
    ; authorityBindings =
        canonicalP5PrimeAuthorityBindings
    ; authorityBindingsAreCanonical =
        refl
    ; incompleteFlags =
        canonicalP5PrimeAuthorityIncompleteFlags
    ; incompleteFlagsAreCanonical =
        refl
    ; separatedFromBsToMuMuBaseline =
        true
    ; separatedFromBsToMuMuBaselineIsTrue =
        refl
    ; p5PrimeAcceptedAuthorityTokenConstructedHere =
        false
    ; p5PrimeAcceptedAuthorityTokenConstructedHereIsFalse =
        refl
    }

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

    p5PrimeSMBaselineAuthorityChain :
      P5PrimeSMBaselineAuthorityChain

    p5PrimeSMBaselineAuthorityChainIsCanonical :
      p5PrimeSMBaselineAuthorityChain
      ≡
      canonicalP5PrimeSMBaselineAuthorityChain

    p5PrimeAcceptedAuthorityStillFailClosed :
      p5PrimeAcceptedAuthorityTokenConstructedHere
        p5PrimeSMBaselineAuthorityChain
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
    ; p5PrimeSMBaselineAuthorityChain =
        canonicalP5PrimeSMBaselineAuthorityChain
    ; p5PrimeSMBaselineAuthorityChainIsCanonical =
        refl
    ; p5PrimeAcceptedAuthorityStillFailClosed =
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

module DASHI.Physics.Closure.W4DiagonalConventionGateConsumer where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (_<_)

import DASHI.Physics.Closure.W4ResponseMatrixAcceptanceCandidateReceipt as Candidate
import DASHI.Physics.Closure.W4ExternalAuthorityTokenSurface as W4Authority

scaledDecimalStrictGT9566over9000 :
  9000 < 9566
scaledDecimalStrictGT9566over9000 =
  Candidate.scaledDecimalStrictGreaterThan9566over9000

------------------------------------------------------------------------
-- W4 diagonal-convention gate-consumer request.
--
-- The response-matrix diagnostic has enough local arithmetic to nominate a
-- concrete candidate for A(M,phi*):
--
--   A_diag[j] = P[j][j]
--
-- This module records that nomination and the exact fields still required
-- before any W4 gate may consume it.  It intentionally does not construct
-- W4ZAdequacy, an accepted DY convention authority, or a W4 promotion.

data W4DiagonalConventionGateConsumerStatus : Set where
  diagonalCandidateSelectedButConsumerMissing :
    W4DiagonalConventionGateConsumerStatus
  diagonalConventionQuarantinedAwaitingExternalAcceptance :
    W4DiagonalConventionGateConsumerStatus
  diagonalCandidateRejectedNoCentralEfficiencyAcceptanceModel :
    W4DiagonalConventionGateConsumerStatus

data W4DiagonalConventionGateConsumerFirstMissing : Set where
  missingExternalDiagonalConventionGateConsumer :
    W4DiagonalConventionGateConsumerFirstMissing
  missingW4ZAdequacyConsumer :
    W4DiagonalConventionGateConsumerFirstMissing
  missingSourceCentralEfficiencyAcceptanceModel :
    W4DiagonalConventionGateConsumerFirstMissing

data W4DiagonalConventionRequiredField : Set where
  providerDiagonalAsAcceptanceConvention :
    W4DiagonalConventionRequiredField
  providerDiagonalAdmissibilityBounds :
    W4DiagonalConventionRequiredField
  acceptedElectronMuonChannelCombinationLaw :
    W4DiagonalConventionRequiredField
  acceptedCovariancePropagationLaw :
    W4DiagonalConventionRequiredField
  acceptedW4ZAdequacyConsumer :
    W4DiagonalConventionRequiredField
  acceptedGatePromotionBoundary :
    W4DiagonalConventionRequiredField

canonicalW4DiagonalConventionRequiredFields :
  List W4DiagonalConventionRequiredField
canonicalW4DiagonalConventionRequiredFields =
  providerDiagonalAsAcceptanceConvention
  ∷ providerDiagonalAdmissibilityBounds
  ∷ acceptedElectronMuonChannelCombinationLaw
  ∷ acceptedCovariancePropagationLaw
  ∷ acceptedW4ZAdequacyConsumer
  ∷ acceptedGatePromotionBoundary
  ∷ []

data W4DiagonalConventionChannelCombinationCandidate : Set where
  channelSeparatedDiagnosticOnly :
    W4DiagonalConventionChannelCombinationCandidate
  inverseCovarianceWeightedCombinationRequested :
    W4DiagonalConventionChannelCombinationCandidate
  blueElectronMuonCombinationRequested :
    W4DiagonalConventionChannelCombinationCandidate
  geometricMeanChannelCombinationQuarantined :
    W4DiagonalConventionChannelCombinationCandidate

data W4DiagonalConventionCovariancePropagationCandidate : Set where
  covariancePropagationRequested :
    W4DiagonalConventionCovariancePropagationCandidate
  linearizedDiagonalRatioCovarianceRequested :
    W4DiagonalConventionCovariancePropagationCandidate
  noAcceptedCovariancePropagationLaw :
    W4DiagonalConventionCovariancePropagationCandidate

data W4DiagonalConventionAdmissibilityStatus : Set where
  diagonalBoundsComputedAndAdmissibleButNotAccepted :
    W4DiagonalConventionAdmissibilityStatus
  diagonalBoundsComputedAndQuarantined :
    W4DiagonalConventionAdmissibilityStatus

data W4DiagonalConventionAuthorityStatus : Set where
  conventionQuarantinedW4ZAdequacyPending :
    W4DiagonalConventionAuthorityStatus
  internalAdequacyEvidenceComputedW4GatePending :
    W4DiagonalConventionAuthorityStatus
  sourceCentralEfficiencyAcceptanceModelMissing :
    W4DiagonalConventionAuthorityStatus

record W4DiagonalConventionGateConsumerRequest : Set where
  field
    status :
      W4DiagonalConventionGateConsumerStatus

    firstMissing :
      W4DiagonalConventionGateConsumerFirstMissing

    candidateReceipt :
      Candidate.W4ResponseMatrixAcceptanceCandidateReceipt

    diagnosticOutputSHA256 :
      String

    checksumManifest :
      String

    selectedCandidate :
      Candidate.W4ResponseMatrixAcceptanceCandidateChoice

    selectedCandidateIsDiagonal :
      selectedCandidate ≡ Candidate.diagonalCandidate

    authorityStatus :
      W4DiagonalConventionAuthorityStatus

    diagonalConventionFormula :
      String

    diagonalAdmissibilityStatus :
      W4DiagonalConventionAdmissibilityStatus

    diagonalAdmissibilityBoundText :
      String

    selectedW4DiagonalGlobalMin :
      String

    selectedW4DiagonalGlobalMax :
      String

    selectedW4DiagonalGlobalMean :
      String

    columnSumFalsificationBoundText :
      String

    selectedMassWindows :
      List String

    electronDiagonalMean50to76 :
      String

    muonDiagonalMean50to76 :
      String

    electronDiagonalMean76to106 :
      String

    muonDiagonalMean76to106 :
      String

    electronDiagonalMean106to170 :
      String

    muonDiagonalMean106to170 :
      String

    channelCombinationCandidate :
      W4DiagonalConventionChannelCombinationCandidate

    channelCombinationFormula :
      String

    channelCombinationLawText :
      String

    channelCombinationInputs :
      List String

    channelCombinationOutputContract :
      String

    covariancePropagationCandidate :
      W4DiagonalConventionCovariancePropagationCandidate

    covariancePropagationFormula :
      String

    covariancePropagationLawText :
      String

    covariancePropagationInputs :
      List String

    covariancePropagationOutputContract :
      String

    internalAdequacyEvidenceReceipt :
      Candidate.W4ZInternalAdequacyEvidenceReceipt

    internalAdequacyMassWindow :
      String

    internalAdequacyCombinedEfficiency :
      String

    internalAdequacyBound :
      String

    internalAdequacyComputationText :
      String

    internalAdequacyFirstMissing :
      Candidate.W4ZInternalAdequacyEvidenceFirstMissing

    externalAuthorityFirstMissingBeforeHookRequest :
      W4Authority.W4ExternalAuthorityMissingField

    externalAuthorityFirstMissingAfterHookRequest :
      W4Authority.W4ExternalAuthorityMissingField

    externalAuthorityFirstMissingUnchanged :
      externalAuthorityFirstMissingAfterHookRequest
      ≡
      externalAuthorityFirstMissingBeforeHookRequest

    internalAdequacyStrictGreaterThanWitness :
      9000 < 9566

    internalAdequacyComputedPass :
      Bool

    internalAdequacyComputedPassIsFalse :
      internalAdequacyComputedPass ≡ false

    acceptedConsumerReceiptShape :
      List String

    requiredAcceptedConsumerFields :
      List W4DiagonalConventionRequiredField

    requiredAcceptedConsumerFieldsAreCanonical :
      requiredAcceptedConsumerFields
      ≡ canonicalW4DiagonalConventionRequiredFields

    diagonalAsAcceptanceConventionAccepted :
      Bool

    diagonalAsAcceptanceConventionAcceptedIsFalse :
      diagonalAsAcceptanceConventionAccepted ≡ false

    diagonalAdmissibilityBoundsAccepted :
      Bool

    diagonalAdmissibilityBoundsAcceptedIsFalse :
      diagonalAdmissibilityBoundsAccepted ≡ false

    electronMuonCombinationLawAccepted :
      Bool

    electronMuonCombinationLawAcceptedIsFalse :
      electronMuonCombinationLawAccepted ≡ false

    covariancePropagationLawAccepted :
      Bool

    covariancePropagationLawAcceptedIsFalse :
      covariancePropagationLawAccepted ≡ false

    constructsW4ZAdequacy :
      Bool

    constructsW4ZAdequacyIsFalse :
      constructsW4ZAdequacy ≡ false

    constructsAcceptedDYLuminosityConventionAuthority :
      Bool

    constructsAcceptedDYLuminosityConventionAuthorityIsFalse :
      constructsAcceptedDYLuminosityConventionAuthority ≡ false

    constructsW4GateReceipt :
      Bool

    constructsW4GateReceiptIsFalse :
      constructsW4GateReceipt ≡ false

    notes :
      List String

canonicalW4DiagonalConventionGateConsumerRequest :
  W4DiagonalConventionGateConsumerRequest
canonicalW4DiagonalConventionGateConsumerRequest =
  record
    { status =
        diagonalCandidateRejectedNoCentralEfficiencyAcceptanceModel
    ; firstMissing =
        missingSourceCentralEfficiencyAcceptanceModel
    ; candidateReceipt =
        Candidate.canonicalW4ResponseMatrixAcceptanceCandidateReceipt
    ; diagnosticOutputSHA256 =
        "366fe83fe4dae1d14ccb9ef3bd7a0858fa8baf9998fc8c96250c16bc4a748fdb"
    ; checksumManifest =
        "scripts/data/hepdata/ins2079374_response_phistar_t68_t77.sha256"
    ; selectedCandidate =
        Candidate.diagonalCandidate
    ; selectedCandidateIsDiagonal =
        refl
    ; authorityStatus =
        sourceCentralEfficiencyAcceptanceModelMissing
    ; diagonalConventionFormula =
        "Rejected convention candidate: A_diag[j] = P[j][j] is same-bin response retention, not a source central efficiency/acceptance model"
    ; diagonalAdmissibilityStatus =
        diagonalBoundsComputedAndAdmissibleButNotAccepted
    ; diagonalAdmissibilityBoundText =
        "W4-selected diagonal entries are checksum-bound and satisfy 0 <= A_diag[j] <= 1, but this bound does not identify central efficiency/acceptance"
    ; selectedW4DiagonalGlobalMin =
        Candidate.W4ResponseMatrixAcceptanceCandidateReceipt.selectedW4DiagonalGlobalMin
          Candidate.canonicalW4ResponseMatrixAcceptanceCandidateReceipt
    ; selectedW4DiagonalGlobalMax =
        Candidate.W4ResponseMatrixAcceptanceCandidateReceipt.selectedW4DiagonalGlobalMax
          Candidate.canonicalW4ResponseMatrixAcceptanceCandidateReceipt
    ; selectedW4DiagonalGlobalMean =
        Candidate.W4ResponseMatrixAcceptanceCandidateReceipt.selectedW4DiagonalGlobalMean
          Candidate.canonicalW4ResponseMatrixAcceptanceCandidateReceipt
    ; columnSumFalsificationBoundText =
        Candidate.W4ResponseMatrixAcceptanceCandidateReceipt.columnSumMaxAbsGapToOne
          Candidate.canonicalW4ResponseMatrixAcceptanceCandidateReceipt
    ; selectedMassWindows =
        "50-76 GeV"
        ∷ "76-106 GeV"
        ∷ "106-170 GeV"
        ∷ []
    ; electronDiagonalMean50to76 =
        "0.9216377777777777"
    ; muonDiagonalMean50to76 =
        "0.9835272222222221"
    ; electronDiagonalMean76to106 =
        "0.9277322222222223"
    ; muonDiagonalMean76to106 =
        "0.9857633333333333"
    ; electronDiagonalMean106to170 =
        "0.9344861111111111"
    ; muonDiagonalMean106to170 =
        "0.9885316666666666"
    ; channelCombinationCandidate =
        channelSeparatedDiagnosticOnly
    ; channelCombinationFormula =
        "A_geom[j] = sqrt(A_e,j * A_mu,j)"
    ; channelCombinationLawText =
        "Diagnostic-only formula: no electron/muon channel combination is accepted because the source does not provide central efficiency/acceptance."
    ; channelCombinationInputs =
        "electron diagonal vector A_e[j]"
        ∷ "muon diagonal vector A_mu[j]"
        ∷ "positivity/admissibility bound 0 <= A_e[j], A_mu[j] <= 1 from the SHA-bound diagonal diagnostic"
        ∷ []
    ; channelCombinationOutputContract =
        "no accepted output; provider must supply a real central efficiency/acceptance model or accepted conversion law"
    ; covariancePropagationCandidate =
        noAcceptedCovariancePropagationLaw
    ; covariancePropagationFormula =
        "V_y = J V_x J^T, with y_j = sigma_j / A_j and J carrying dy/dsigma = 1/A_j and dy/dA = -sigma_j/A_j^2"
    ; covariancePropagationLawText =
        "No accepted covariance law: propagating sigma/A is not source-valid without a central efficiency/acceptance model."
    ; covariancePropagationInputs =
        "published phi-star covariance for the measured ratio or source spectrum"
        ∷ "response-matrix diagonal uncertainty or accepted proxy"
        ∷ "geometric-mean channel-combination covariance or accepted proxy"
        ∷ "bin-width and normalization convention"
        ∷ []
    ; covariancePropagationOutputContract =
        "no accepted corrected covariance output"
    ; internalAdequacyEvidenceReceipt =
        Candidate.canonicalW4ZInternalAdequacyEvidenceReceipt
    ; internalAdequacyMassWindow =
        "76-106 GeV"
    ; internalAdequacyCombinedEfficiency =
        "not accepted: response diagonal is not central efficiency"
    ; internalAdequacyBound =
        "0.90"
    ; internalAdequacyComputationText =
        "Fail-closed: the former 0.9566 diagonal arithmetic is not W4 adequacy evidence because Table 2/3 and response matrices do not provide a central efficiency/acceptance model"
    ; internalAdequacyFirstMissing =
        Candidate.internalAdequacyBlockedBySourceModelGap
    ; externalAuthorityFirstMissingBeforeHookRequest =
        W4Authority.w4AuthorityFirstMissingBeforePolicyHookRequest
    ; externalAuthorityFirstMissingAfterHookRequest =
        W4Authority.w4AuthorityFirstMissingAfterPolicyHookRequest
    ; externalAuthorityFirstMissingUnchanged =
        W4Authority.w4AuthorityPolicyHookRequestFirstMissingUnchanged
    ; internalAdequacyStrictGreaterThanWitness =
        scaledDecimalStrictGT9566over9000
    ; internalAdequacyComputedPass =
        false
    ; internalAdequacyComputedPassIsFalse =
        refl
    ; acceptedConsumerReceiptShape =
        "acceptedCandidate : none from public Table 2/3 or response matrices"
        ∷ "diagonalAdmissibility : diagnostic only; all W4-selected A_diag[j] in [0,1], SHA-bound"
        ∷ "channelCombinationLaw : missing"
        ∷ "covariancePropagationLaw : missing"
        ∷ "internalAdequacyEvidence : none accepted"
        ∷ "w4AdequacyConsumer : consumes corrected observable and covariance"
        ∷ "promotionBoundary : states whether W4ZAdequacy and W4 gate receipt are constructed"
        ∷ []
    ; requiredAcceptedConsumerFields =
        canonicalW4DiagonalConventionRequiredFields
    ; requiredAcceptedConsumerFieldsAreCanonical =
        refl
    ; diagonalAsAcceptanceConventionAccepted =
        false
    ; diagonalAsAcceptanceConventionAcceptedIsFalse =
        refl
    ; diagonalAdmissibilityBoundsAccepted =
        false
    ; diagonalAdmissibilityBoundsAcceptedIsFalse =
        refl
    ; electronMuonCombinationLawAccepted =
        false
    ; electronMuonCombinationLawAcceptedIsFalse =
        refl
    ; covariancePropagationLawAccepted =
        false
    ; covariancePropagationLawAcceptedIsFalse =
        refl
    ; constructsW4ZAdequacy =
        false
    ; constructsW4ZAdequacyIsFalse =
        refl
    ; constructsAcceptedDYLuminosityConventionAuthority =
        false
    ; constructsAcceptedDYLuminosityConventionAuthorityIsFalse =
        refl
    ; constructsW4GateReceipt =
        false
    ; constructsW4GateReceiptIsFalse =
        refl
    ; notes =
        "The diagonal response-matrix arithmetic remains checksum-bound diagnostic context only"
        ∷ "Table 2/3 do not bind a central efficiency/acceptance model"
        ∷ "The diagonal convention is not accepted as W4 A(M,phi*)"
        ∷ "No electron/muon channel-combination law is accepted"
        ∷ "No covariance propagation law through sigma/A is accepted"
        ∷ "No internal adequacy pass is accepted from 0.9566 > 0.90"
        ∷ "The local blocker is the missing source central efficiency/acceptance model or accepted conversion law"
        ∷ "The external authority blocker is unchanged before/after public-source policy-hook request: missingAcceptedDYLuminosityConventionAuthority"
        ∷ "No W4ZAdequacy, accepted DY convention authority, or W4 gate receipt is constructed"
        ∷ []
    }

canonicalW4DiagonalConventionGateConsumerDoesNotPromoteW4 :
  W4DiagonalConventionGateConsumerRequest.constructsW4GateReceipt
    canonicalW4DiagonalConventionGateConsumerRequest
  ≡ false
canonicalW4DiagonalConventionGateConsumerDoesNotPromoteW4 =
  W4DiagonalConventionGateConsumerRequest.constructsW4GateReceiptIsFalse
    canonicalW4DiagonalConventionGateConsumerRequest

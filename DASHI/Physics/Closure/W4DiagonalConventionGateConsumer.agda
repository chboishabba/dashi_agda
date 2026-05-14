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
  diagonalConventionAcceptedAwaitingW4ZAdequacy :
    W4DiagonalConventionGateConsumerStatus

data W4DiagonalConventionGateConsumerFirstMissing : Set where
  missingAcceptedDiagonalConventionGateConsumer :
    W4DiagonalConventionGateConsumerFirstMissing
  missingW4ZAdequacyConsumer :
    W4DiagonalConventionGateConsumerFirstMissing

data W4DiagonalConventionRequiredField : Set where
  acceptedDiagonalAsAcceptanceConvention :
    W4DiagonalConventionRequiredField
  acceptedDiagonalAdmissibilityBounds :
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
  acceptedDiagonalAsAcceptanceConvention
  ∷ acceptedDiagonalAdmissibilityBounds
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
  geometricMeanChannelCombinationAccepted :
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
  diagonalBoundsComputedAndAccepted :
    W4DiagonalConventionAdmissibilityStatus

data W4DiagonalConventionAuthorityStatus : Set where
  conventionAcceptedW4ZAdequacyPending :
    W4DiagonalConventionAuthorityStatus
  internalAdequacyEvidenceComputedW4GatePending :
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

    internalAdequacyComputedPassIsTrue :
      internalAdequacyComputedPass ≡ true

    acceptedConsumerReceiptShape :
      List String

    requiredAcceptedConsumerFields :
      List W4DiagonalConventionRequiredField

    requiredAcceptedConsumerFieldsAreCanonical :
      requiredAcceptedConsumerFields
      ≡ canonicalW4DiagonalConventionRequiredFields

    diagonalAsAcceptanceConventionAccepted :
      Bool

    diagonalAsAcceptanceConventionAcceptedIsTrue :
      diagonalAsAcceptanceConventionAccepted ≡ true

    diagonalAdmissibilityBoundsAccepted :
      Bool

    diagonalAdmissibilityBoundsAcceptedIsTrue :
      diagonalAdmissibilityBoundsAccepted ≡ true

    electronMuonCombinationLawAccepted :
      Bool

    electronMuonCombinationLawAcceptedIsTrue :
      electronMuonCombinationLawAccepted ≡ true

    covariancePropagationLawAccepted :
      Bool

    covariancePropagationLawAcceptedIsTrue :
      covariancePropagationLawAccepted ≡ true

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
        diagonalConventionAcceptedAwaitingW4ZAdequacy
    ; firstMissing =
        missingW4ZAdequacyConsumer
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
        internalAdequacyEvidenceComputedW4GatePending
    ; diagonalConventionFormula =
        "Accepted convention layer: A_diag[j] = P[j][j], same-bin diagonal of the CMS phi-star response matrix"
    ; diagonalAdmissibilityStatus =
        diagonalBoundsComputedAndAccepted
    ; diagonalAdmissibilityBoundText =
        "W4-selected diagonal entries are checksum-bound and satisfy 0 <= A_diag[j] <= 1; global selected min=0.8279, max=1.0, mean=0.9569463888888888"
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
        geometricMeanChannelCombinationAccepted
    ; channelCombinationFormula =
        "A_geom[j] = sqrt(A_e,j * A_mu,j)"
    ; channelCombinationLawText =
        "Accepted convention-layer law: combine electron and muon diagonal candidates by geometric mean. This avoids claiming an inverse-covariance channel authority before W4ZAdequacy consumes the convention."
    ; channelCombinationInputs =
        "electron diagonal vector A_e[j]"
        ∷ "muon diagonal vector A_mu[j]"
        ∷ "positivity/admissibility bound 0 <= A_e[j], A_mu[j] <= 1 from the SHA-bound diagonal diagnostic"
        ∷ []
    ; channelCombinationOutputContract =
        "accepted convention-layer A_geom[j]; W4ZAdequacy must still consume it with a pass/fail tolerance"
    ; covariancePropagationCandidate =
        linearizedDiagonalRatioCovarianceRequested
    ; covariancePropagationFormula =
        "V_y = J V_x J^T, with y_j = sigma_j / A_j and J carrying dy/dsigma = 1/A_j and dy/dA = -sigma_j/A_j^2"
    ; covariancePropagationLawText =
        "Accepted convention-layer law: propagate measurement and diagonal-response uncertainty through the corrected ratio with a linearized Jacobian. A W4ZAdequacy consumer must still bind the concrete covariance inputs and tolerance."
    ; covariancePropagationInputs =
        "published phi-star covariance for the measured ratio or source spectrum"
        ∷ "response-matrix diagonal uncertainty or accepted proxy"
        ∷ "geometric-mean channel-combination covariance or accepted proxy"
        ∷ "bin-width and normalization convention"
        ∷ []
    ; covariancePropagationOutputContract =
        "accepted covariance for the W4 corrected observable, including whether response-matrix uncertainty is treated as statistical, systematic, or fixed convention"
    ; internalAdequacyEvidenceReceipt =
        Candidate.canonicalW4ZInternalAdequacyEvidenceReceipt
    ; internalAdequacyMassWindow =
        "76-106 GeV"
    ; internalAdequacyCombinedEfficiency =
        "0.9566"
    ; internalAdequacyBound =
        "0.90"
    ; internalAdequacyComputationText =
        "Internal non-promoting adequacy evidence: 76-106 GeV geometric-mean diagonal combined efficiency 0.9566 clears bound 0.90, with an Agda Nat witness for scaled-decimal strict inequality 9566 > 9000"
    ; internalAdequacyFirstMissing =
        Candidate.internalAdequacyArithmeticDischargedW4ZAdequacyPending
    ; externalAuthorityFirstMissingBeforeHookRequest =
        W4Authority.w4AuthorityFirstMissingBeforePolicyHookRequest
    ; externalAuthorityFirstMissingAfterHookRequest =
        W4Authority.w4AuthorityFirstMissingAfterPolicyHookRequest
    ; externalAuthorityFirstMissingUnchanged =
        W4Authority.w4AuthorityPolicyHookRequestFirstMissingUnchanged
    ; internalAdequacyStrictGreaterThanWitness =
        scaledDecimalStrictGT9566over9000
    ; internalAdequacyComputedPass =
        true
    ; internalAdequacyComputedPassIsTrue =
        refl
    ; acceptedConsumerReceiptShape =
        "acceptedCandidate : diagonalCandidate"
        ∷ "diagonalAdmissibility : all W4-selected A_diag[j] in [0,1], SHA-bound"
        ∷ "channelCombinationLaw : geometric mean A_geom[j] = sqrt(A_e,j * A_mu,j)"
        ∷ "covariancePropagationLaw : Jacobian V_y = J V_x J^T"
        ∷ "internalAdequacyEvidence : non-promoting computed evidence with Agda Nat witness for 0.9566 > 0.90"
        ∷ "w4AdequacyConsumer : consumes corrected observable and covariance"
        ∷ "promotionBoundary : states whether W4ZAdequacy and W4 gate receipt are constructed"
        ∷ []
    ; requiredAcceptedConsumerFields =
        canonicalW4DiagonalConventionRequiredFields
    ; requiredAcceptedConsumerFieldsAreCanonical =
        refl
    ; diagonalAsAcceptanceConventionAccepted =
        true
    ; diagonalAsAcceptanceConventionAcceptedIsTrue =
        refl
    ; diagonalAdmissibilityBoundsAccepted =
        true
    ; diagonalAdmissibilityBoundsAcceptedIsTrue =
        refl
    ; electronMuonCombinationLawAccepted =
        true
    ; electronMuonCombinationLawAcceptedIsTrue =
        refl
    ; covariancePropagationLawAccepted =
        true
    ; covariancePropagationLawAcceptedIsTrue =
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
        "The diagonal convention layer is accepted internally for the W4 consumer target"
        ∷ "The local response-matrix arithmetic and diagnostic checksum are bound"
        ∷ "Explicit diagonal admissibility bounds are accepted for the W4-selected windows"
        ∷ "The accepted channel-combination law is the geometric mean, not the previous BLUE request"
        ∷ "The accepted covariance law is linearized Jacobian propagation through sigma/A"
        ∷ "A non-promoting internal adequacy evidence receipt records 0.9566 > 0.90 at the string/scaled-decimal layer with a typed Nat witness"
        ∷ "The diagonal-consumer local blocker is a W4ZAdequacy consumer for the corrected observable and covariance"
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

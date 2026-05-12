module DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate as AUTH
import DASHI.Physics.Closure.W3AcceptedEvidenceAuthorityTokenIntakeRequest as Intake

------------------------------------------------------------------------
-- W3 accepted evidence authority provider-response intake.
--
-- This module records the typed response shape after the final request-only
-- packet.  It preserves the exact external token type but deliberately
-- constructs no W3AcceptedEvidenceAuthorityToken locally.

data W3AcceptedEvidenceAuthorityProviderResponseStatus : Set where
  awaitingProviderResponse :
    W3AcceptedEvidenceAuthorityProviderResponseStatus
  providerAcceptedW3EvidenceAuthority :
    W3AcceptedEvidenceAuthorityProviderResponseStatus
  providerRejectedW3EvidenceAuthority :
    W3AcceptedEvidenceAuthorityProviderResponseStatus
  providerResponseInsufficientForW3EvidenceAuthority :
    W3AcceptedEvidenceAuthorityProviderResponseStatus

data W3EvidenceAuthorityDecision : Set where
  decisionAccepted :
    W3EvidenceAuthorityDecision
  decisionRejected :
    W3EvidenceAuthorityDecision
  decisionInsufficient :
    W3EvidenceAuthorityDecision
  decisionPendingProviderResponse :
    W3EvidenceAuthorityDecision

data W3EvidenceAuthorityRejectionReasonClass : Set where
  providerIdentityRejected :
    W3EvidenceAuthorityRejectionReasonClass
  hepDataDOIMismatch :
    W3EvidenceAuthorityRejectionReasonClass
  cmsPaperDOIMismatch :
    W3EvidenceAuthorityRejectionReasonClass
  frozenCommitMismatch :
    W3EvidenceAuthorityRejectionReasonClass
  comparisonLawRejectedOrUnderspecified :
    W3EvidenceAuthorityRejectionReasonClass
  covarianceSourceRejectedOrUnderspecified :
    W3EvidenceAuthorityRejectionReasonClass
  tableChecksumBindingMissingOrUnderspecified :
    W3EvidenceAuthorityRejectionReasonClass
  nonCollapseWitnessRejectedOrNotReproduced :
    W3EvidenceAuthorityRejectionReasonClass
  authorityScopeCannotIssueW3Token :
    W3EvidenceAuthorityRejectionReasonClass
  noRejectionBecauseResponsePending :
    W3EvidenceAuthorityRejectionReasonClass

record W3AcceptedEvidenceAuthorityProviderResponse : Setω where
  field
    responseStatus :
      W3AcceptedEvidenceAuthorityProviderResponseStatus

    intakeRequest :
      Intake.W3AcceptedEvidenceAuthorityTokenIntakeRequest

    providerIdentity :
      String

    evidenceAuthorityDecision :
      W3EvidenceAuthorityDecision

    hepDataDOI :
      String

    cmsPaperDOI :
      String

    cmsAnalysisId :
      String

    frozenCommit :
      String

    candidateComparisonArtifact :
      String

    candidateComparisonArtifactSha256 :
      String

    candidateComparisonStatus :
      String

    candidateComparisonChi2PerDof :
      String

    localT19CsvSha256 :
      String

    localT20CsvSha256 :
      String

    localT43CsvSha256 :
      String

    localT43ChecksumBindingSource :
      String

    localT44CsvSha256 :
      String

    localT44ChecksumBindingSource :
      String

    localT43T44ManifestPath :
      String

    localT43T44HeadersValidated :
      Bool

    localT43T44HeadersValidatedIsTrue :
      localT43T44HeadersValidated
      ≡
      true

    providerCanonicalT43ChecksumOrEquivalent :
      String

    providerCanonicalT44ChecksumOrEquivalent :
      String

    providerCanonicalTableChecksumBindingPresent :
      Bool

    providerCanonicalTableChecksumBindingPresentIsFalse :
      providerCanonicalTableChecksumBindingPresent
      ≡
      false

    comparisonLaw :
      String

    covarianceSource :
      String

    tableChecksumBound :
      Bool

    tableChecksumBoundIsFalseUntilProviderAttestation :
      tableChecksumBound
      ≡
      false

    exactRemainingChecksumGap :
      String

    nonCollapseWitness :
      String

    exactStatusLabel :
      String

    exactRejectionReason :
      String

    rejectionReasonClass :
      W3EvidenceAuthorityRejectionReasonClass

    requiredResponseFields :
      List String

    responseContainsAcceptedToken :
      Bool

    authorityTokenConstructedHere :
      Bool

    authorityTokenConstructedHereIsFalse :
      authorityTokenConstructedHere
      ≡
      false

    tokenTypePreserved :
      String

    constructorlessTokenBoundary :
      AUTH.W3AcceptedEvidenceAuthorityToken →
      ⊥

    nonPromotionBoundary :
      List String

    exactRemainingGap :
      String

w3AcceptedEvidenceAuthorityTokenImpossibleHere :
  AUTH.W3AcceptedEvidenceAuthorityToken →
  ⊥
w3AcceptedEvidenceAuthorityTokenImpossibleHere ()

canonicalW3AcceptedEvidenceAuthorityProviderResponse :
  W3AcceptedEvidenceAuthorityProviderResponse
canonicalW3AcceptedEvidenceAuthorityProviderResponse =
  record
    { responseStatus =
        awaitingProviderResponse
    ; intakeRequest =
        Intake.canonicalW3AcceptedEvidenceAuthorityTokenIntakeRequest
    ; providerIdentity =
        "awaiting external provider identity"
    ; evidenceAuthorityDecision =
        decisionPendingProviderResponse
    ; hepDataDOI =
        "10.17182/hepdata.104472; submission 10.17182/hepdata.115656.v1; ratio t43; covariance t44"
    ; cmsPaperDOI =
        "10.1140/epjc/s10052-023-11631-7"
    ; cmsAnalysisId =
        "CMS-SMP-20-003"
    ; frozenCommit =
        "3205d746639568762c9e97adf4a3672c356bd491"
    ; candidateComparisonArtifact =
        "logs/research/w3_frozen_3205d74_t43_comparison_20260513.json"
    ; candidateComparisonArtifactSha256 =
        "92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238"
    ; candidateComparisonStatus =
        "candidate-pass-no-authority-token"
    ; candidateComparisonChi2PerDof =
        "2.1565191176275618"
    ; localT19CsvSha256 =
        "1a1d280da645f4c55aba73aabf1b398a3fd9614532c363d972018f194b653677"
    ; localT20CsvSha256 =
        "fa4b694211862d4b07b761d0dab77c8fe1016d2ccd5015dc6f7bc3272c34201a"
    ; localT43CsvSha256 =
        "0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b"
    ; localT43ChecksumBindingSource =
        "local HEP-R28 receipt: HEPDataRatioTableArtifactReceipt canonicalT43RatioArtifactChecksumEntry"
    ; localT44CsvSha256 =
        "3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"
    ; localT44ChecksumBindingSource =
        "local HEP-R28 receipt: HEPDataRatioTableArtifactReceipt canonicalT44RatioCovarianceArtifactChecksumEntry"
    ; localT43T44ManifestPath =
        "scripts/data/hepdata/ins2079374_t43_t44.sha256"
    ; localT43T44HeadersValidated =
        true
    ; localT43T44HeadersValidatedIsTrue =
        refl
    ; providerCanonicalT43ChecksumOrEquivalent =
        "awaiting provider canonical HEPData t43 checksum or immutable equivalent"
    ; providerCanonicalT44ChecksumOrEquivalent =
        "awaiting provider canonical HEPData t44 checksum or immutable equivalent"
    ; providerCanonicalTableChecksumBindingPresent =
        false
    ; providerCanonicalTableChecksumBindingPresentIsFalse =
        refl
    ; comparisonLaw =
        "bounded below-Z t43 per-bin comparison under the unnormalized differential cross-section ratio convention"
    ; covarianceSource =
        "HEPData covariance table t44, source/checksum/provider equivalent still awaiting provider acknowledgement"
    ; tableChecksumBound =
        false
    ; tableChecksumBoundIsFalseUntilProviderAttestation =
        refl
    ; exactRemainingChecksumGap =
        "tableChecksumBound: authoritative HEPData t43/t44 table checksum or provider-equivalent immutable table binding is absent"
    ; nonCollapseWitness =
        "bin 12; pred 0.0486590199823977; data 0.049758; unc 0.00048197510309143566; pull -2.280159308132989"
    ; exactStatusLabel =
        "awaitingProviderResponse"
    ; exactRejectionReason =
        "none yet: provider response has not been received"
    ; rejectionReasonClass =
        noRejectionBecauseResponsePending
    ; requiredResponseFields =
        "provider identity"
        ∷ "evidence authority decision: accepted, rejected, or insufficient"
        ∷ "HEPData DOI and t43/t44 table acknowledgement"
        ∷ "CMS paper DOI"
        ∷ "CMS analysis id CMS-SMP-20-003"
        ∷ "frozen commit"
        ∷ "candidate comparison artifact sha256 92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238"
        ∷ "local CSV checksums: t19 1a1d280da645f4c55aba73aabf1b398a3fd9614532c363d972018f194b653677; t20 fa4b694211862d4b07b761d0dab77c8fe1016d2ccd5015dc6f7bc3272c34201a; t43 0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b; t44 3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"
        ∷ "local HEP-R28 t43/t44 checksum receipt and manifest scripts/data/hepdata/ins2079374_t43_t44.sha256"
        ∷ "provider canonical t43/t44 checksum or provider-equivalent immutable table records"
        ∷ "comparison law"
        ∷ "covariance/source"
        ∷ "tableChecksumBound for authoritative HEPData t43/t44 table payloads or provider-equivalent immutable table records"
        ∷ "non-collapse witness"
        ∷ "exact status"
        ∷ "exact rejection reason for rejected or insufficient responses"
        ∷ []
    ; responseContainsAcceptedToken =
        false
    ; authorityTokenConstructedHere =
        false
    ; authorityTokenConstructedHereIsFalse =
        refl
    ; tokenTypePreserved =
        "DASHI.Physics.Closure.W3AcceptedEmpiricalAuthorityGate.W3AcceptedEvidenceAuthorityToken"
    ; constructorlessTokenBoundary =
        w3AcceptedEvidenceAuthorityTokenImpossibleHere
    ; nonPromotionBoundary =
        "This provider-response packet is an ingestion skeleton only"
        ∷ "It does not construct W3AcceptedEvidenceAuthorityToken"
        ∷ "It does not construct W3EvidenceBackedEmpiricalTarget"
        ∷ "It does not construct W3AcceptedAuthorityExternalReceipt"
        ∷ "It does not promote B4, W8 origin, W4/W5, or broad empirical adequacy"
        ∷ []
    ; exactRemainingGap =
        "missing accepted external W3AcceptedEvidenceAuthorityToken; provider canonical t43/t44 checksum binding and tableChecksumBound are absent"
    }

canonicalW3ProviderResponseTableChecksumBound :
  W3AcceptedEvidenceAuthorityProviderResponse.tableChecksumBound
    canonicalW3AcceptedEvidenceAuthorityProviderResponse
  ≡
  false
canonicalW3ProviderResponseTableChecksumBound = refl

canonicalW3ProviderResponseProviderCanonicalChecksumBindingAbsent :
  W3AcceptedEvidenceAuthorityProviderResponse.providerCanonicalTableChecksumBindingPresent
    canonicalW3AcceptedEvidenceAuthorityProviderResponse
  ≡
  false
canonicalW3ProviderResponseProviderCanonicalChecksumBindingAbsent = refl

record W3AcceptedEvidenceAuthorityTokenReceipt : Setω where
  field
    providerResponse :
      W3AcceptedEvidenceAuthorityProviderResponse

    authorityToken :
      AUTH.W3AcceptedEvidenceAuthorityToken

    providerResponseAccepted :
      W3AcceptedEvidenceAuthorityProviderResponse.responseStatus
        providerResponse
      ≡
      providerAcceptedW3EvidenceAuthority

    providerResponseContainsAcceptedToken :
      W3AcceptedEvidenceAuthorityProviderResponse.responseContainsAcceptedToken
        providerResponse
      ≡
      true

    tokenReceiptProviderIdentity :
      String

    tokenReceiptEvidenceBinding :
      List String

tokenReceiptToExternalToken :
  W3AcceptedEvidenceAuthorityTokenReceipt →
  AUTH.W3AcceptedEvidenceAuthorityToken
tokenReceiptToExternalToken receipt =
  W3AcceptedEvidenceAuthorityTokenReceipt.authorityToken receipt

canonicalW3ProviderResponseStatus :
  W3AcceptedEvidenceAuthorityProviderResponseStatus
canonicalW3ProviderResponseStatus =
  W3AcceptedEvidenceAuthorityProviderResponse.responseStatus
    canonicalW3AcceptedEvidenceAuthorityProviderResponse

canonicalW3ProviderResponseContainsAcceptedToken :
  W3AcceptedEvidenceAuthorityProviderResponse.responseContainsAcceptedToken
    canonicalW3AcceptedEvidenceAuthorityProviderResponse
  ≡
  false
canonicalW3ProviderResponseContainsAcceptedToken = refl

canonicalW3ProviderResponseConstructsNoToken :
  W3AcceptedEvidenceAuthorityProviderResponse.authorityTokenConstructedHere
    canonicalW3AcceptedEvidenceAuthorityProviderResponse
  ≡
  false
canonicalW3ProviderResponseConstructsNoToken = refl

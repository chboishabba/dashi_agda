module DASHI.Physics.Closure.W3CanonicalChecksumBindingReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataRatioTableArtifactReceipt as Ratio

------------------------------------------------------------------------
-- W3 canonical checksum binding receipt.
--
-- This receipt hardens the non-governance provenance gap for the W3 t43/t44
-- evidence packet.  It binds the local CSV artifacts, the staged canonical
-- HEPData JSON payloads supplied by browser download, and the semantic match
-- counts.  It deliberately does not construct W3AcceptedEvidenceAuthorityToken
-- or any accepted authority response.

data W3CanonicalChecksumBindingStatus : Set where
  canonicalT43T44JsonBoundAndSemanticallyMatchedNoAuthorityToken :
    W3CanonicalChecksumBindingStatus

data W3CanonicalChecksumBindingRole : Set where
  canonicalRatioTableT43Json :
    W3CanonicalChecksumBindingRole
  canonicalRatioCovarianceTableT44Json :
    W3CanonicalChecksumBindingRole

data W3CanonicalChecksumBindingSource : Set where
  userSuppliedBrowserDownloadFromHEPData :
    W3CanonicalChecksumBindingSource

data W3CanonicalChecksumBindingBoundary : Set where
  noW3AcceptedEvidenceAuthorityTokenHere :
    W3CanonicalChecksumBindingBoundary
  noW3AcceptedAuthorityExternalReceiptHere :
    W3CanonicalChecksumBindingBoundary
  noW3PromotionHere :
    W3CanonicalChecksumBindingBoundary

canonicalW3CanonicalChecksumBindingBoundaries :
  List W3CanonicalChecksumBindingBoundary
canonicalW3CanonicalChecksumBindingBoundaries =
  noW3AcceptedEvidenceAuthorityTokenHere
  ∷ noW3AcceptedAuthorityExternalReceiptHere
  ∷ noW3PromotionHere
  ∷ []

record W3CanonicalJSONChecksumEntry : Set where
  field
    role :
      W3CanonicalChecksumBindingRole

    tableDOI :
      String

    tableName :
      String

    source :
      W3CanonicalChecksumBindingSource

    stagedPath :
      String

    stagedSha256 :
      String

    canonicalJsonSha256 :
      String

    semanticRowsChecked :
      Nat

    semanticMismatches :
      Nat

canonicalT43JSONChecksumEntry :
  W3CanonicalJSONChecksumEntry
canonicalT43JSONChecksumEntry =
  record
    { role =
        canonicalRatioTableT43Json
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t43"
    ; tableName =
        "phistar mass 50-76 over mass 76-106"
    ; source =
        userSuppliedBrowserDownloadFromHEPData
    ; stagedPath =
        "logs/research/provider_inputs/hepdata_ins2079374/t43_canonical.json"
    ; stagedSha256 =
        "5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340"
    ; canonicalJsonSha256 =
        "9deb46c59a5d44c6d98599c81db154791563b08a576d3b5fe46b7ca9d91996a4"
    ; semanticRowsChecked =
        18
    ; semanticMismatches =
        0
    }

canonicalT44JSONChecksumEntry :
  W3CanonicalJSONChecksumEntry
canonicalT44JSONChecksumEntry =
  record
    { role =
        canonicalRatioCovarianceTableT44Json
    ; tableDOI =
        "10.17182/hepdata.115656.v1/t44"
    ; tableName =
        "Covariance matrices for phistar mass 50-76 over mass 76-106"
    ; source =
        userSuppliedBrowserDownloadFromHEPData
    ; stagedPath =
        "logs/research/provider_inputs/hepdata_ins2079374/t44_canonical.json"
    ; stagedSha256 =
        "2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b"
    ; canonicalJsonSha256 =
        "ee938eedf77b703e3d318eb17fb737163716a849a853b2e414eaf15aa8bc88a7"
    ; semanticRowsChecked =
        324
    ; semanticMismatches =
        0
    }

canonicalW3CanonicalJSONChecksumEntries :
  List W3CanonicalJSONChecksumEntry
canonicalW3CanonicalJSONChecksumEntries =
  canonicalT43JSONChecksumEntry
  ∷ canonicalT44JSONChecksumEntry
  ∷ []

record W3CanonicalChecksumBindingReceipt : Setω where
  field
    status :
      W3CanonicalChecksumBindingStatus

    localCSVArtifactReceipt :
      Ratio.HEPDataRatioTableArtifactReceipt

    localTableChecksumBound :
      Bool

    localTableChecksumBoundIsTrue :
      localTableChecksumBound
      ≡
      true

    providerCanonicalTableChecksumBindingPresent :
      Bool

    providerCanonicalTableChecksumBindingPresentIsTrue :
      providerCanonicalTableChecksumBindingPresent
      ≡
      true

    canonicalJSONEntries :
      List W3CanonicalJSONChecksumEntry

    canonicalJSONEntriesAreCanonical :
      canonicalJSONEntries
      ≡
      canonicalW3CanonicalJSONChecksumEntries

    t43CanonicalJSONSha256 :
      String

    t43CanonicalJSONSha256IsCanonical :
      t43CanonicalJSONSha256
      ≡
      "5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340"

    t44CanonicalJSONSha256 :
      String

    t44CanonicalJSONSha256IsCanonical :
      t44CanonicalJSONSha256
      ≡
      "2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b"

    canonicalIntakeDiagnosticPath :
      String

    canonicalIntakeDiagnosticSha256 :
      String

    providerInputChecksumManifestPath :
      String

    providerInputChecksumManifestSha256 :
      String

    semanticMatchT43Rows :
      Nat

    semanticMatchT44Rows :
      Nat

    semanticMismatches :
      Nat

    evidenceReadyForAuthorityReview :
      Bool

    evidenceReadyForAuthorityReviewIsTrue :
      evidenceReadyForAuthorityReview
      ≡
      true

    constructsW3AcceptedEvidenceAuthorityToken :
      Bool

    constructsW3AcceptedEvidenceAuthorityTokenIsFalse :
      constructsW3AcceptedEvidenceAuthorityToken
      ≡
      false

    boundaries :
      List W3CanonicalChecksumBindingBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalW3CanonicalChecksumBindingBoundaries

canonicalW3CanonicalChecksumBindingReceipt :
  W3CanonicalChecksumBindingReceipt
canonicalW3CanonicalChecksumBindingReceipt =
  record
    { status =
        canonicalT43T44JsonBoundAndSemanticallyMatchedNoAuthorityToken
    ; localCSVArtifactReceipt =
        Ratio.canonicalHEPDataRatioTableArtifactReceipt
    ; localTableChecksumBound =
        true
    ; localTableChecksumBoundIsTrue =
        refl
    ; providerCanonicalTableChecksumBindingPresent =
        true
    ; providerCanonicalTableChecksumBindingPresentIsTrue =
        refl
    ; canonicalJSONEntries =
        canonicalW3CanonicalJSONChecksumEntries
    ; canonicalJSONEntriesAreCanonical =
        refl
    ; t43CanonicalJSONSha256 =
        "5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340"
    ; t43CanonicalJSONSha256IsCanonical =
        refl
    ; t44CanonicalJSONSha256 =
        "2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b"
    ; t44CanonicalJSONSha256IsCanonical =
        refl
    ; canonicalIntakeDiagnosticPath =
        "logs/research/w3_authority_t43_t44_canonical_json_intake_20260513.json"
    ; canonicalIntakeDiagnosticSha256 =
        "f8ffbecbc039e0cee681b589522f7774c0c087c99f010fab86f759f112b4bf61"
    ; providerInputChecksumManifestPath =
        "logs/research/provider_inputs/hepdata_ins2079374/checksums.txt"
    ; providerInputChecksumManifestSha256 =
        "66004b85d63702c6b9ba9f02b91ab150255d9c054e044156037f51cd20614d38"
    ; semanticMatchT43Rows =
        18
    ; semanticMatchT44Rows =
        324
    ; semanticMismatches =
        0
    ; evidenceReadyForAuthorityReview =
        true
    ; evidenceReadyForAuthorityReviewIsTrue =
        refl
    ; constructsW3AcceptedEvidenceAuthorityToken =
        false
    ; constructsW3AcceptedEvidenceAuthorityTokenIsFalse =
        refl
    ; boundaries =
        canonicalW3CanonicalChecksumBindingBoundaries
    ; boundariesAreCanonical =
        refl
    }

canonicalW3LocalTableChecksumBound :
  W3CanonicalChecksumBindingReceipt.localTableChecksumBound
    canonicalW3CanonicalChecksumBindingReceipt
  ≡
  true
canonicalW3LocalTableChecksumBound = refl

canonicalW3ProviderCanonicalBindingPresent :
  W3CanonicalChecksumBindingReceipt.providerCanonicalTableChecksumBindingPresent
    canonicalW3CanonicalChecksumBindingReceipt
  ≡
  true
canonicalW3ProviderCanonicalBindingPresent = refl

canonicalW3ChecksumBindingDoesNotConstructAuthorityToken :
  W3CanonicalChecksumBindingReceipt.constructsW3AcceptedEvidenceAuthorityToken
    canonicalW3CanonicalChecksumBindingReceipt
  ≡
  false
canonicalW3ChecksumBindingDoesNotConstructAuthorityToken = refl

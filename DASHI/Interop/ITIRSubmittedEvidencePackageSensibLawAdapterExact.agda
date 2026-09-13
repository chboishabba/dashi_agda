module DASHI.Interop.ITIRSubmittedEvidencePackageSensibLawAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIR
import DASHI.Interop.ITIRTemporalHealthSensibLawAdapterExact as TemporalAdapter
import DASHI.Law.SensibLawSubmittedEvidencePackageWrongTypeExact as Package
import DASHI.Law.SensibLawWrongTypeCausationElementExact as Element

------------------------------------------------------------------------
-- ITIR NORMALIZED SPINE -> SENSIBLAW SUBMITTED-EVIDENCE PACKAGE
--
-- ITIR continues to own source/provenance/observation/review/promotion.
-- SensibLaw packages multiple legal-evidence modalities on one submitted
-- carrier.  A common carrier is not permission to flatten modal authority.
------------------------------------------------------------------------

record ITIRSubmittedEvidencePackage : Set₁ where
  constructor itirSubmittedEvidencePackage
  field
    submittedPackage : Package.SubmittedEvidencePackage
    sourceArtifact : ITIR.NormalizedArtifact
    packageClaimArtifact : ITIR.NormalizedArtifact
    sourceIsArtifact : ITIR.concept sourceArtifact ≡ ITIR.sourceArtifact
    packageClaimIsReviewable :
      ITIR.concept packageClaimArtifact ≡ ITIR.reviewableClaim
    packageCompilationReference : String

open ITIRSubmittedEvidencePackage public

record ITIRWrongTypeSubmittedPackageAdmission
    {declaration : Element.WrongTypeCausationElementDeclaration}
    (weld : Element.ViolationWrongTypeCausationElementWeld declaration) : Set₁ where
  constructor itirWrongTypeSubmittedPackageAdmission
  field
    packageEvidence : Package.WrongTypeSubmittedEvidencePackage weld
    normalizedPackage : ITIRSubmittedEvidencePackage
    samePackageReference :
      Package.SubmittedEvidencePackage.packageReference
        (Package.WrongTypeSubmittedEvidencePackage.submittedPackage packageEvidence)
      ≡
      Package.SubmittedEvidencePackage.packageReference
        (ITIRSubmittedEvidencePackage.submittedPackage normalizedPackage)
    admissionReference : String

open ITIRWrongTypeSubmittedPackageAdmission public

record ITIRWrongTypeSubmittedPackagePayment
    {declaration : Element.WrongTypeCausationElementDeclaration}
    {weld : Element.ViolationWrongTypeCausationElementWeld declaration}
    (admission : ITIRWrongTypeSubmittedPackageAdmission weld) : Set₁ where
  constructor itirWrongTypeSubmittedPackagePayment
  field
    legalPayment :
      Package.SubmittedEvidencePackagePayment
        (ITIRWrongTypeSubmittedPackageAdmission.packageEvidence admission)
    promotedArtifact : ITIR.NormalizedArtifact
    promotedIsRecord : ITIR.concept promotedArtifact ≡ ITIR.promotedRecord
    promotionReceipt :
      ITIR.PromotionReceipt
        (ITIRSubmittedEvidencePackage.packageClaimArtifact
          (ITIRWrongTypeSubmittedPackageAdmission.normalizedPackage admission))
        promotedArtifact
    paymentReference : String

open ITIRWrongTypeSubmittedPackagePayment public

------------------------------------------------------------------------
-- Parity boundary.
------------------------------------------------------------------------

record ITIRSubmittedEvidencePackageParityBoundary : Set where
  constructor itirSubmittedEvidencePackageParityBoundary
  field
    packageStartsFromSourceArtifact : Bool
    packageStartsFromSourceArtifactIsTrue :
      packageStartsFromSourceArtifact ≡ true

    packageLegalClaimStartsReviewable : Bool
    packageLegalClaimStartsReviewableIsTrue :
      packageLegalClaimStartsReviewable ≡ true

    packageMayFlattenModalityAuthority : Bool
    packageMayFlattenModalityAuthorityIsFalse :
      packageMayFlattenModalityAuthority ≡ false

    packageMayBypassPromotion : Bool
    packageMayBypassPromotionIsFalse : packageMayBypassPromotion ≡ false

    packageAdmissionAutomaticallyPaysCausation : Bool
    packageAdmissionAutomaticallyPaysCausationIsFalse :
      packageAdmissionAutomaticallyPaysCausation ≡ false

canonicalITIRSubmittedEvidencePackageParityBoundary :
  ITIRSubmittedEvidencePackageParityBoundary
canonicalITIRSubmittedEvidencePackageParityBoundary =
  itirSubmittedEvidencePackageParityBoundary
    true refl
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PackageFlattensModalityAuthority : Set where
data PackageBypassesPromotion : Set where
data PackageAdmissionAutomaticallyPaysCausation : Set where

packageDoesNotFlattenModalityAuthority :
  PackageFlattensModalityAuthority → ⊥
packageDoesNotFlattenModalityAuthority ()

packageDoesNotBypassPromotion : PackageBypassesPromotion → ⊥
packageDoesNotBypassPromotion ()

packageAdmissionDoesNotAutoPayCausation :
  PackageAdmissionAutomaticallyPaysCausation → ⊥
packageAdmissionDoesNotAutoPayCausation ()

------------------------------------------------------------------------
-- Regression bridge: the temporal adapter remains a constituent owner.
------------------------------------------------------------------------

selectedTemporalBoundary :
  TemporalAdapter.ITIRTemporalHealthSensibLawParityBoundary
selectedTemporalBoundary =
  TemporalAdapter.canonicalITIRTemporalHealthSensibLawParityBoundary

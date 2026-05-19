module DASHI.Physics.Closure.HEPDataComparisonLawReceiptRequest where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HEPDataRatioComparisonLawIntakeRequest as Intake

------------------------------------------------------------------------
-- HEP-R31: future HEPData comparison-law receipt skeleton.
--
-- HEP-R27 records that comparison intake is blocked.  This module records the
-- future receipt shape requested for the t43/t44 comparison-law lane: adapter
-- receipt, projection artifact, t43/t44 digests, freeze hash, worktree clean
-- certificate, chi2, chi2/dof, per-bin 2 sigma law, and authority DOI.
--
-- This is request/skeleton-only.  It does not parse covariance, run DASHI,
-- compute chi2, accept a comparison law, claim empirical adequacy, or promote
-- W3.  The future receipt is intentionally uninhabitable here because the
-- current artifacts, freeze, projection, covariance parsing, and real DASHI
-- prediction are absent. HEP-R28 now supplies the t43/t44 artifact digests,
-- but this skeleton remains uninhabited until the freeze, projection, and
-- comparison pieces exist.

data HEPDataComparisonLawReceiptRequestStatus : Set where
  blockedAwaitingComparisonLawReceiptArtifacts :
    HEPDataComparisonLawReceiptRequestStatus

data HEPDataComparisonLawReceiptField : Set where
  adapterReceiptField :
    HEPDataComparisonLawReceiptField
  projectionArtifactField :
    HEPDataComparisonLawReceiptField
  t43DigestField :
    HEPDataComparisonLawReceiptField
  t44DigestField :
    HEPDataComparisonLawReceiptField
  freezeHashField :
    HEPDataComparisonLawReceiptField
  worktreeCleanCertificateField :
    HEPDataComparisonLawReceiptField
  chi2Field :
    HEPDataComparisonLawReceiptField
  chi2PerDofField :
    HEPDataComparisonLawReceiptField
  perBinTwoSigmaLawField :
    HEPDataComparisonLawReceiptField
  authorityDOIField :
    HEPDataComparisonLawReceiptField

canonicalHEPDataComparisonLawReceiptFields :
  List HEPDataComparisonLawReceiptField
canonicalHEPDataComparisonLawReceiptFields =
  adapterReceiptField
  ∷ projectionArtifactField
  ∷ t43DigestField
  ∷ t44DigestField
  ∷ freezeHashField
  ∷ worktreeCleanCertificateField
  ∷ chi2Field
  ∷ chi2PerDofField
  ∷ perBinTwoSigmaLawField
  ∷ authorityDOIField
  ∷ []

data HEPDataComparisonLawReceiptCurrentGap : Set where
  missingAdapterTransformReceipt :
    HEPDataComparisonLawReceiptCurrentGap
  missingProjectionArtifact :
    HEPDataComparisonLawReceiptCurrentGap
  missingT43T44DigestReceipts :
    HEPDataComparisonLawReceiptCurrentGap
  missingAcceptedFreezeHash :
    HEPDataComparisonLawReceiptCurrentGap
  missingWorktreeCleanCertificate :
    HEPDataComparisonLawReceiptCurrentGap
  missingCovarianceParsing :
    HEPDataComparisonLawReceiptCurrentGap
  missingRealDASHIPrediction :
    HEPDataComparisonLawReceiptCurrentGap
  missingChi2Computation :
    HEPDataComparisonLawReceiptCurrentGap
  missingPerBinTwoSigmaLaw :
    HEPDataComparisonLawReceiptCurrentGap
  missingAuthorityDOIBinding :
    HEPDataComparisonLawReceiptCurrentGap

canonicalHEPDataComparisonLawReceiptCurrentGaps :
  List HEPDataComparisonLawReceiptCurrentGap
canonicalHEPDataComparisonLawReceiptCurrentGaps =
  missingAdapterTransformReceipt
  ∷ missingProjectionArtifact
  ∷ missingAcceptedFreezeHash
  ∷ missingWorktreeCleanCertificate
  ∷ missingCovarianceParsing
  ∷ missingRealDASHIPrediction
  ∷ missingChi2Computation
  ∷ missingPerBinTwoSigmaLaw
  ∷ missingAuthorityDOIBinding
  ∷ []

data HEPDataComparisonLawReceiptBoundary : Set where
  noChi2ResultClaimed :
    HEPDataComparisonLawReceiptBoundary
  noAcceptedComparisonLawConstructed :
    HEPDataComparisonLawReceiptBoundary
  noEmpiricalAdequacyClaim :
    HEPDataComparisonLawReceiptBoundary
  noW3Promotion :
    HEPDataComparisonLawReceiptBoundary
  noAuthorityFromDOITextAlone :
    HEPDataComparisonLawReceiptBoundary

canonicalHEPDataComparisonLawReceiptBoundaries :
  List HEPDataComparisonLawReceiptBoundary
canonicalHEPDataComparisonLawReceiptBoundaries =
  noChi2ResultClaimed
  ∷ noAcceptedComparisonLawConstructed
  ∷ noEmpiricalAdequacyClaim
  ∷ noW3Promotion
  ∷ noAuthorityFromDOITextAlone
  ∷ []

data HEPDataComparisonLawReceiptUninhabitedGate : Set where

comparisonLawReceiptUninhabitedGateImpossibleHere :
  HEPDataComparisonLawReceiptUninhabitedGate →
  ⊥
comparisonLawReceiptUninhabitedGateImpossibleHere ()

record HEPDataComparisonLawReceiptShape : Setω where
  field
    adapterReceipt :
      Set

    projectionArtifact :
      Set

    t43Digest :
      String

    t44Digest :
      String

    freezeHash :
      String

    worktreeCleanCertificate :
      Set

    chi2 :
      Set

    chi2PerDof :
      Set

    perBinTwoSigmaLaw :
      Set

    authorityDOI :
      String

    currentArtifactsExist :
      HEPDataComparisonLawReceiptUninhabitedGate

comparisonLawReceiptShapeImpossibleHere :
  HEPDataComparisonLawReceiptShape →
  ⊥
comparisonLawReceiptShapeImpossibleHere receipt =
  comparisonLawReceiptUninhabitedGateImpossibleHere
    (HEPDataComparisonLawReceiptShape.currentArtifactsExist receipt)

record HEPDataComparisonLawReceiptRequest : Setω where
  field
    status :
      HEPDataComparisonLawReceiptRequestStatus

    intakeRequest :
      Intake.HEPDataRatioComparisonLawIntakeRequest

    intakeStillBlocked :
      Intake.canonicalHEPDataRatioComparisonLawIntakeStatus
      ≡
      Intake.blockedAwaitingRatioComparisonIntakeReceipts

    requiredFields :
      List HEPDataComparisonLawReceiptField

    requiredFieldsAreCanonical :
      requiredFields
      ≡
      canonicalHEPDataComparisonLawReceiptFields

    exactRequiredReceiptShape :
      List String

    currentGaps :
      List HEPDataComparisonLawReceiptCurrentGap

    currentGapsAreCanonical :
      currentGaps
      ≡
      canonicalHEPDataComparisonLawReceiptCurrentGaps

    requestOnly :
      Bool

    nonPromoting :
      Bool

    boundaries :
      List HEPDataComparisonLawReceiptBoundary

    boundariesAreCanonical :
      boundaries
      ≡
      canonicalHEPDataComparisonLawReceiptBoundaries

    futureReceiptBlocked :
      HEPDataComparisonLawReceiptShape →
      ⊥

canonicalHEPDataComparisonLawReceiptRequest :
  HEPDataComparisonLawReceiptRequest
canonicalHEPDataComparisonLawReceiptRequest =
  record
    { status =
        blockedAwaitingComparisonLawReceiptArtifacts
    ; intakeRequest =
        Intake.canonicalHEPDataRatioComparisonLawIntakeRequest
    ; intakeStillBlocked =
        refl
    ; requiredFields =
        canonicalHEPDataComparisonLawReceiptFields
    ; requiredFieldsAreCanonical =
        refl
    ; exactRequiredReceiptShape =
        "adapterReceipt : receipt for the selected t43/t44 HEPData adapter transform"
        ∷ "projectionArtifact : digest-bound DASHI projection artifact over the selected t43 bins"
        ∷ "t43Digest : supplied by HEP-R28 as 0c46377d8f119abce35e6304c9a88dd03da663833b63848572e062ea532c7d2b"
        ∷ "t44Digest : supplied by HEP-R28 as 3526be84e53db1b1ae13d8e17ed3ab724750ae1298ca6b4fa11e9c0253ecb54b"
        ∷ "freezeHash : accepted immutable hash for the frozen DASHI prediction code and inputs"
        ∷ "worktreeCleanCertificate : certificate that the freeze source was clean at receipt time"
        ∷ "chi2 : covariance-aware comparison statistic computed from the frozen projection and t43/t44 artifacts"
        ∷ "chi2PerDof : chi2 divided by the receipt-bound degrees of freedom"
        ∷ "perBinTwoSigmaLaw : per-bin law stating the allowed two-sigma residual boundary"
        ∷ "authorityDOI : DOI authority binding for the accepted external HEPData/CMS source"
        ∷ []
    ; currentGaps =
        canonicalHEPDataComparisonLawReceiptCurrentGaps
    ; currentGapsAreCanonical =
        refl
    ; requestOnly =
        true
    ; nonPromoting =
        true
    ; boundaries =
        canonicalHEPDataComparisonLawReceiptBoundaries
    ; boundariesAreCanonical =
        refl
    ; futureReceiptBlocked =
        comparisonLawReceiptShapeImpossibleHere
    }

canonicalHEPDataComparisonLawReceiptRequestStatus :
  HEPDataComparisonLawReceiptRequestStatus
canonicalHEPDataComparisonLawReceiptRequestStatus =
  blockedAwaitingComparisonLawReceiptArtifacts

canonicalHEPDataComparisonLawReceiptShapeBlocked :
  HEPDataComparisonLawReceiptShape →
  ⊥
canonicalHEPDataComparisonLawReceiptShapeBlocked =
  HEPDataComparisonLawReceiptRequest.futureReceiptBlocked
    canonicalHEPDataComparisonLawReceiptRequest

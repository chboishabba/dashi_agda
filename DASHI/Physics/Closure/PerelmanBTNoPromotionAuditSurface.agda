module DASHI.Physics.Closure.PerelmanBTNoPromotionAuditSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.PerelmanBTNoPromotionLaw as Law
import DASHI.Physics.Closure.PerelmanBTGeometrizationAnalogueSummary as Summary
import DASHI.Physics.Closure.PerelmanBTAnalogueImportSmoke as Smoke

------------------------------------------------------------------------
-- Agda mirror of scripts/perelman_bt_no_promotion_audit.py.
--
-- This is intentionally only Nat/List/String bookkeeping.  It mirrors the
-- audit policy as typed data: the blocked-hit rows are empty, while the
-- required evidence rows are present with an exact count.

listLength : {A : Set} → List A → Nat
listLength [] =
  0
listLength (_ ∷ xs) =
  suc (listLength xs)

data ForbiddenAuditToken : Set where
  convergesPointwiseToken :
    ForbiddenAuditToken

  smoothSurgeryPromotionSpellingToken :
    ForbiddenAuditToken

  clayClaimPromotedTrueToken :
    ForbiddenAuditToken

  geometrizationClaimPromotedTrueToken :
    ForbiddenAuditToken

forbiddenAuditTokenName : ForbiddenAuditToken → String
forbiddenAuditTokenName convergesPointwiseToken =
  "blocked convergence-token spelling"
forbiddenAuditTokenName smoothSurgeryPromotionSpellingToken =
  "blocked smooth-surgery-promotion spelling"
forbiddenAuditTokenName clayClaimPromotedTrueToken =
  "blocked Clay-claim true spelling"
forbiddenAuditTokenName geometrizationClaimPromotedTrueToken =
  "blocked geometrization-claim true spelling"

allForbiddenAuditTokens :
  List ForbiddenAuditToken
allForbiddenAuditTokens =
  convergesPointwiseToken
  ∷ smoothSurgeryPromotionSpellingToken
  ∷ clayClaimPromotedTrueToken
  ∷ geometrizationClaimPromotedTrueToken
  ∷ []

allForbiddenAuditTokenCount :
  Nat
allForbiddenAuditTokenCount =
  listLength allForbiddenAuditTokens

allForbiddenAuditTokenCountIs4 :
  allForbiddenAuditTokenCount ≡ 4
allForbiddenAuditTokenCountIs4 =
  refl

forbiddenRows :
  List String
forbiddenRows =
  []

forbiddenRowCount :
  Nat
forbiddenRowCount =
  listLength forbiddenRows

forbiddenRowsAreEmpty :
  forbiddenRows ≡ []
forbiddenRowsAreEmpty =
  refl

forbiddenRowCountIs0 :
  forbiddenRowCount ≡ 0
forbiddenRowCountIs0 =
  refl

requiredIndexEvidenceRow : String
requiredIndexEvidenceRow =
  "PerelmanBTGeometrizationAnalogueIndex"

requiredBoundaryEvidenceRow : String
requiredBoundaryEvidenceRow =
  "No local btGaussianReducedVolume"

requiredConstructibleCountEvidenceRow : String
requiredConstructibleCountEvidenceRow =
  "constructibleRowCountIs10"

requiredBlockerCountEvidenceRow : String
requiredBlockerCountEvidenceRow =
  "smoothAuthorityBlockerCountIs9"

requiredRows :
  List String
requiredRows =
  requiredIndexEvidenceRow
  ∷ requiredBoundaryEvidenceRow
  ∷ requiredConstructibleCountEvidenceRow
  ∷ requiredBlockerCountEvidenceRow
  ∷ []

requiredRowCount :
  Nat
requiredRowCount =
  listLength requiredRows

requiredRowConcreteCount :
  Nat
requiredRowConcreteCount =
  4

requiredRowCountIs4 :
  requiredRowCount ≡ 4
requiredRowCountIs4 =
  refl

requiredRowCountMatchesConcrete :
  requiredRowCount ≡ requiredRowConcreteCount
requiredRowCountMatchesConcrete =
  refl

requiredEvidenceSummaryCountIs10 :
  Summary.summaryConstructibleRowCountIs10 ≡ Summary.summaryConstructibleRowCountIs10
requiredEvidenceSummaryCountIs10 =
  refl

requiredEvidenceBlockerCountIs9 :
  Summary.summaryBlockerCountIs9 ≡ Summary.summaryBlockerCountIs9
requiredEvidenceBlockerCountIs9 =
  refl

record PerelmanBTNoPromotionAuditSurface : Setω where
  constructor perelmanBTNoPromotionAuditSurface
  field
    noPromotionLaw :
      Law.PerelmanBTNoPromotionLaw

    geometrizationSummary :
      Summary.PerelmanBTGeometrizationAnalogueSummary

    importSmoke :
      Smoke.PerelmanBTAnalogueImportSmoke

    forbiddenTokenUniverse :
      List ForbiddenAuditToken
    forbiddenTokenUniverseIsCanonical :
      forbiddenTokenUniverse ≡ allForbiddenAuditTokens
    forbiddenTokenUniverseCount :
      Nat
    forbiddenTokenUniverseCountIs4 :
      forbiddenTokenUniverseCount ≡ 4

    forbiddenHitRows :
      List String
    forbiddenHitRowsAreEmpty :
      forbiddenHitRows ≡ []
    forbiddenHitRowCount :
      Nat
    forbiddenHitRowCountIs0 :
      forbiddenHitRowCount ≡ 0

    requiredEvidenceRows :
      List String
    requiredEvidenceRowsAreCanonical :
      requiredEvidenceRows ≡ requiredRows
    requiredEvidenceRowCount :
      Nat
    requiredEvidenceRowCountIs4 :
      requiredEvidenceRowCount ≡ 4
    requiredEvidenceRowCountMatchesConcrete :
      requiredEvidenceRowCount ≡ requiredRowConcreteCount

    summaryConstructibleEvidencePresent :
      Summary.summaryConstructibleRowCountIs10
      ≡
      Summary.summaryConstructibleRowCountIs10

    summaryBlockerEvidencePresent :
      Summary.summaryBlockerCountIs9
      ≡
      Summary.summaryBlockerCountIs9

    auditSurfaceStatus :
      String

open PerelmanBTNoPromotionAuditSurface public

canonicalPerelmanBTNoPromotionAuditSurface :
  PerelmanBTNoPromotionAuditSurface
canonicalPerelmanBTNoPromotionAuditSurface =
  perelmanBTNoPromotionAuditSurface
    Law.canonicalPerelmanBTNoPromotionLaw
    Summary.canonicalPerelmanBTGeometrizationAnalogueSummary
    Smoke.perelmanBTAnalogueImportSmoke
    allForbiddenAuditTokens
    refl
    allForbiddenAuditTokenCount
    allForbiddenAuditTokenCountIs4
    forbiddenRows
    forbiddenRowsAreEmpty
    forbiddenRowCount
    forbiddenRowCountIs0
    requiredRows
    refl
    requiredRowCount
    requiredRowCountIs4
    requiredRowCountMatchesConcrete
    requiredEvidenceSummaryCountIs10
    requiredEvidenceBlockerCountIs9
    "Agda no-promotion audit surface: forbidden rows empty; four required evidence rows present."

canonicalAuditForbiddenRowsEmpty :
  forbiddenHitRows canonicalPerelmanBTNoPromotionAuditSurface
  ≡
  []
canonicalAuditForbiddenRowsEmpty =
  refl

canonicalAuditRequiredRowsCountIs4 :
  requiredEvidenceRowCount canonicalPerelmanBTNoPromotionAuditSurface
  ≡
  4
canonicalAuditRequiredRowsCountIs4 =
  refl

canonicalAuditRequiredRowsMatchConcrete :
  requiredEvidenceRowCount canonicalPerelmanBTNoPromotionAuditSurface
  ≡
  requiredRowConcreteCount
canonicalAuditRequiredRowsMatchConcrete =
  refl

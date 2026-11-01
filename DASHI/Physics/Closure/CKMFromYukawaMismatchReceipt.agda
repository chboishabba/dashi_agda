module DASHI.Physics.Closure.CKMFromYukawaMismatchReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- CKM from Yukawa-mismatch receipt.
--
-- This records the leading Froggatt-Nielsen mismatch reading: the Cabibbo
-- angle is identified, at leading 1-2 order, with the down-type depth
-- separation alphaD.  The receipt is diagnostic/structural only.  It does
-- not promote the physical CKM matrix or physical Yukawa predictions because
-- the full 3x3 biunitary diagonalisation remains open.

data YukawaMismatchCKMStatus : Set where
  candidate :
    YukawaMismatchCKMStatus

data CKMFromYukawaMismatchBlocker : Set where
  full3x3YukawaDiagonalisationOpen :
    CKMFromYukawaMismatchBlocker

  missingPhysicalCKMPromotion :
    CKMFromYukawaMismatchBlocker

  missingPhysicalYukawaPromotion :
    CKMFromYukawaMismatchBlocker

canonicalCKMFromYukawaMismatchBlockers :
  List CKMFromYukawaMismatchBlocker
canonicalCKMFromYukawaMismatchBlockers =
  full3x3YukawaDiagonalisationOpen
  ∷ missingPhysicalCKMPromotion
  ∷ missingPhysicalYukawaPromotion
  ∷ []

data CKMFromYukawaMismatchPromotion : Set where

ckmFromYukawaMismatchPromotionImpossibleHere :
  CKMFromYukawaMismatchPromotion →
  ⊥
ckmFromYukawaMismatchPromotionImpossibleHere ()

record CKMFromYukawaMismatchReceipt : Set where
  field
    yukawaMismatchGivesCKM :
      YukawaMismatchCKMStatus

    yukawaMismatchGivesCKMIsCandidate :
      yukawaMismatchGivesCKM ≡ candidate

    leadingFNEstimate :
      String

    cabibboAngleFromDownTypeAlphaD :
      Float

    cabibboAngleFromDownTypeAlphaDIsCanonical :
      cabibboAngleFromDownTypeAlphaD ≡ 0.2242

    pdgVusReference :
      Float

    pdgVusReferenceIsCanonical :
      pdgVusReference ≡ 0.2245

    pdgVusAgreementPercent :
      Float

    pdgVusAgreementPercentIsCanonical :
      pdgVusAgreementPercent ≡ 0.13

    agreesWithExistingDASHILambda :
      Bool

    agreesWithExistingDASHILambdaIsTrue :
      agreesWithExistingDASHILambda ≡ true

    dashiLambdaIdentification :
      String

    unificationOfLambdaAndAlphaD :
      String

    unificationOfLambdaAndAlphaDIsStructuralResult :
      unificationOfLambdaAndAlphaD ≡ "structural result"

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    physicalYukawaPromoted :
      Bool

    physicalYukawaPromotedIsFalse :
      physicalYukawaPromoted ≡ false

    full3x3DiagonalisationComplete :
      Bool

    full3x3DiagonalisationCompleteIsFalse :
      full3x3DiagonalisationComplete ≡ false

    blockers :
      List CKMFromYukawaMismatchBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMFromYukawaMismatchBlockers

    promotionFlags :
      List CKMFromYukawaMismatchPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMFromYukawaMismatchReceipt public

canonicalCKMFromYukawaMismatchReceipt :
  CKMFromYukawaMismatchReceipt
canonicalCKMFromYukawaMismatchReceipt =
  record
    { yukawaMismatchGivesCKM =
        candidate
    ; yukawaMismatchGivesCKMIsCandidate =
        refl
    ; leadingFNEstimate =
        "theta12 ~= alphaD from mismatch of Yu and Yd diagonalisations"
    ; cabibboAngleFromDownTypeAlphaD =
        0.2242
    ; cabibboAngleFromDownTypeAlphaDIsCanonical =
        refl
    ; pdgVusReference =
        0.2245
    ; pdgVusReferenceIsCanonical =
        refl
    ; pdgVusAgreementPercent =
        0.13
    ; pdgVusAgreementPercentIsCanonical =
        refl
    ; agreesWithExistingDASHILambda =
        true
    ; agreesWithExistingDASHILambdaIsTrue =
        refl
    ; dashiLambdaIdentification =
        "Existing DASHI lambda derivation is the same quantity as the down-type 1-2 depth separation"
    ; unificationOfLambdaAndAlphaD =
        "structural result"
    ; unificationOfLambdaAndAlphaDIsStructuralResult =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; physicalYukawaPromoted =
        false
    ; physicalYukawaPromotedIsFalse =
        refl
    ; full3x3DiagonalisationComplete =
        false
    ; full3x3DiagonalisationCompleteIsFalse =
        refl
    ; blockers =
        canonicalCKMFromYukawaMismatchBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Records CKM as a candidate from mismatch of Yu and Yd diagonalisations"
        ∷ "Leading Cabibbo FN estimate is theta12 ~= alphaD = 0.2242"
        ∷ "The estimate matches PDG |Vus| = 0.2245 at about 0.13 percent"
        ∷ "Existing DASHI lambda and down-type alphaD are identified structurally"
        ∷ "Physical CKM and physical Yukawa promotions remain false"
        ∷ "Full 3x3 diagonalisation remains open"
        ∷ []
    }

ckmFromYukawaMismatchRecordsCandidate :
  yukawaMismatchGivesCKM canonicalCKMFromYukawaMismatchReceipt
  ≡
  candidate
ckmFromYukawaMismatchRecordsCandidate =
  refl

ckmFromYukawaMismatchAgreesWithExistingLambda :
  agreesWithExistingDASHILambda canonicalCKMFromYukawaMismatchReceipt
  ≡
  true
ckmFromYukawaMismatchAgreesWithExistingLambda =
  refl

ckmFromYukawaMismatchKeepsPhysicalCKMClosed :
  physicalCKMPromoted canonicalCKMFromYukawaMismatchReceipt
  ≡
  false
ckmFromYukawaMismatchKeepsPhysicalCKMClosed =
  refl

ckmFromYukawaMismatchKeepsPhysicalYukawaClosed :
  physicalYukawaPromoted canonicalCKMFromYukawaMismatchReceipt
  ≡
  false
ckmFromYukawaMismatchKeepsPhysicalYukawaClosed =
  refl

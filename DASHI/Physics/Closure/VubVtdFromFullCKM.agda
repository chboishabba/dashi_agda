module DASHI.Physics.Closure.VubVtdFromFullCKM where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CKMFromPhysicalMassMatrix as CKM

------------------------------------------------------------------------
-- Complex-entry CKM tail and Jarlskog diagnostic.

data VubVtdFromFullCKMStatus : Set where
  vubVtdJarlskogDiagnosticRecorded :
    VubVtdFromFullCKMStatus

data VubVtdFromFullCKMBlocker : Set where
  jarlskogTooLargeInDiagnostic :
    VubVtdFromFullCKMBlocker

  missingPhysicalCPPhaseAuthority :
    VubVtdFromFullCKMBlocker

  missingCertifiedComplexEigenbasis :
    VubVtdFromFullCKMBlocker

canonicalVubVtdFromFullCKMBlockers :
  List VubVtdFromFullCKMBlocker
canonicalVubVtdFromFullCKMBlockers =
  jarlskogTooLargeInDiagnostic
  ∷ missingPhysicalCPPhaseAuthority
  ∷ missingCertifiedComplexEigenbasis
  ∷ []

data VubVtdFromFullCKMPromotion : Set where

vubVtdFromFullCKMPromotionImpossibleHere :
  VubVtdFromFullCKMPromotion →
  ⊥
vubVtdFromFullCKMPromotionImpossibleHere ()

record VubVtdFromFullCKMReceipt : Set where
  field
    status :
      VubVtdFromFullCKMStatus

    ckmReceipt :
      CKM.CKMFromPhysicalMassMatrixReceipt

    ckmReceiptIsCanonical :
      ckmReceipt ≡ CKM.canonicalCKMFromPhysicalMassMatrixReceipt

    diagnosticScript :
      String

    vubAbs :
      Float

    vtdAbs :
      Float

    jarlskog :
      Float

    jarlskogAbs :
      Float

    pdgJarlskogTarget :
      Float

    jOverPDGAbs :
      Float

    jarlskogInvariantComputed :
      Bool

    jarlskogInvariantComputedIsTrue :
      jarlskogInvariantComputed ≡ true

    cpViolationDiagnosticRecorded :
      Bool

    cpViolationDiagnosticRecordedIsTrue :
      cpViolationDiagnosticRecorded ≡ true

    physicalCPPhaseDerived :
      Bool

    physicalCPPhaseDerivedIsFalse :
      physicalCPPhaseDerived ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List VubVtdFromFullCKMBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVubVtdFromFullCKMBlockers

    promotionFlags :
      List VubVtdFromFullCKMPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open VubVtdFromFullCKMReceipt public

canonicalVubVtdFromFullCKMReceipt :
  VubVtdFromFullCKMReceipt
canonicalVubVtdFromFullCKMReceipt =
  record
    { status =
        vubVtdJarlskogDiagnosticRecorded
    ; ckmReceipt =
        CKM.canonicalCKMFromPhysicalMassMatrixReceipt
    ; ckmReceiptIsCanonical =
        refl
    ; diagnosticScript =
        "scripts/check_vub_vtd_jarlskog.py"
    ; vubAbs =
        0.7557621132954777
    ; vtdAbs =
        0.13114167929480824
    ; jarlskog =
        -0.00034677077334643956
    ; jarlskogAbs =
        0.00034677077334643956
    ; pdgJarlskogTarget =
        0.0000308
    ; jOverPDGAbs =
        11.258791342416867
    ; jarlskogInvariantComputed =
        true
    ; jarlskogInvariantComputedIsTrue =
        refl
    ; cpViolationDiagnosticRecorded =
        true
    ; cpViolationDiagnosticRecordedIsTrue =
        refl
    ; physicalCPPhaseDerived =
        false
    ; physicalCPPhaseDerivedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalVubVtdFromFullCKMBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The complex full-CKM diagnostic yields nonzero Jarlskog bookkeeping"
        ∷ "The magnitude is about 11.26 times the PDG-sized target and is not a physical match"
        ∷ "No physical CP phase or CKM promotion is asserted"
        ∷ []
    }

vubVtdFullCKMDoesNotPromoteCP :
  physicalCPPhaseDerived canonicalVubVtdFromFullCKMReceipt ≡ false
vubVtdFullCKMDoesNotPromoteCP =
  refl


module DASHI.Physics.Closure.CKMFromPhysicalMassMatrix where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.PhysicalMassMatrixReceipt as Mass

------------------------------------------------------------------------
-- CKM diagnostic after VEV calibration.

data CKMFromPhysicalMassMatrixStatus : Set where
  physicalMassMatrixCKMDiagnosticRecorded :
    CKMFromPhysicalMassMatrixStatus

data CKMFromPhysicalMassMatrixBlocker : Set where
  vevScaleDoesNotChangeEigenvectors :
    CKMFromPhysicalMassMatrixBlocker

  diagnosticMatrixPoorPDGMatch :
    CKMFromPhysicalMassMatrixBlocker

  missingCertifiedUnitaryDiagonalisation :
    CKMFromPhysicalMassMatrixBlocker

  missingPDGAuthorityBinding :
    CKMFromPhysicalMassMatrixBlocker

canonicalCKMFromPhysicalMassMatrixBlockers :
  List CKMFromPhysicalMassMatrixBlocker
canonicalCKMFromPhysicalMassMatrixBlockers =
  vevScaleDoesNotChangeEigenvectors
  ∷ diagnosticMatrixPoorPDGMatch
  ∷ missingCertifiedUnitaryDiagonalisation
  ∷ missingPDGAuthorityBinding
  ∷ []

data CKMFromPhysicalMassMatrixPromotion : Set where

ckmFromPhysicalMassMatrixPromotionImpossibleHere :
  CKMFromPhysicalMassMatrixPromotion →
  ⊥
ckmFromPhysicalMassMatrixPromotionImpossibleHere ()

record CKMFromPhysicalMassMatrixReceipt : Set where
  field
    status :
      CKMFromPhysicalMassMatrixStatus

    massMatrixReceipt :
      Mass.PhysicalMassMatrixReceipt

    massMatrixReceiptIsCanonical :
      massMatrixReceipt ≡ Mass.canonicalPhysicalMassMatrixReceipt

    diagnosticScript :
      String

    scaleObservation :
      String

    vudAbs :
      Float

    vusAbs :
      Float

    vubAbs :
      Float

    vcdAbs :
      Float

    vcsAbs :
      Float

    vcbAbs :
      Float

    vtdAbs :
      Float

    vtsAbs :
      Float

    vtbAbs :
      Float

    pdgComparisonLabel :
      String

    ckmFromPhysicalMassMatrixRecorded :
      Bool

    ckmFromPhysicalMassMatrixRecordedIsTrue :
      ckmFromPhysicalMassMatrixRecorded ≡ true

    physicalCKMMatchesPDG :
      Bool

    physicalCKMMatchesPDGIsFalse :
      physicalCKMMatchesPDG ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List CKMFromPhysicalMassMatrixBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMFromPhysicalMassMatrixBlockers

    promotionFlags :
      List CKMFromPhysicalMassMatrixPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CKMFromPhysicalMassMatrixReceipt public

canonicalCKMFromPhysicalMassMatrixReceipt :
  CKMFromPhysicalMassMatrixReceipt
canonicalCKMFromPhysicalMassMatrixReceipt =
  record
    { status =
        physicalMassMatrixCKMDiagnosticRecorded
    ; massMatrixReceipt =
        Mass.canonicalPhysicalMassMatrixReceipt
    ; massMatrixReceiptIsCanonical =
        refl
    ; diagnosticScript =
        "scripts/check_ckm_from_physical_mass_matrix.py"
    ; scaleObservation =
        "The VEV factor rescales masses but leaves the U_d eigenvectors unchanged"
    ; vudAbs =
        0.6486646808181264
    ; vusAbs =
        0.08976502640934969
    ; vubAbs =
        0.7557621132954777
    ; vcdAbs =
        0.7496905973872525
    ; vcsAbs =
        0.09589115634857552
    ; vcbAbs =
        0.6548044702987887
    ; vtdAbs =
        0.13114167929480824
    ; vtsAbs =
        0.99133603090368
    ; vtbAbs =
        0.007398228428201423
    ; pdgComparisonLabel =
        "Diagnostic |V| is far from PDG-sized CKM targets; the VEV calibration does not repair the eigenbasis"
    ; ckmFromPhysicalMassMatrixRecorded =
        true
    ; ckmFromPhysicalMassMatrixRecordedIsTrue =
        refl
    ; physicalCKMMatchesPDG =
        false
    ; physicalCKMMatchesPDGIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalCKMFromPhysicalMassMatrixBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The CKM matrix from the VEV-calibrated mass matrix is recorded"
        ∷ "Global VEV scaling cannot change the poor diagnostic CKM eigenvectors"
        ∷ "No physical CKM promotion is asserted"
        ∷ []
    }

ckmFromPhysicalMassMatrixDoesNotPromote :
  physicalCKMPromoted canonicalCKMFromPhysicalMassMatrixReceipt ≡ false
ckmFromPhysicalMassMatrixDoesNotPromote =
  refl


module DASHI.Physics.Closure.YukawaNormalisationStructureReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Yukawa normalisation structure receipt.
--
-- This receipt records the requested modular-volume normalisation rule
-- for off-diagonal Yukawa entries.  It is a structure/diagnostic receipt:
-- no physical Yukawa eigenbasis or CKM promotion is constructed here.

data YukawaNormalisationStructureStatus : Set where
  yukawaNormalisationFormulaRecorded :
    YukawaNormalisationStructureStatus

data YukawaNormalisationBlocker : Set where
  missingPhysicalVolumeAuthority :
    YukawaNormalisationBlocker

  missingCertifiedModularIndexComputation :
    YukawaNormalisationBlocker

  missingPhysicalYukawaEigenbasis :
    YukawaNormalisationBlocker

canonicalYukawaNormalisationBlockers :
  List YukawaNormalisationBlocker
canonicalYukawaNormalisationBlockers =
  missingPhysicalVolumeAuthority
  ∷ missingCertifiedModularIndexComputation
  ∷ missingPhysicalYukawaEigenbasis
  ∷ []

data YukawaNormalisationPromotion : Set where

yukawaNormalisationPromotionImpossibleHere :
  YukawaNormalisationPromotion →
  ⊥
yukawaNormalisationPromotionImpossibleHere ()

yukawaNormalisationFormulaLabel : String
yukawaNormalisationFormulaLabel =
  "Y_ij normalisation = vol(X0(Nk))/sqrt(psi(Ni)*psi(Nj))"

sqrtTwentyFourFormulaLabel : String
sqrtTwentyFourFormulaLabel =
  "sqrt24 = sqrt(psi4*psi3), with psi4=6 and psi3=4"

record YukawaNormalisationStructureReceipt : Set where
  field
    status :
      YukawaNormalisationStructureStatus

    normalisationFormula :
      String

    normalisationFormulaIsCanonical :
      normalisationFormula ≡ yukawaNormalisationFormulaLabel

    psi4 :
      Nat

    psi4IsSix :
      psi4 ≡ 6

    psi3 :
      Nat

    psi3IsFour :
      psi3 ≡ 4

    psi4TimesPsi3 :
      Nat

    psi4TimesPsi3IsTwentyFour :
      psi4TimesPsi3 ≡ 24

    sqrt24Formula :
      String

    sqrt24FormulaIsCanonical :
      sqrt24Formula ≡ sqrtTwentyFourFormulaLabel

    sqrt24Approx :
      Float

    volumeNormalisationStructureRecorded :
      Bool

    volumeNormalisationStructureRecordedIsTrue :
      volumeNormalisationStructureRecorded ≡ true

    physicalVolumeAuthorityConstructed :
      Bool

    physicalVolumeAuthorityConstructedIsFalse :
      physicalVolumeAuthorityConstructed ≡ false

    physicalYukawaEigenbasisPromoted :
      Bool

    physicalYukawaEigenbasisPromotedIsFalse :
      physicalYukawaEigenbasisPromoted ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    terminalClaimPromoted :
      Bool

    terminalClaimPromotedIsFalse :
      terminalClaimPromoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    blockers :
      List YukawaNormalisationBlocker

    blockersAreCanonical :
      blockers ≡ canonicalYukawaNormalisationBlockers

    promotionFlags :
      List YukawaNormalisationPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YukawaNormalisationStructureReceipt public

canonicalYukawaNormalisationStructureReceipt :
  YukawaNormalisationStructureReceipt
canonicalYukawaNormalisationStructureReceipt =
  record
    { status =
        yukawaNormalisationFormulaRecorded
    ; normalisationFormula =
        yukawaNormalisationFormulaLabel
    ; normalisationFormulaIsCanonical =
        refl
    ; psi4 =
        6
    ; psi4IsSix =
        refl
    ; psi3 =
        4
    ; psi3IsFour =
        refl
    ; psi4TimesPsi3 =
        24
    ; psi4TimesPsi3IsTwentyFour =
        refl
    ; sqrt24Formula =
        sqrtTwentyFourFormulaLabel
    ; sqrt24FormulaIsCanonical =
        refl
    ; sqrt24Approx =
        4.898979485566356
    ; volumeNormalisationStructureRecorded =
        true
    ; volumeNormalisationStructureRecordedIsTrue =
        refl
    ; physicalVolumeAuthorityConstructed =
        false
    ; physicalVolumeAuthorityConstructedIsFalse =
        refl
    ; physicalYukawaEigenbasisPromoted =
        false
    ; physicalYukawaEigenbasisPromotedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; terminalClaimPromoted =
        false
    ; terminalClaimPromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; blockers =
        canonicalYukawaNormalisationBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The requested vol(X0(Nk))/sqrt(psi(Ni)*psi(Nj)) normalisation is recorded"
        ∷ "The sqrt24 carrier factor is fixed as sqrt(psi4*psi3) with psi4=6 and psi3=4"
        ∷ "This receipt does not construct a physical volume authority, eigenbasis, CKM promotion, terminal claim, or Clay claim"
        ∷ []
    }

yukawaNormalisationDoesNotPromoteCKM :
  physicalCKMPromoted canonicalYukawaNormalisationStructureReceipt ≡ false
yukawaNormalisationDoesNotPromoteCKM =
  refl

yukawaNormalisationDoesNotPromoteTerminal :
  terminalClaimPromoted canonicalYukawaNormalisationStructureReceipt
  ≡
  false
yukawaNormalisationDoesNotPromoteTerminal =
  refl

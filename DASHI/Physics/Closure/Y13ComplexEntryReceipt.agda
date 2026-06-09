module DASHI.Physics.Closure.Y13ComplexEntryReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HeckeCharacterPhaseReceipt as Phase
import DASHI.Physics.Closure.Y13FromBridgeIsogenyReceipt as Bridge

------------------------------------------------------------------------
-- Complex y13 entry surface.

data Y13ComplexEntryStatus : Set where
  y13ComplexEntrySurfaceRecorded :
    Y13ComplexEntryStatus

data Y13ComplexEntryBlocker : Set where
  heckePhaseIsDiagnosticNotPhysical :
    Y13ComplexEntryBlocker

  missingCertifiedComplexYukawaDiagonalisation :
    Y13ComplexEntryBlocker

  missingDHRIntertwinerAuthorityForP2P5 :
    Y13ComplexEntryBlocker

canonicalY13ComplexEntryBlockers :
  List Y13ComplexEntryBlocker
canonicalY13ComplexEntryBlockers =
  heckePhaseIsDiagnosticNotPhysical
  ∷ missingCertifiedComplexYukawaDiagonalisation
  ∷ missingDHRIntertwinerAuthorityForP2P5
  ∷ []

data Y13ComplexEntryPromotion : Set where

y13ComplexEntryPromotionImpossibleHere :
  Y13ComplexEntryPromotion →
  ⊥
y13ComplexEntryPromotionImpossibleHere ()

record Y13ComplexEntryReceipt : Set where
  field
    status :
      Y13ComplexEntryStatus

    bridgeReceipt :
      Bridge.Y13FromBridgeIsogenyReceipt

    bridgeReceiptIsCanonical :
      bridgeReceipt ≡ Bridge.canonicalY13FromBridgeIsogenyReceipt

    phaseReceipt :
      Phase.HeckeCharacterPhaseReceipt

    phaseReceiptIsCanonical :
      phaseReceipt ≡ Phase.canonicalHeckeCharacterPhaseReceipt

    complexEntryFormula :
      String

    magnitude :
      Float

    magnitudeLabel :
      String

    phaseRadians :
      Float

    phaseRadiansLabel :
      String

    realPartLabel :
      String

    imaginaryPartLabel :
      String

    y13ComplexEntryRecorded :
      Bool

    y13ComplexEntryRecordedIsTrue :
      y13ComplexEntryRecorded ≡ true

    cpPhaseFromHeckeCharacterDiagnostic :
      Bool

    cpPhaseFromHeckeCharacterDiagnosticIsTrue :
      cpPhaseFromHeckeCharacterDiagnostic ≡ true

    y13PhysicalValue :
      Bool

    y13PhysicalValueIsFalse :
      y13PhysicalValue ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Y13ComplexEntryBlocker

    blockersAreCanonical :
      blockers ≡ canonicalY13ComplexEntryBlockers

    promotionFlags :
      List Y13ComplexEntryPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Y13ComplexEntryReceipt public

canonicalY13ComplexEntryReceipt :
  Y13ComplexEntryReceipt
canonicalY13ComplexEntryReceipt =
  record
    { status =
        y13ComplexEntrySurfaceRecorded
    ; bridgeReceipt =
        Bridge.canonicalY13FromBridgeIsogenyReceipt
    ; bridgeReceiptIsCanonical =
        refl
    ; phaseReceipt =
        Phase.canonicalHeckeCharacterPhaseReceipt
    ; phaseReceiptIsCanonical =
        refl
    ; complexEntryFormula =
        "(Y_d)13 = (24*pi/sqrt(6)) * exp(i*delta_29), delta_29 = arg((1+2*i*sqrt(7))/(5+2*i))"
    ; magnitude =
        30.781195923884738
    ; magnitudeLabel =
        "|(Y_d)13| ~= 30.781195923884738 before alpha1^3 suppression"
    ; phaseRadians =
        1.003510488600938
    ; phaseRadiansLabel =
        "delta_29 ~= 1.003510488600938 radians"
    ; realPartLabel =
        "Re((Y_d)13) ~= 16.540122 before alpha1^3 suppression"
    ; imaginaryPartLabel =
        "Im((Y_d)13) ~= 25.959707 before alpha1^3 suppression"
    ; y13ComplexEntryRecorded =
        true
    ; y13ComplexEntryRecordedIsTrue =
        refl
    ; cpPhaseFromHeckeCharacterDiagnostic =
        true
    ; cpPhaseFromHeckeCharacterDiagnosticIsTrue =
        refl
    ; y13PhysicalValue =
        false
    ; y13PhysicalValueIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; blockers =
        canonicalY13ComplexEntryBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The complex p2-p5 entry is now specified as a diagnostic surface"
        ∷ "The p=29 phase is not a physical CP-phase derivation"
        ∷ "No physical CKM promotion is asserted"
        ∷ []
    }

y13ComplexEntryIsRecorded :
  y13ComplexEntryRecorded canonicalY13ComplexEntryReceipt ≡ true
y13ComplexEntryIsRecorded =
  refl

y13ComplexEntryDoesNotPromoteCKM :
  physicalCKMPromoted canonicalY13ComplexEntryReceipt ≡ false
y13ComplexEntryDoesNotPromoteCKM =
  refl


module DASHI.Physics.Boundaries.HiggsPDGBoundary where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.HiggsSymmetryBreakingReceipt as Higgs

------------------------------------------------------------------------
-- Higgs / PDG electroweak boundary.
--
-- This module records the empirical constants and the symmetry-breaking
-- consistency shape as a typed boundary.  It does not derive the Higgs
-- mechanism or any W/Z mass law internally.

data HiggsPDGBoundaryStatus : Set where
  boundaryRecordedNoHiggsPromotion :
    HiggsPDGBoundaryStatus

record HiggsPDGBoundary : Setω where
  field
    higgsVEVReceipt :
      Higgs.VHiggsDefinitionalReceipt

    vHiggsGeVTimes100 :
      Nat

    vHiggsGeVTimes100Is24622 :
      vHiggsGeVTimes100 ≡ 24622

    mWGeVTimes100 :
      Nat

    mWGeVTimes100Is80377 :
      mWGeVTimes100 ≡ 80377

    mZGeVTimes100 :
      Nat

    mZGeVTimes100Is91188 :
      mZGeVTimes100 ≡ 91188

    electroweakGenerator :
      String

    electroweakGenerator-v :
      electroweakGenerator ≡ "Q = T3 + Y/2"

    wMassLaw :
      String

    wMassLaw-v :
      wMassLaw ≡ "M_W = (g v) / 2"

    zMassLaw :
      String

    zMassLaw-v :
      zMassLaw ≡ "M_Z = (sqrt(g^2 + g'^2) v) / 2"

    generatorNeutralityOnHiggs :
      Bool

    generatorNeutralityOnHiggsIsTrue :
      generatorNeutralityOnHiggs ≡ true

    physicalConstantsStillImported :
      Bool

    physicalConstantsStillImportedIsFalse :
      physicalConstantsStillImported ≡ false

    boundary :
      List String

open HiggsPDGBoundary public

canonicalHiggsPDGBoundary :
  HiggsPDGBoundary
canonicalHiggsPDGBoundary =
  record
    { higgsVEVReceipt =
        Higgs.canonicalVHiggsDefinitionalReceipt
    ; vHiggsGeVTimes100 =
        24622
    ; vHiggsGeVTimes100Is24622 =
        refl
    ; mWGeVTimes100 =
        80377
    ; mWGeVTimes100Is80377 =
        refl
    ; mZGeVTimes100 =
        91188
    ; mZGeVTimes100Is91188 =
        refl
    ; electroweakGenerator =
        "Q = T3 + Y/2"
    ; electroweakGenerator-v =
        refl
    ; wMassLaw =
        "M_W = (g v) / 2"
    ; wMassLaw-v =
        refl
    ; zMassLaw =
        "M_Z = (sqrt(g^2 + g'^2) v) / 2"
    ; zMassLaw-v =
        refl
    ; generatorNeutralityOnHiggs =
        true
    ; generatorNeutralityOnHiggsIsTrue =
        refl
    ; physicalConstantsStillImported =
        false
    ; physicalConstantsStillImportedIsFalse =
        refl
    ; boundary =
        "The v_Higgs, m_W, and m_Z constants are recorded as imported boundary data"
        ∷ "The electroweak generator is named as Q = T3 + Y/2"
        ∷ "The Higgs neutrality / symmetry-breaking law is a typed consistency target, not a derived theorem"
        ∷ "No internal promotion of W/Z calibration is claimed here"
        ∷ []
    }

record HiggsPDGBoundaryReceipt : Setω where
  field
    boundary :
      HiggsPDGBoundary

    boundaryRecordedAsImportedConstants :
      Bool

    boundaryRecordedAsImportedConstantsIsTrue :
      boundaryRecordedAsImportedConstants ≡ true

    higgsVEVReceiptIsCanonical :
      higgsVEVReceipt boundary
      ≡
      Higgs.canonicalVHiggsDefinitionalReceipt

    physicalConstantsBoundaryOpen :
      Bool

    physicalConstantsBoundaryOpenIsFalse :
      physicalConstantsBoundaryOpen ≡ false

    receiptBoundary :
      List String

open HiggsPDGBoundaryReceipt public

canonicalHiggsPDGBoundaryReceipt :
  HiggsPDGBoundaryReceipt
canonicalHiggsPDGBoundaryReceipt =
  record
    { boundary =
        canonicalHiggsPDGBoundary
    ; boundaryRecordedAsImportedConstants =
        true
    ; boundaryRecordedAsImportedConstantsIsTrue =
        refl
    ; higgsVEVReceiptIsCanonical =
        refl
    ; physicalConstantsBoundaryOpen =
        false
    ; physicalConstantsBoundaryOpenIsFalse =
        refl
    ; receiptBoundary =
        "The PDG-boundary receipt consumes the canonical v_Higgs definitional receipt"
        ∷ "W/Z masses are carried as imported constants, not deduced from the repo"
        ∷ "The electroweak generator consistency law remains a boundary-level constraint"
        ∷ []
    }

canonicalHiggsPDGBoundaryKeepsPhysicalConstantsOpen :
  physicalConstantsStillImported canonicalHiggsPDGBoundary ≡ false
canonicalHiggsPDGBoundaryKeepsPhysicalConstantsOpen =
  refl

canonicalHiggsPDGBoundaryUsesCanonicalVEV :
  higgsVEVReceipt canonicalHiggsPDGBoundary
  ≡
  Higgs.canonicalVHiggsDefinitionalReceipt
canonicalHiggsPDGBoundaryUsesCanonicalVEV =
  refl

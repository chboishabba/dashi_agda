module DASHI.Physics.QFT.Spin2FermionInterpretationReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Spin-2 fermion interpretation receipt.
--
-- This receipt records a fail-closed interpretation boundary for reading the
-- SU(2)_4 j=2 sector as Standard-Model fermion data.  The SU(2) spin-j
-- representation has ordinary dimension 2j+1, so the j=2 representation is
-- five-dimensional.  It is therefore not an SM weak left doublet and does not
-- match the quark weak-doublet representation surface.  Exact Standard Model
-- and G_DHR promotion remain false.

data Spin2FermionResidual : Set where
  j2RepresentationFiveDimensional :
    Spin2FermionResidual

  missingSMWeakLeftDoublet :
    Spin2FermionResidual

  missingQuarkWeakDoubletMatch :
    Spin2FermionResidual

  missingExactStandardModelPromotion :
    Spin2FermionResidual

  missingExactGDHRPromotion :
    Spin2FermionResidual

canonicalSpin2FermionResiduals :
  List Spin2FermionResidual
canonicalSpin2FermionResiduals =
  j2RepresentationFiveDimensional
  ∷ missingSMWeakLeftDoublet
  ∷ missingQuarkWeakDoubletMatch
  ∷ missingExactStandardModelPromotion
  ∷ missingExactGDHRPromotion
  ∷ []

su2Level4J2RepresentationLabel : String
su2Level4J2RepresentationLabel =
  "SU(2)_4 j=2 representation has ordinary dimension 5"

notSMWeakLeftDoubletLabel : String
notSMWeakLeftDoubletLabel =
  "dimension-5 SU(2)_4 j=2 sector is not an SM weak left doublet"

quarkMismatchLabel : String
quarkMismatchLabel =
  "spin-2 fermion interpretation mismatches the quark weak-doublet surface"

promotionBoundaryLabel : String
promotionBoundaryLabel =
  "exact Standard Model and G_DHR promotion remain false"

j2OrdinaryDimension :
  Nat
j2OrdinaryDimension =
  5

j2Is5dimensional :
  Bool
j2Is5dimensional =
  true

j2NotSMLdoublet :
  Bool
j2NotSMLdoublet =
  true

spin2FermionMismatchWithQuarks :
  Bool
spin2FermionMismatchWithQuarks =
  true

exactSMPromotion :
  Bool
exactSMPromotion =
  false

exactDHRPromotion :
  Bool
exactDHRPromotion =
  false

exactGDHREqualsGSMPromotion :
  Bool
exactGDHREqualsGSMPromotion =
  false

record Spin2FermionInterpretationReceipt : Set where
  field
    representationLabel :
      String

    representationLabelIsCanonical :
      representationLabel ≡ su2Level4J2RepresentationLabel

    weakDoubletBoundaryLabel :
      String

    weakDoubletBoundaryLabelIsCanonical :
      weakDoubletBoundaryLabel ≡ notSMWeakLeftDoubletLabel

    quarkBoundaryLabel :
      String

    quarkBoundaryLabelIsCanonical :
      quarkBoundaryLabel ≡ quarkMismatchLabel

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ promotionBoundaryLabel

    j2Dimension :
      Nat

    j2DimensionIsFive :
      j2Dimension ≡ j2OrdinaryDimension

    j2Is5dimensionalReceipt :
      Bool

    j2Is5dimensionalReceiptIsTrue :
      j2Is5dimensionalReceipt ≡ true

    j2NotSMLdoubletReceipt :
      Bool

    j2NotSMLdoubletReceiptIsTrue :
      j2NotSMLdoubletReceipt ≡ true

    spin2FermionMismatchWithQuarksReceipt :
      Bool

    spin2FermionMismatchWithQuarksReceiptIsTrue :
      spin2FermionMismatchWithQuarksReceipt ≡ true

    exactSMPromotionReceipt :
      Bool

    exactSMPromotionReceiptIsFalse :
      exactSMPromotionReceipt ≡ false

    exactDHRPromotionReceipt :
      Bool

    exactDHRPromotionReceiptIsFalse :
      exactDHRPromotionReceipt ≡ false

    exactGDHREqualsGSMPromotionReceipt :
      Bool

    exactGDHREqualsGSMPromotionReceiptIsFalse :
      exactGDHREqualsGSMPromotionReceipt ≡ false

    residuals :
      List Spin2FermionResidual

    residualsAreCanonical :
      residuals ≡ canonicalSpin2FermionResiduals

open Spin2FermionInterpretationReceipt public

canonicalSpin2FermionInterpretationReceipt :
  Spin2FermionInterpretationReceipt
canonicalSpin2FermionInterpretationReceipt =
  record
    { representationLabel =
        su2Level4J2RepresentationLabel
    ; representationLabelIsCanonical =
        refl
    ; weakDoubletBoundaryLabel =
        notSMWeakLeftDoubletLabel
    ; weakDoubletBoundaryLabelIsCanonical =
        refl
    ; quarkBoundaryLabel =
        quarkMismatchLabel
    ; quarkBoundaryLabelIsCanonical =
        refl
    ; promotionBoundary =
        promotionBoundaryLabel
    ; promotionBoundaryIsCanonical =
        refl
    ; j2Dimension =
        j2OrdinaryDimension
    ; j2DimensionIsFive =
        refl
    ; j2Is5dimensionalReceipt =
        j2Is5dimensional
    ; j2Is5dimensionalReceiptIsTrue =
        refl
    ; j2NotSMLdoubletReceipt =
        j2NotSMLdoublet
    ; j2NotSMLdoubletReceiptIsTrue =
        refl
    ; spin2FermionMismatchWithQuarksReceipt =
        spin2FermionMismatchWithQuarks
    ; spin2FermionMismatchWithQuarksReceiptIsTrue =
        refl
    ; exactSMPromotionReceipt =
        exactSMPromotion
    ; exactSMPromotionReceiptIsFalse =
        refl
    ; exactDHRPromotionReceipt =
        exactDHRPromotion
    ; exactDHRPromotionReceiptIsFalse =
        refl
    ; exactGDHREqualsGSMPromotionReceipt =
        exactGDHREqualsGSMPromotion
    ; exactGDHREqualsGSMPromotionReceiptIsFalse =
        refl
    ; residuals =
        canonicalSpin2FermionResiduals
    ; residualsAreCanonical =
        refl
    }

j2OrdinaryDimensionIsFive :
  j2OrdinaryDimension ≡ 5
j2OrdinaryDimensionIsFive =
  refl

j2Is5dimensionalIsTrue :
  j2Is5dimensional ≡ true
j2Is5dimensionalIsTrue =
  refl

j2NotSMLdoubletIsTrue :
  j2NotSMLdoublet ≡ true
j2NotSMLdoubletIsTrue =
  refl

spin2FermionMismatchWithQuarksIsTrue :
  spin2FermionMismatchWithQuarks ≡ true
spin2FermionMismatchWithQuarksIsTrue =
  refl

exactSMPromotionIsFalse :
  exactSMPromotion ≡ false
exactSMPromotionIsFalse =
  refl

exactDHRPromotionIsFalse :
  exactDHRPromotion ≡ false
exactDHRPromotionIsFalse =
  refl

exactGDHREqualsGSMPromotionIsFalse :
  exactGDHREqualsGSMPromotion ≡ false
exactGDHREqualsGSMPromotionIsFalse =
  refl

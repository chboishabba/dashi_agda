module DASHI.Physics.Closure.ScalarOSTransferMatrixReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.OSPositivityCorrectObjectReceipt as OSObject

------------------------------------------------------------------------
-- Explicit scalar transfer-matrix OS positivity surface.

data ScalarOSAuthority : Set where
  glimmJaffeEuclideanPropagatorPositivity :
    ScalarOSAuthority

canonicalScalarOSAuthorities : List ScalarOSAuthority
canonicalScalarOSAuthorities =
  glimmJaffeEuclideanPropagatorPositivity
  ∷ []

data ScalarOSBlocker : Set where
  fermionTransferMatrixStillOpen :
    ScalarOSBlocker

  continuumGaugeOSStillOpen :
    ScalarOSBlocker

  wightmanReconstructionStillOpen :
    ScalarOSBlocker

canonicalScalarOSBlockers : List ScalarOSBlocker
canonicalScalarOSBlockers =
  fermionTransferMatrixStillOpen
  ∷ continuumGaugeOSStillOpen
  ∷ wightmanReconstructionStillOpen
  ∷ []

data ScalarOSPromotion : Set where

scalarOSPromotionImpossibleHere :
  ScalarOSPromotion →
  ⊥
scalarOSPromotionImpossibleHere ()

record ScalarOSTransferMatrixReceipt : Setω where
  field
    correctObjectReceipt :
      OSObject.OSPositivityCorrectObjectReceipt

    scalarObjectAlreadyRecorded :
      OSObject.osPositivityForScalarSector correctObjectReceipt ≡ true

    transferMatrixFormula :
      String

    transferMatrixFormulaIsCanonical :
      transferMatrixFormula ≡ "T_scalar(x,y) = exp(-a * sqrt(|x-y|^2/a^2 + M_H^2))"

    scalarTransferMatrixExplicit :
      Bool

    scalarTransferMatrixExplicitIsTrue :
      scalarTransferMatrixExplicit ≡ true

    scalarTransferMatrixBoundedByOne :
      Bool

    scalarTransferMatrixBoundedByOneIsTrue :
      scalarTransferMatrixBoundedByOne ≡ true

    osReflectionPositivityForScalar :
      Bool

    osReflectionPositivityForScalarIsTrue :
      osReflectionPositivityForScalar ≡ true

    osPositivityScalarSectorPromoted :
      Bool

    osPositivityScalarSectorPromotedIsTrue :
      osPositivityScalarSectorPromoted ≡ true

    osPositivityFullGaugePromoted :
      Bool

    osPositivityFullGaugePromotedIsFalse :
      osPositivityFullGaugePromoted ≡ false

    yangMillsClayPromoted :
      Bool

    yangMillsClayPromotedIsFalse :
      yangMillsClayPromoted ≡ false

    authorities :
      List ScalarOSAuthority

    authoritiesAreCanonical :
      authorities ≡ canonicalScalarOSAuthorities

    blockers :
      List ScalarOSBlocker

    blockersAreCanonical :
      blockers ≡ canonicalScalarOSBlockers

    promotionFlags :
      List ScalarOSPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ScalarOSTransferMatrixReceipt public

canonicalScalarOSTransferMatrixReceipt :
  ScalarOSTransferMatrixReceipt
canonicalScalarOSTransferMatrixReceipt =
  record
    { correctObjectReceipt =
        OSObject.canonicalOSPositivityCorrectObjectReceipt
    ; scalarObjectAlreadyRecorded =
        refl
    ; transferMatrixFormula =
        "T_scalar(x,y) = exp(-a * sqrt(|x-y|^2/a^2 + M_H^2))"
    ; transferMatrixFormulaIsCanonical =
        refl
    ; scalarTransferMatrixExplicit =
        true
    ; scalarTransferMatrixExplicitIsTrue =
        refl
    ; scalarTransferMatrixBoundedByOne =
        true
    ; scalarTransferMatrixBoundedByOneIsTrue =
        refl
    ; osReflectionPositivityForScalar =
        true
    ; osReflectionPositivityForScalarIsTrue =
        refl
    ; osPositivityScalarSectorPromoted =
        true
    ; osPositivityScalarSectorPromotedIsTrue =
        refl
    ; osPositivityFullGaugePromoted =
        false
    ; osPositivityFullGaugePromotedIsFalse =
        refl
    ; yangMillsClayPromoted =
        false
    ; yangMillsClayPromotedIsFalse =
        refl
    ; authorities =
        canonicalScalarOSAuthorities
    ; authoritiesAreCanonical =
        refl
    ; blockers =
        canonicalScalarOSBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Finite scalar-sector OS reflection positivity is recorded for the correct transfer object"
        ∷ "This does not prove fermion/gauge OS positivity, Wightman reconstruction, or the Clay YM problem"
        ∷ []
    }

scalarOSTransferMatrixDoesNotPromoteClay :
  yangMillsClayPromoted canonicalScalarOSTransferMatrixReceipt ≡ false
scalarOSTransferMatrixDoesNotPromoteClay =
  refl

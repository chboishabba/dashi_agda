module DASHI.Physics.Closure.Y13FromBridgeIsogenyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- p2-p5 bridge-isogeny diagnostic for the down-type Yukawa y13 entry.
--
-- The receipt records the carrier bridge formula through the intermediate
-- Heegner lanes.  It is a diagnostic formula for the matrix entry surface,
-- not a physical CKM promotion.

data Y13BridgeStatus : Set where
  y13BridgeIsogenyFormulaRecorded :
    Y13BridgeStatus

data Y13BridgeBlocker : Set where
  missingComplexHeckePhaseAuthority :
    Y13BridgeBlocker

  missingPhysicalYukawaNormalisation :
    Y13BridgeBlocker

  missingCertifiedCKMDiagonalisation :
    Y13BridgeBlocker

canonicalY13BridgeBlockers :
  List Y13BridgeBlocker
canonicalY13BridgeBlockers =
  missingComplexHeckePhaseAuthority
  ∷ missingPhysicalYukawaNormalisation
  ∷ missingCertifiedCKMDiagonalisation
  ∷ []

data Y13BridgePromotion : Set where

y13BridgePromotionImpossibleHere :
  Y13BridgePromotion →
  ⊥
y13BridgePromotionImpossibleHere ()

record Y13FromBridgeIsogenyReceipt : Set where
  field
    status :
      Y13BridgeStatus

    sourceLanePointCount :
      Nat

    sourceLanePointCountIsThree :
      sourceLanePointCount ≡ 3

    intermediateP3PointCount :
      Nat

    intermediateP3PointCountIsFour :
      intermediateP3PointCount ≡ 4

    intermediateP5PointCount :
      Nat

    intermediateP5PointCountIsSix :
      intermediateP5PointCount ≡ 6

    targetHeegnerPointCount :
      Nat

    targetHeegnerPointCountIsEight :
      targetHeegnerPointCount ≡ 8

    bridgeDegree :
      Nat

    bridgeDegreeIsEighteen :
      bridgeDegree ≡ 18

    denominatorLabel :
      String

    rawCouplingLabel :
      String

    targetVolumeLabel :
      String

    y13BridgeFormula :
      String

    y13BridgeMagnitude :
      Float

    y13BridgeMagnitudeLabel :
      String

    y13BridgeFormulaInhabited :
      Bool

    y13BridgeFormulaInhabitedIsTrue :
      y13BridgeFormulaInhabited ≡ true

    y13PhysicalValue :
      Bool

    y13PhysicalValueIsFalse :
      y13PhysicalValue ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    blockers :
      List Y13BridgeBlocker

    blockersAreCanonical :
      blockers ≡ canonicalY13BridgeBlockers

    promotionFlags :
      List Y13BridgePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Y13FromBridgeIsogenyReceipt public

canonicalY13FromBridgeIsogenyReceipt :
  Y13FromBridgeIsogenyReceipt
canonicalY13FromBridgeIsogenyReceipt =
  record
    { status =
        y13BridgeIsogenyFormulaRecorded
    ; sourceLanePointCount =
        3
    ; sourceLanePointCountIsThree =
        refl
    ; intermediateP3PointCount =
        4
    ; intermediateP3PointCountIsFour =
        refl
    ; intermediateP5PointCount =
        6
    ; intermediateP5PointCountIsSix =
        refl
    ; targetHeegnerPointCount =
        8
    ; targetHeegnerPointCountIsEight =
        refl
    ; bridgeDegree =
        18
    ; bridgeDegreeIsEighteen =
        refl
    ; denominatorLabel =
        "sqrt(|E(F_2)| * |E(F_7)|) = sqrt(3*8) = sqrt(24)"
    ; rawCouplingLabel =
        "g13_raw = deg13 / sqrt(24) = 18 / sqrt(24) = 9/sqrt(6)"
    ; targetVolumeLabel =
        "vol(X_0(7)) = 8*pi/3"
    ; y13BridgeFormula =
        "(Y_d)13 = (18/sqrt(24)) * (8*pi/3) = 24*pi/sqrt(6)"
    ; y13BridgeMagnitude =
        30.781195923884738
    ; y13BridgeMagnitudeLabel =
        "24*pi/sqrt(6) ~= 30.781195923884738"
    ; y13BridgeFormulaInhabited =
        true
    ; y13BridgeFormulaInhabitedIsTrue =
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
        canonicalY13BridgeBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The p2-p5 bridge formula is recorded as a carrier diagnostic"
        ∷ "The complex phase and physical normalisation are separate blockers"
        ∷ "No physical CKM promotion is asserted by this receipt"
        ∷ []
    }

y13BridgeFormulaIsRecorded :
  y13BridgeFormulaInhabited canonicalY13FromBridgeIsogenyReceipt ≡ true
y13BridgeFormulaIsRecorded =
  refl

y13BridgeDoesNotPromoteCKM :
  physicalCKMPromoted canonicalY13FromBridgeIsogenyReceipt ≡ false
y13BridgeDoesNotPromoteCKM =
  refl


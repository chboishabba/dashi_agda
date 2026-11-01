module DASHI.Physics.Closure.CheckerboardUltrametricBridgeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import Monster.MUltrametric as MU
import DASHI.Physics.Closure.ReflectionPositivityForWilsonReceipt as RP

------------------------------------------------------------------------
-- Checkerboard/reflection-positivity bridge receipt.
--
-- This records the requested bridge shape between checkerboard Wilson-loop
-- submultiplicativity and carrier ultrametric control.  The only proved
-- inputs consumed here are the carrier mask ultrametric surface and finite
-- Wilson reflection-positivity receipt.  No continuum checkerboard estimate,
-- OS axiom promotion, or Clay Yang-Mills promotion is made.

data CheckerboardUltrametricStatus : Set where
  checkerboardUltrametricBridgeShapeRecordedOnly :
    CheckerboardUltrametricStatus

data CheckerboardUltrametricPiece : Set where
  finiteWilsonReflectionPositivity :
    CheckerboardUltrametricPiece

  carrierMaskUltrametric :
    CheckerboardUltrametricPiece

  ultrametricSmallFieldSector :
    CheckerboardUltrametricPiece

  ultrametricLargeFieldSector :
    CheckerboardUltrametricPiece

  wilsonLoopSubmultiplicativityShape :
    CheckerboardUltrametricPiece

  continuumCheckerboardEstimateOpen :
    CheckerboardUltrametricPiece

canonicalCheckerboardUltrametricPieces :
  List CheckerboardUltrametricPiece
canonicalCheckerboardUltrametricPieces =
  finiteWilsonReflectionPositivity
  ∷ carrierMaskUltrametric
  ∷ ultrametricSmallFieldSector
  ∷ ultrametricLargeFieldSector
  ∷ wilsonLoopSubmultiplicativityShape
  ∷ continuumCheckerboardEstimateOpen
  ∷ []

data UltrametricFieldSplitStatus : Set where
  largeSmallFieldSplitRecordedObligationOpen :
    UltrametricFieldSplitStatus

ultrametricLargeSmallFieldSplitLabel : String
ultrametricLargeSmallFieldSplitLabel =
  "small fields are the ultrametric balls controlled by finite Wilson/reflection-positive estimates; large fields are their complement and require a separate tail suppression estimate before Balaban induction"

data CheckerboardUltrametricPromotion : Set where

checkerboardUltrametricPromotionImpossibleHere :
  CheckerboardUltrametricPromotion →
  ⊥
checkerboardUltrametricPromotionImpossibleHere ()

checkerboardUltrametricStatement : String
checkerboardUltrametricStatement =
  "The checkerboard reflection-positivity estimate is recorded as an ultrametric bridge shape only.  The ultrametric large/small field split is named as an open Balaban-induction obligation; finite Wilson positivity is available, but continuum OS positivity is not promoted."

record CheckerboardUltrametricBridgeReceipt : Setω where
  field
    status :
      CheckerboardUltrametricStatus

    statusIsCanonical :
      status ≡ checkerboardUltrametricBridgeShapeRecordedOnly

    finiteWilsonReflectionReceipt :
      RP.ReflectionPositivityForWilsonReceipt

    finiteWilsonReflectionPositivityAvailable :
      RP.finiteLatticeReflectionPositivityInherited
        finiteWilsonReflectionReceipt
      ≡ true

    finiteWilsonContinuumPositivityStillOpen :
      RP.continuumReflectionPositivityProved finiteWilsonReflectionReceipt
      ≡ false

    carrierMaskUltrametricRecorded :
      Bool

    carrierMaskUltrametricRecordedIsTrue :
      carrierMaskUltrametricRecorded ≡ true

    largeSmallFieldSplitStatus :
      UltrametricFieldSplitStatus

    largeSmallFieldSplitStatusIsOpen :
      largeSmallFieldSplitStatus
      ≡
      largeSmallFieldSplitRecordedObligationOpen

    largeSmallFieldSplitStatement :
      String

    largeSmallFieldSplitStatementIsCanonical :
      largeSmallFieldSplitStatement ≡ ultrametricLargeSmallFieldSplitLabel

    smallFieldSectorRecorded :
      Bool

    smallFieldSectorRecordedIsTrue :
      smallFieldSectorRecorded ≡ true

    largeFieldTailEstimateProved :
      Bool

    largeFieldTailEstimateProvedIsFalse :
      largeFieldTailEstimateProved ≡ false

    checkerboardSubmultiplicativityShapeRecorded :
      Bool

    checkerboardSubmultiplicativityShapeRecordedIsTrue :
      checkerboardSubmultiplicativityShapeRecorded ≡ true

    ultrametricToGaugeFieldsConstructed :
      Bool

    ultrametricToGaugeFieldsConstructedIsFalse :
      ultrametricToGaugeFieldsConstructed ≡ false

    continuumCheckerboardEstimateProved :
      Bool

    continuumCheckerboardEstimateProvedIsFalse :
      continuumCheckerboardEstimateProved ≡ false

    osReflectionPositivityPromoted :
      Bool

    osReflectionPositivityPromotedIsFalse :
      osReflectionPositivityPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    pieces :
      List CheckerboardUltrametricPiece

    piecesAreCanonical :
      pieces ≡ canonicalCheckerboardUltrametricPieces

    promotionFlags :
      List CheckerboardUltrametricPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ checkerboardUltrametricStatement

    receiptBoundary :
      List String

open CheckerboardUltrametricBridgeReceipt public

canonicalCheckerboardUltrametricBridgeReceipt :
  CheckerboardUltrametricBridgeReceipt
canonicalCheckerboardUltrametricBridgeReceipt =
  record
    { status =
        checkerboardUltrametricBridgeShapeRecordedOnly
    ; statusIsCanonical =
        refl
    ; finiteWilsonReflectionReceipt =
        RP.canonicalReflectionPositivityForWilsonReceipt
    ; finiteWilsonReflectionPositivityAvailable =
        refl
    ; finiteWilsonContinuumPositivityStillOpen =
        refl
    ; carrierMaskUltrametricRecorded =
        true
    ; carrierMaskUltrametricRecordedIsTrue =
        refl
    ; largeSmallFieldSplitStatus =
        largeSmallFieldSplitRecordedObligationOpen
    ; largeSmallFieldSplitStatusIsOpen =
        refl
    ; largeSmallFieldSplitStatement =
        ultrametricLargeSmallFieldSplitLabel
    ; largeSmallFieldSplitStatementIsCanonical =
        refl
    ; smallFieldSectorRecorded =
        true
    ; smallFieldSectorRecordedIsTrue =
        refl
    ; largeFieldTailEstimateProved =
        false
    ; largeFieldTailEstimateProvedIsFalse =
        refl
    ; checkerboardSubmultiplicativityShapeRecorded =
        true
    ; checkerboardSubmultiplicativityShapeRecordedIsTrue =
        refl
    ; ultrametricToGaugeFieldsConstructed =
        false
    ; ultrametricToGaugeFieldsConstructedIsFalse =
        refl
    ; continuumCheckerboardEstimateProved =
        false
    ; continuumCheckerboardEstimateProvedIsFalse =
        refl
    ; osReflectionPositivityPromoted =
        false
    ; osReflectionPositivityPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; pieces =
        canonicalCheckerboardUltrametricPieces
    ; piecesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        checkerboardUltrametricStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Monster.MUltrametric.UMask supplies the carrier mask ultrametric surface"
        ∷ "ReflectionPositivityForWilsonReceipt supplies finite Wilson reflection positivity"
        ∷ "The ultrametric small-field sector is only the finite carrier ball controlled by existing estimates"
        ∷ "The ultrametric large-field sector still needs a tail-suppression estimate uniform enough for Balaban induction"
        ∷ "The checkerboard/Wilson-loop inequality is recorded only as a bridge shape"
        ∷ "No gauge-field ultrametric extension or continuum OS3 proof is constructed"
        ∷ "Keeps all Clay Yang-Mills promotion flags false"
        ∷ []
    }

checkerboardUltrametricCarrierMaskSurface :
  Bool
checkerboardUltrametricCarrierMaskSurface =
  true

checkerboardUltrametricCarrierMaskSurfaceIsRecorded :
  checkerboardUltrametricCarrierMaskSurface ≡ true
checkerboardUltrametricCarrierMaskSurfaceIsRecorded =
  refl

checkerboardUltrametricKeepsClayFalse :
  clayYangMillsPromoted canonicalCheckerboardUltrametricBridgeReceipt
  ≡ false
checkerboardUltrametricKeepsClayFalse =
  refl

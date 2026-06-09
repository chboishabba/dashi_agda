module DASHI.Physics.Closure.MillenniumTowerYangMillsInstanceReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.MillenniumTowerSchemaReceipt as Schema
import DASHI.Physics.Closure.ContinuumClayMassGapReceiptObligation as ClayGap
import DASHI.Physics.Closure.BalabanRGMassGapReceiptSurface as Balaban
import DASHI.Physics.Closure.YangMillsFieldEquationReceipt as YM
import DASHI.Physics.Closure.YangMillsMassGapBoundary as YMGap
import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as ClayTarget

------------------------------------------------------------------------
-- Yang-Mills instance of the shared tower schema.
--
-- The finite local carrier gap and finite field-equation receipts inhabit
-- T0/T1/T2.  The continuum Yang-Mills construction, OS/reflection-positive
-- lift, and Clay mass-gap acceptance remain explicit T3/T4 blockers.

record MillenniumTowerYangMillsInstanceReceipt : Setω where
  field
    schema :
      Schema.MillenniumTowerSchemaReceipt

    schemaIsCanonical :
      schema ≡ Schema.canonicalMillenniumTowerSchemaReceipt

    localFiniteMassGapSurface :
      Balaban.BalabanRGMassGapReceiptSurface

    finiteFieldEquationReceipt :
      YM.YMSFGCPureZeroCurrentFiniteReceipt

    yangMillsFieldEquationReceipt :
      YM.YangMillsFieldEquationReceipt

    yangMillsFieldEquationReceiptSelected :
      Bool

    yangMillsFieldEquationReceiptSelectedIsTrue :
      yangMillsFieldEquationReceiptSelected ≡ true

    yangMillsMassGapBoundaryReceipt :
      YMGap.YangMillsMassGapBoundaryReceipt

    yangMillsMassGapBoundaryReceiptSelected :
      Bool

    yangMillsMassGapBoundaryReceiptSelectedIsTrue :
      yangMillsMassGapBoundaryReceiptSelected ≡ true

    clayCompositionObligation :
      ClayGap.ContinuumClayMassGapReceiptObligation

    carrierOSWightmanClosureTarget :
      ClayTarget.CarrierOSPositivityAndWightmanTargetReceipt

    carrierOSPositivityConstructedFalse :
      ClayTarget.osPositivityConstructed carrierOSWightmanClosureTarget
      ≡
      false

    carrierUniformGapConstructedFalse :
      ClayTarget.uniformDepthIndependentGapConstructed
        carrierOSWightmanClosureTarget
      ≡
      false

    carrierWightmanReconstructionAppliedFalse :
      ClayTarget.wightmanReconstructionApplied carrierOSWightmanClosureTarget
      ≡
      false

    finiteControlRecorded :
      Bool

    finiteControlRecordedIsTrue :
      finiteControlRecorded ≡ true

    depthFamilyRecorded :
      Bool

    depthFamilyRecordedIsTrue :
      depthFamilyRecorded ≡ true

    liftAttemptRecorded :
      Bool

    liftAttemptRecordedIsTrue :
      liftAttemptRecorded ≡ true

    localFiniteCarrierGapAvailable :
      Bool

    localFiniteCarrierGapAvailableIsTrue :
      localFiniteCarrierGapAvailable ≡ true

    continuumMassGapPromoted :
      Bool

    continuumMassGapPromotedIsFalse :
      continuumMassGapPromoted ≡ false

    yangMillsClosurePromoted :
      Bool

    yangMillsClosurePromotedIsFalse :
      yangMillsClosurePromoted ≡ false

    yangMillsMassGapPromoted :
      Bool

    yangMillsMassGapPromotedIsFalse :
      yangMillsMassGapPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    instanceBoundary :
      List String

open MillenniumTowerYangMillsInstanceReceipt public

canonicalMillenniumTowerYangMillsInstanceReceipt :
  MillenniumTowerYangMillsInstanceReceipt
canonicalMillenniumTowerYangMillsInstanceReceipt =
  record
    { schema =
        Schema.canonicalMillenniumTowerSchemaReceipt
    ; schemaIsCanonical =
        refl
    ; localFiniteMassGapSurface =
        Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; finiteFieldEquationReceipt =
        YM.canonicalYMSFGCPureZeroCurrentFiniteReceipt
    ; yangMillsFieldEquationReceipt =
        YM.canonicalYangMillsFieldEquationReceipt
    ; yangMillsFieldEquationReceiptSelected =
        true
    ; yangMillsFieldEquationReceiptSelectedIsTrue =
        refl
    ; yangMillsMassGapBoundaryReceipt =
        YMGap.canonicalYangMillsMassGapBoundaryReceipt
    ; yangMillsMassGapBoundaryReceiptSelected =
        true
    ; yangMillsMassGapBoundaryReceiptSelectedIsTrue =
        refl
    ; clayCompositionObligation =
        ClayGap.canonicalContinuumClayMassGapReceiptObligation
    ; carrierOSWightmanClosureTarget =
        ClayTarget.canonicalCarrierOSPositivityAndWightmanTargetReceipt
    ; carrierOSPositivityConstructedFalse =
        refl
    ; carrierUniformGapConstructedFalse =
        refl
    ; carrierWightmanReconstructionAppliedFalse =
        refl
    ; finiteControlRecorded =
        true
    ; finiteControlRecordedIsTrue =
        refl
    ; depthFamilyRecorded =
        true
    ; depthFamilyRecordedIsTrue =
        refl
    ; liftAttemptRecorded =
        true
    ; liftAttemptRecordedIsTrue =
        refl
    ; localFiniteCarrierGapAvailable =
        Balaban.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromoted
          Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; localFiniteCarrierGapAvailableIsTrue =
        Balaban.BalabanRGMassGapReceiptSurface.localFiniteCarrierSpectralGapPromotedIsTrue
          Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; continuumMassGapPromoted =
        Balaban.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHI
          Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; continuumMassGapPromotedIsFalse =
        Balaban.BalabanRGMassGapReceiptSurface.continuumMassGapPromotedByDASHIIsFalse
          Balaban.canonicalBalabanRGMassGapReceiptSurface
    ; yangMillsClosurePromoted =
        YM.YangMillsFieldEquationReceipt.yangMillsClosurePromoted
          YM.canonicalYangMillsFieldEquationReceipt
    ; yangMillsClosurePromotedIsFalse =
        refl
    ; yangMillsMassGapPromoted =
        YMGap.YangMillsMassGapBoundaryReceipt.massGapPromoted
          YMGap.canonicalYangMillsMassGapBoundaryReceipt
    ; yangMillsMassGapPromotedIsFalse =
        YMGap.YangMillsMassGapBoundaryReceipt.massGapPromotedIsFalse
          YMGap.canonicalYangMillsMassGapBoundaryReceipt
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; instanceBoundary =
        "T0 finiteControl: Balaban-style local finite carrier spectral-gap surface is inhabited"
        ∷ "T1 depthFamily: depth-indexed finite carrier Yang-Mills receipts are consumed through the existing mass-gap and field-equation surfaces"
        ∷ "T2 liftAttempt: finite zero-current D star F = J lane is recorded without strict real or continuum promotion"
        ∷ "The named YangMillsMassGapBoundaryReceipt and YangMillsFieldEquationReceipt are selected as the YM instance surfaces"
        ∷ "CarrierOSPositivityAndWightmanTargetReceipt records OS positivity, a uniform gap, and Wightman reconstruction as open hard targets"
        ∷ "T3 continuumObligation: continuum Yang-Mills construction and OS/reflection-positive lift remain open"
        ∷ "T4 authorityBoundary: Clay Yang-Mills mass-gap acceptance remains false"
        ∷ []
    }

millenniumTowerYangMillsNoClayPromotion :
  clayYangMillsPromoted canonicalMillenniumTowerYangMillsInstanceReceipt
  ≡
  false
millenniumTowerYangMillsNoClayPromotion =
  refl

millenniumTowerYangMillsFieldEquationNoPromotion :
  yangMillsClosurePromoted canonicalMillenniumTowerYangMillsInstanceReceipt
  ≡
  false
millenniumTowerYangMillsFieldEquationNoPromotion =
  refl

millenniumTowerYangMillsMassGapNoPromotion :
  yangMillsMassGapPromoted canonicalMillenniumTowerYangMillsInstanceReceipt
  ≡
  false
millenniumTowerYangMillsMassGapNoPromotion =
  refl

module DASHI.Physics.Closure.CarrierSchwingerFunctionCauchyReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Carrier Schwinger-function Cauchy receipt.
--
-- O/R/C/S/L/P/G/F surface:
-- This receipt records the bounded carrier theorem surface only.  The
-- intended local statement is Cauchy convergence of carrier Schwinger
-- functions in the carrier norm from ultrametric decorrelation,
-- overlap-domination, and an explicit finite carrier measure input.  The
-- receipt does not use a mass gap as an input and does not lift the result to
-- S' distributions without Gate 3.  Spectral-measure convergence, continuum
-- Yang-Mills, Wightman reconstruction, and Clay promotion remain false/open.

data CarrierSchwingerCauchyInput : Set where
  finiteCarrierMeasureInput :
    CarrierSchwingerCauchyInput

  ultrametricDecorrelationInput :
    CarrierSchwingerCauchyInput

  overlapDominationInput :
    CarrierSchwingerCauchyInput

  carrierNormInput :
    CarrierSchwingerCauchyInput

canonicalCarrierSchwingerCauchyInputs :
  List CarrierSchwingerCauchyInput
canonicalCarrierSchwingerCauchyInputs =
  finiteCarrierMeasureInput
  ∷ ultrametricDecorrelationInput
  ∷ overlapDominationInput
  ∷ carrierNormInput
  ∷ []

data CarrierSchwingerCauchyStatus : Set where
  carrierNormCauchySurfaceRecorded :
    CarrierSchwingerCauchyStatus

  inequalityRecordedAsReceiptSurface :
    CarrierSchwingerCauchyStatus

data CarrierSchwingerCauchyBlocker : Set where
  gate3DistributionLiftMissing :
    CarrierSchwingerCauchyBlocker

  spectralMeasureConvergenceOpen :
    CarrierSchwingerCauchyBlocker

  continuumYangMillsConstructionOpen :
    CarrierSchwingerCauchyBlocker

  wightmanReconstructionOpen :
    CarrierSchwingerCauchyBlocker

  clayYangMillsPromotionBlocked :
    CarrierSchwingerCauchyBlocker

canonicalCarrierSchwingerCauchyBlockers :
  List CarrierSchwingerCauchyBlocker
canonicalCarrierSchwingerCauchyBlockers =
  gate3DistributionLiftMissing
  ∷ spectralMeasureConvergenceOpen
  ∷ continuumYangMillsConstructionOpen
  ∷ wightmanReconstructionOpen
  ∷ clayYangMillsPromotionBlocked
  ∷ []

data CarrierSchwingerContinuumPromotion : Set where

carrierSchwingerContinuumPromotionImpossibleHere :
  CarrierSchwingerContinuumPromotion →
  ⊥
carrierSchwingerContinuumPromotionImpossibleHere ()

carrierSchwingerCauchyInequalityLabel : String
carrierSchwingerCauchyInequalityLabel =
  "For carrier Schwinger functions S_k and S_l, ||S_k - S_l||_carrier is bounded by the ultrametric decorrelation tail plus the overlap-domination error over the explicit finite carrier measure."

carrierSchwingerCauchyStatement : String
carrierSchwingerCauchyStatement =
  "Carrier Schwinger-function Cauchy convergence is recorded only in carrier norm from finite carrier measure, ultrametric decorrelation, and overlap domination.  No mass-gap input, Gate3 S' lift, spectral-measure convergence, continuum YM, or Clay promotion is supplied."

record CarrierSchwingerFunctionCauchyReceipt : Setω where
  field
    status :
      CarrierSchwingerCauchyStatus

    statusIsCarrierSurface :
      status ≡ carrierNormCauchySurfaceRecorded

    inequalityStatus :
      CarrierSchwingerCauchyStatus

    inequalityStatusIsReceiptSurface :
      inequalityStatus ≡ inequalityRecordedAsReceiptSurface

    canonicalInputs :
      List CarrierSchwingerCauchyInput

    canonicalInputsAreExact :
      canonicalInputs ≡ canonicalCarrierSchwingerCauchyInputs

    finiteCarrierMeasureExplicit :
      Bool

    finiteCarrierMeasureExplicitIsTrue :
      finiteCarrierMeasureExplicit ≡ true

    ultrametricDecorrelationInputRecorded :
      Bool

    ultrametricDecorrelationInputRecordedIsTrue :
      ultrametricDecorrelationInputRecorded ≡ true

    overlapDominationInputRecorded :
      Bool

    overlapDominationInputRecordedIsTrue :
      overlapDominationInputRecorded ≡ true

    carrierNormCauchySurfaceRecordedFlag :
      Bool

    carrierNormCauchySurfaceRecordedFlagIsTrue :
      carrierNormCauchySurfaceRecordedFlag ≡ true

    massGapUsedAsInput :
      Bool

    massGapUsedAsInputIsFalse :
      massGapUsedAsInput ≡ false

    inequalityString :
      String

    inequalityStringIsCanonical :
      inequalityString ≡ carrierSchwingerCauchyInequalityLabel

    exactNumericInequalityFormalizedHere :
      Bool

    exactNumericInequalityFormalizedHereIsFalse :
      exactNumericInequalityFormalizedHere ≡ false

    blockers :
      List CarrierSchwingerCauchyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCarrierSchwingerCauchyBlockers

    gate3DistributionLiftConstructed :
      Bool

    gate3DistributionLiftConstructedIsFalse :
      gate3DistributionLiftConstructed ≡ false

    liftToSPrimeConstructed :
      Bool

    liftToSPrimeConstructedIsFalse :
      liftToSPrimeConstructed ≡ false

    spectralMeasureConvergenceConstructed :
      Bool

    spectralMeasureConvergenceConstructedIsFalse :
      spectralMeasureConvergenceConstructed ≡ false

    continuumYangMillsConstructed :
      Bool

    continuumYangMillsConstructedIsFalse :
      continuumYangMillsConstructed ≡ false

    wightmanReconstructionConstructed :
      Bool

    wightmanReconstructionConstructedIsFalse :
      wightmanReconstructionConstructed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    notes :
      List String

canonicalCarrierSchwingerFunctionCauchyReceipt :
  CarrierSchwingerFunctionCauchyReceipt
canonicalCarrierSchwingerFunctionCauchyReceipt = record
  { status =
      carrierNormCauchySurfaceRecorded
  ; statusIsCarrierSurface =
      refl
  ; inequalityStatus =
      inequalityRecordedAsReceiptSurface
  ; inequalityStatusIsReceiptSurface =
      refl
  ; canonicalInputs =
      canonicalCarrierSchwingerCauchyInputs
  ; canonicalInputsAreExact =
      refl
  ; finiteCarrierMeasureExplicit =
      true
  ; finiteCarrierMeasureExplicitIsTrue =
      refl
  ; ultrametricDecorrelationInputRecorded =
      true
  ; ultrametricDecorrelationInputRecordedIsTrue =
      refl
  ; overlapDominationInputRecorded =
      true
  ; overlapDominationInputRecordedIsTrue =
      refl
  ; carrierNormCauchySurfaceRecordedFlag =
      true
  ; carrierNormCauchySurfaceRecordedFlagIsTrue =
      refl
  ; massGapUsedAsInput =
      false
  ; massGapUsedAsInputIsFalse =
      refl
  ; inequalityString =
      carrierSchwingerCauchyInequalityLabel
  ; inequalityStringIsCanonical =
      refl
  ; exactNumericInequalityFormalizedHere =
      false
  ; exactNumericInequalityFormalizedHereIsFalse =
      refl
  ; blockers =
      canonicalCarrierSchwingerCauchyBlockers
  ; blockersAreCanonical =
      refl
  ; gate3DistributionLiftConstructed =
      false
  ; gate3DistributionLiftConstructedIsFalse =
      refl
  ; liftToSPrimeConstructed =
      false
  ; liftToSPrimeConstructedIsFalse =
      refl
  ; spectralMeasureConvergenceConstructed =
      false
  ; spectralMeasureConvergenceConstructedIsFalse =
      refl
  ; continuumYangMillsConstructed =
      false
  ; continuumYangMillsConstructedIsFalse =
      refl
  ; wightmanReconstructionConstructed =
      false
  ; wightmanReconstructionConstructedIsFalse =
      refl
  ; clayYangMillsPromoted =
      false
  ; clayYangMillsPromotedIsFalse =
      refl
  ; notes =
      "The inequality is recorded as a receipt-surface string, not as a numeric theorem in this file"
      ∷ "The carrier Cauchy surface uses finite carrier measure, ultrametric decorrelation, and overlap domination inputs"
      ∷ "Mass gap is deliberately not an input to this receipt"
      ∷ "Gate3 is required before any lift to S' distributions"
      ∷ "Spectral-measure convergence, continuum YM, Wightman reconstruction, and Clay promotion remain false"
      ∷ []
  }

canonicalCarrierSchwingerCauchyNoMassGapInput :
  CarrierSchwingerFunctionCauchyReceipt.massGapUsedAsInput
    canonicalCarrierSchwingerFunctionCauchyReceipt
  ≡
  false
canonicalCarrierSchwingerCauchyNoMassGapInput =
  CarrierSchwingerFunctionCauchyReceipt.massGapUsedAsInputIsFalse
    canonicalCarrierSchwingerFunctionCauchyReceipt

canonicalCarrierSchwingerCauchyNoGate3Lift :
  CarrierSchwingerFunctionCauchyReceipt.liftToSPrimeConstructed
    canonicalCarrierSchwingerFunctionCauchyReceipt
  ≡
  false
canonicalCarrierSchwingerCauchyNoGate3Lift =
  CarrierSchwingerFunctionCauchyReceipt.liftToSPrimeConstructedIsFalse
    canonicalCarrierSchwingerFunctionCauchyReceipt

canonicalCarrierSchwingerCauchyNoContinuumYM :
  CarrierSchwingerFunctionCauchyReceipt.continuumYangMillsConstructed
    canonicalCarrierSchwingerFunctionCauchyReceipt
  ≡
  false
canonicalCarrierSchwingerCauchyNoContinuumYM =
  CarrierSchwingerFunctionCauchyReceipt.continuumYangMillsConstructedIsFalse
    canonicalCarrierSchwingerFunctionCauchyReceipt

canonicalCarrierSchwingerCauchyNoClayPromotion :
  CarrierSchwingerFunctionCauchyReceipt.clayYangMillsPromoted
    canonicalCarrierSchwingerFunctionCauchyReceipt
  ≡
  false
canonicalCarrierSchwingerCauchyNoClayPromotion =
  CarrierSchwingerFunctionCauchyReceipt.clayYangMillsPromotedIsFalse
    canonicalCarrierSchwingerFunctionCauchyReceipt

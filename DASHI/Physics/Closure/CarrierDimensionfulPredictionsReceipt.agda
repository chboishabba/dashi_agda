module DASHI.Physics.Closure.CarrierDimensionfulPredictionsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.CarrierScaleFromHeegnerReceipt as Scale
import DASHI.Physics.Closure.VEVAsPDGInputReceipt as VEV

data CarrierDimensionfulPredictionsStatus : Set where
  dimensionfulPredictionsRequireExternalAnchor :
    CarrierDimensionfulPredictionsStatus

data CarrierDimensionfulPredictionTarget : Set where
  massGapScalePrediction :
    CarrierDimensionfulPredictionTarget

  physicalMassMatrixPrediction :
    CarrierDimensionfulPredictionTarget

  qcdScalePrediction :
    CarrierDimensionfulPredictionTarget

  physicalRateOrCrossSectionPrediction :
    CarrierDimensionfulPredictionTarget

canonicalDimensionfulPredictionTargets :
  List CarrierDimensionfulPredictionTarget
canonicalDimensionfulPredictionTargets =
  massGapScalePrediction
  ∷ physicalMassMatrixPrediction
  ∷ qcdScalePrediction
  ∷ physicalRateOrCrossSectionPrediction
  ∷ []

data CarrierDimensionfulPredictionBlocker : Set where
  missingExternalUnitAnchor :
    CarrierDimensionfulPredictionBlocker

  missingLambdaQCDAnchor :
    CarrierDimensionfulPredictionBlocker

  missingCarrierDerivedVEVAnchor :
    CarrierDimensionfulPredictionBlocker

  missingRunningScaleConvention :
    CarrierDimensionfulPredictionBlocker

  missingContinuumPhysicalCalibration :
    CarrierDimensionfulPredictionBlocker

canonicalCarrierDimensionfulPredictionBlockers :
  List CarrierDimensionfulPredictionBlocker
canonicalCarrierDimensionfulPredictionBlockers =
  missingExternalUnitAnchor
  ∷ missingLambdaQCDAnchor
  ∷ missingCarrierDerivedVEVAnchor
  ∷ missingRunningScaleConvention
  ∷ missingContinuumPhysicalCalibration
  ∷ []

data CarrierDimensionfulPredictionPromotion : Set where

carrierDimensionfulPredictionPromotionImpossibleHere :
  CarrierDimensionfulPredictionPromotion →
  ⊥
carrierDimensionfulPredictionPromotionImpossibleHere ()

dimensionfulPredictionBoundaryStatement : String
dimensionfulPredictionBoundaryStatement =
  "Carrier formulas are dimensionless until an external physical anchor such as Lambda_QCD, a lattice spacing, or the PDG VEV is supplied."

record CarrierDimensionfulPredictionsReceipt : Setω where
  field
    status :
      CarrierDimensionfulPredictionsStatus

    scaleReceipt :
      Scale.CarrierScaleFromHeegnerReceipt

    dimensionlessCarrierScaleRecorded :
      Scale.dimensionlessCarrierScaleRecorded scaleReceipt ≡ true

    dimensionfulCarrierScaleStillOpen :
      Scale.dimensionfulCarrierScaleDerived scaleReceipt ≡ false

    qcdScaleAnchorStillOpen :
      Scale.qcdScaleAnchorDerived scaleReceipt ≡ false

    vevReceipt :
      VEV.VEVAsPDGInputReceipt

    pdgVEVRecordedOnlyAsInput :
      VEV.pdgVEVInputRecorded vevReceipt ≡ true

    higgsVEVDerivationStillFalse :
      VEV.higgsVEVDerivedFromCarrier vevReceipt ≡ false

    dimensionlessCarrierPredictionsRecorded :
      Bool

    dimensionlessCarrierPredictionsRecordedIsTrue :
      dimensionlessCarrierPredictionsRecorded ≡ true

    externalAnchorRequired :
      Bool

    externalAnchorRequiredIsTrue :
      externalAnchorRequired ≡ true

    dimensionfulMassGapPredicted :
      Bool

    dimensionfulMassGapPredictedIsFalse :
      dimensionfulMassGapPredicted ≡ false

    physicalMassPredictedWithoutVEV :
      Bool

    physicalMassPredictedWithoutVEVIsFalse :
      physicalMassPredictedWithoutVEV ≡ false

    higgsVEVDerivationPromoted :
      Bool

    higgsVEVDerivationPromotedIsFalse :
      higgsVEVDerivationPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalPhysicalPredictionPromoted :
      Bool

    terminalPhysicalPredictionPromotedIsFalse :
      terminalPhysicalPredictionPromoted ≡ false

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ dimensionfulPredictionBoundaryStatement

    predictionTargets :
      List CarrierDimensionfulPredictionTarget

    predictionTargetsAreCanonical :
      predictionTargets ≡ canonicalDimensionfulPredictionTargets

    blockers :
      List CarrierDimensionfulPredictionBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCarrierDimensionfulPredictionBlockers

    promotionFlags :
      List CarrierDimensionfulPredictionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CarrierDimensionfulPredictionsReceipt public

canonicalCarrierDimensionfulPredictionsReceipt :
  CarrierDimensionfulPredictionsReceipt
canonicalCarrierDimensionfulPredictionsReceipt =
  record
    { status =
        dimensionfulPredictionsRequireExternalAnchor
    ; scaleReceipt =
        Scale.canonicalCarrierScaleFromHeegnerReceipt
    ; dimensionlessCarrierScaleRecorded =
        refl
    ; dimensionfulCarrierScaleStillOpen =
        refl
    ; qcdScaleAnchorStillOpen =
        refl
    ; vevReceipt =
        VEV.canonicalVEVAsPDGInputReceipt
    ; pdgVEVRecordedOnlyAsInput =
        refl
    ; higgsVEVDerivationStillFalse =
        refl
    ; dimensionlessCarrierPredictionsRecorded =
        true
    ; dimensionlessCarrierPredictionsRecordedIsTrue =
        refl
    ; externalAnchorRequired =
        true
    ; externalAnchorRequiredIsTrue =
        refl
    ; dimensionfulMassGapPredicted =
        false
    ; dimensionfulMassGapPredictedIsFalse =
        refl
    ; physicalMassPredictedWithoutVEV =
        false
    ; physicalMassPredictedWithoutVEVIsFalse =
        refl
    ; higgsVEVDerivationPromoted =
        false
    ; higgsVEVDerivationPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalPhysicalPredictionPromoted =
        false
    ; terminalPhysicalPredictionPromotedIsFalse =
        refl
    ; boundaryStatement =
        dimensionfulPredictionBoundaryStatement
    ; boundaryStatementIsCanonical =
        refl
    ; predictionTargets =
        canonicalDimensionfulPredictionTargets
    ; predictionTargetsAreCanonical =
        refl
    ; blockers =
        canonicalCarrierDimensionfulPredictionBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Carrier depth and Heegner formulas record dimensionless scale data only"
        ∷ "Dimensionful predictions require an external anchor such as Lambda_QCD, a lattice spacing, or the PDG VEV"
        ∷ "No dimensionful mass-gap, physical mass, Higgs VEV, or terminal physical prediction is promoted"
        ∷ []
    }

dimensionfulPredictionNeedsExternalAnchor :
  externalAnchorRequired canonicalCarrierDimensionfulPredictionsReceipt ≡ true
dimensionfulPredictionNeedsExternalAnchor =
  refl

dimensionfulMassGapPredictionStillFalse :
  dimensionfulMassGapPredicted
    canonicalCarrierDimensionfulPredictionsReceipt ≡ false
dimensionfulMassGapPredictionStillFalse =
  refl

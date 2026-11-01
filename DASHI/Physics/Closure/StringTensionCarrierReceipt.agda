module DASHI.Physics.Closure.StringTensionCarrierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.StrongCouplingExpansionReceipt as Strong

data StringTensionInput : Set where
  suTwoWilsonStrongCoupling :
    StringTensionInput

  carrierBetaAlphaOne :
    StringTensionInput

  rectangularWilsonLoopAreaLaw :
    StringTensionInput

  carrierUnitsOnly :
    StringTensionInput

canonicalStringTensionInputs : List StringTensionInput
canonicalStringTensionInputs =
  suTwoWilsonStrongCoupling
  ∷ carrierBetaAlphaOne
  ∷ rectangularWilsonLoopAreaLaw
  ∷ carrierUnitsOnly
  ∷ []

data StringTensionBoundary : Set where
  dimensionfulScaleOpen :
    StringTensionBoundary

  vevCalibrationOpen :
    StringTensionBoundary

  continuumLimitNotEstablished :
    StringTensionBoundary

canonicalStringTensionBoundaries :
  List StringTensionBoundary
canonicalStringTensionBoundaries =
  dimensionfulScaleOpen
  ∷ vevCalibrationOpen
  ∷ continuumLimitNotEstablished
  ∷ []

data StringTensionPromotion : Set where

stringTensionPromotionImpossibleHere :
  StringTensionPromotion →
  ⊥
stringTensionPromotionImpossibleHere ()

stringTensionFormulaLabel : String
stringTensionFormulaLabel =
  "sigma = -log(beta/(2 N^2)) + O(beta^2); for SU(2) and beta=alpha1, sigma = -log(alpha1/8)"

carrierStringTensionApproxLabel : String
carrierStringTensionApproxLabel =
  "sigma ~= 5.27 in carrier units"

carrierMassGapApproxLabel : String
carrierMassGapApproxLabel =
  "m_gap ~= sqrt(sigma) ~= 2.30 in carrier units"

record StringTensionCarrierReceipt : Setω where
  field
    strongCouplingReceipt :
      Strong.StrongCouplingExpansionReceipt

    strongCouplingRegime :
      Strong.strongCouplingRegime strongCouplingReceipt ≡ true

    strongCouplingKeepsClayFalse :
      Strong.clayYangMillsPromoted strongCouplingReceipt ≡ false

    stringTensionFormula :
      String

    stringTensionFormulaIsCanonical :
      stringTensionFormula ≡ stringTensionFormulaLabel

    carrierStringTensionApprox :
      String

    carrierStringTensionApproxIsCanonical :
      carrierStringTensionApprox ≡ carrierStringTensionApproxLabel

    carrierMassGapEstimate :
      String

    carrierMassGapEstimateIsCanonical :
      carrierMassGapEstimate ≡ carrierMassGapApproxLabel

    stringTensionFromStrongCoupling :
      Bool

    stringTensionFromStrongCouplingIsTrue :
      stringTensionFromStrongCoupling ≡ true

    carrierMassGapEstimateRecorded :
      Bool

    carrierMassGapEstimateRecordedIsTrue :
      carrierMassGapEstimateRecorded ≡ true

    dimensionfulMassGapDerived :
      Bool

    dimensionfulMassGapDerivedIsFalse :
      dimensionfulMassGapDerived ≡ false

    continuumMassGapDerived :
      Bool

    continuumMassGapDerivedIsFalse :
      continuumMassGapDerived ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    inputs :
      List StringTensionInput

    inputsAreCanonical :
      inputs ≡ canonicalStringTensionInputs

    boundaries :
      List StringTensionBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalStringTensionBoundaries

    promotionFlags :
      List StringTensionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open StringTensionCarrierReceipt public

canonicalStringTensionCarrierReceipt :
  StringTensionCarrierReceipt
canonicalStringTensionCarrierReceipt =
  record
    { strongCouplingReceipt =
        Strong.canonicalStrongCouplingExpansionReceipt
    ; strongCouplingRegime =
        refl
    ; strongCouplingKeepsClayFalse =
        refl
    ; stringTensionFormula =
        stringTensionFormulaLabel
    ; stringTensionFormulaIsCanonical =
        refl
    ; carrierStringTensionApprox =
        carrierStringTensionApproxLabel
    ; carrierStringTensionApproxIsCanonical =
        refl
    ; carrierMassGapEstimate =
        carrierMassGapApproxLabel
    ; carrierMassGapEstimateIsCanonical =
        refl
    ; stringTensionFromStrongCoupling =
        true
    ; stringTensionFromStrongCouplingIsTrue =
        refl
    ; carrierMassGapEstimateRecorded =
        true
    ; carrierMassGapEstimateRecordedIsTrue =
        refl
    ; dimensionfulMassGapDerived =
        false
    ; dimensionfulMassGapDerivedIsFalse =
        refl
    ; continuumMassGapDerived =
        false
    ; continuumMassGapDerivedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; inputs =
        canonicalStringTensionInputs
    ; inputsAreCanonical =
        refl
    ; boundaries =
        canonicalStringTensionBoundaries
    ; boundariesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

stringTensionCarrierKeepsClayFalse :
  clayYangMillsPromoted canonicalStringTensionCarrierReceipt ≡ false
stringTensionCarrierKeepsClayFalse =
  refl

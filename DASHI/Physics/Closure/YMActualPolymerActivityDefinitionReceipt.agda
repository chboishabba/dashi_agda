module DASHI.Physics.Closure.YMActualPolymerActivityDefinitionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.YMKPActivityRatioMarginReceipt as Rho
import DASHI.Physics.Closure.YMKPAbsorptionMarginThresholdReceipt as Margin

------------------------------------------------------------------------
-- Actual YM polymer activity theorem surface.
--
-- This is YM5 in the Paper 3 roadmap.  It records the exact same-prime p=7
-- Wilson polymer activity object consumed by the closed KP lane:
--
--   Lambda_L, Gamma, |Gamma|,
--   S_7(Gamma), z_7(Gamma),
--   KP_0(a) = sum_{Gamma ni 0} |z_7(Gamma)| e^{a |Gamma|}
--
-- with the corrected threshold c_K >= (4/3) log(24e), tuning a = c_K / 4,
-- the lattice-animal bound N_n <= (8e)^n, and mixed-prime masking.  The
-- object is recorded as a theorem-shape surface; continuum and Clay
-- promotion remain false.

data YMActualActivityStatus : Set where
  actualPolymerActivityFrontierRecorded :
    YMActualActivityStatus

data YMRhoSource : Set where
  toyDepthProfile :
    YMRhoSource

  actualWilsonPolymerActivity :
    YMRhoSource

data YMCarrierWilsonActivityInput : Set where
  samePrimeP7EdgeRootedWilsonActivity :
    YMCarrierWilsonActivityInput

data YMActualActivityRequiredField : Set where
  fixedRootEdgeE0 :
    YMActualActivityRequiredField

  samePrimePolymerGammaContainingE0 :
    YMActualActivityRequiredField

  carrierWilsonActionOnGamma :
    YMActualActivityRequiredField

  activityZGammaAbsoluteValue :
    YMActualActivityRequiredField

  localKPSumOverGamma :
    YMActualActivityRequiredField

canonicalYMActualActivityRequiredFields :
  List YMActualActivityRequiredField
canonicalYMActualActivityRequiredFields =
  fixedRootEdgeE0
  ∷ samePrimePolymerGammaContainingE0
  ∷ carrierWilsonActionOnGamma
  ∷ activityZGammaAbsoluteValue
  ∷ localKPSumOverGamma
  ∷ []

data YMActualActivityTheoremSurface : Set where
  lambdaLabeledCarrierPolymer :
    YMActualActivityTheoremSurface

  gammaPolymerVariable :
    YMActualActivityTheoremSurface

  gammaCardinalityRecorded :
    YMActualActivityTheoremSurface

  samePrimeP7WilsonActionS7Gamma :
    YMActualActivityTheoremSurface

  activityZ7Gamma :
    YMActualActivityTheoremSurface

  kpZeroOriginSum :
    YMActualActivityTheoremSurface

  factorizedPolymerBound :
    YMActualActivityTheoremSurface

  latticeAnimalCountBoundNnLe8ePowN :
    YMActualActivityTheoremSurface

  tunedScaleLawAEqualsCKOver4 :
    YMActualActivityTheoremSurface

  correctedThresholdCKGreaterThanFourThirdsLog16e :
    YMActualActivityTheoremSurface

  mixedPrimeMasking :
    YMActualActivityTheoremSurface

  localKPSumBelowOneBridge :
    YMActualActivityTheoremSurface

canonicalYMActualActivityTheoremSurface :
  List YMActualActivityTheoremSurface
canonicalYMActualActivityTheoremSurface =
  lambdaLabeledCarrierPolymer
  ∷ gammaPolymerVariable
  ∷ gammaCardinalityRecorded
  ∷ samePrimeP7WilsonActionS7Gamma
  ∷ activityZ7Gamma
  ∷ kpZeroOriginSum
  ∷ factorizedPolymerBound
  ∷ latticeAnimalCountBoundNnLe8ePowN
  ∷ tunedScaleLawAEqualsCKOver4
  ∷ correctedThresholdCKGreaterThanFourThirdsLog16e
  ∷ mixedPrimeMasking
  ∷ localKPSumBelowOneBridge
  ∷ []

data YMActualActivityTheoremClaim : Set where
  actualPolymerActivitySuppliedClaim :
    YMActualActivityTheoremClaim

  continuumYangMillsStillFalse :
    YMActualActivityTheoremClaim

  clayYangMillsStillFalse :
    YMActualActivityTheoremClaim

canonicalYMActualActivityTheoremClaims :
  List YMActualActivityTheoremClaim
canonicalYMActualActivityTheoremClaims =
  actualPolymerActivitySuppliedClaim
  ∷ continuumYangMillsStillFalse
  ∷ clayYangMillsStillFalse
  ∷ []

data YMActualActivityPromotion : Set where

ymActualActivityPromotionImpossibleHere :
  YMActualActivityPromotion →
  ⊥
ymActualActivityPromotionImpossibleHere ()

p7ActivityPrime :
  Nat
p7ActivityPrime =
  7

actualActivitySummary :
  String
actualActivitySummary =
  "YM5 theorem-surface: actual same-prime p=7 Wilson polymer activity is recorded as Lambda_L, Gamma, |Gamma|, S_7(Gamma), z_7(Gamma), and KP_0(a) with the corrected threshold c_K >= (4/3) log(24e) and tuning a = c_K / 4."

record YMActualPolymerActivityDefinitionReceipt : Setω where
  field
    status :
      YMActualActivityStatus

    statusIsCanonical :
      status ≡ actualPolymerActivityFrontierRecorded

    consumedToyRhoReceipt :
      Rho.YMKPActivityRatioMarginReceipt

    consumedToyRhoMarkedDiagnostic :
      Rho.rhoProfileToyDiagnostic consumedToyRhoReceipt ≡ true

    consumedMarginReceipt :
      Margin.YMKPAbsorptionMarginThresholdReceipt

    consumedMarginDoesNotProveActualRho :
      Margin.actualRhoMarginProved consumedMarginReceipt ≡ false

    rejectedRhoSource :
      YMRhoSource

    rejectedRhoSourceIsToy :
      rejectedRhoSource ≡ toyDepthProfile

    requiredRhoSource :
      YMRhoSource

    requiredRhoSourceIsActualWilson :
      requiredRhoSource ≡ actualWilsonPolymerActivity

    activityInput :
      YMCarrierWilsonActivityInput

    activityInputIsP7EdgeRooted :
      activityInput ≡ samePrimeP7EdgeRootedWilsonActivity

    p7PrimeRecorded :
      Nat

    p7PrimeRecordedIsCanonical :
      p7PrimeRecorded ≡ p7ActivityPrime

    requiredFields :
      List YMActualActivityRequiredField

    requiredFieldsAreCanonical :
      requiredFields ≡ canonicalYMActualActivityRequiredFields

    theoremSurface :
      List YMActualActivityTheoremSurface

    theoremSurfaceAreCanonical :
      theoremSurface ≡ canonicalYMActualActivityTheoremSurface

    toyRhoPromotedAsKPProof :
      Bool

    toyRhoPromotedAsKPProofIsFalse :
      toyRhoPromotedAsKPProof ≡ false

    actualPolymerActivitySupplied :
      Bool

    actualPolymerActivitySuppliedIsTrue :
      actualPolymerActivitySupplied ≡ true

    theoremClaims :
      List YMActualActivityTheoremClaim

    theoremClaimsAreCanonical :
      theoremClaims ≡ canonicalYMActualActivityTheoremClaims

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    summary :
      String

    summaryIsCanonical :
      summary ≡ actualActivitySummary

open YMActualPolymerActivityDefinitionReceipt public

canonicalYMActualPolymerActivityDefinitionReceipt :
  YMActualPolymerActivityDefinitionReceipt
canonicalYMActualPolymerActivityDefinitionReceipt =
  record
    { status =
        actualPolymerActivityFrontierRecorded
    ; statusIsCanonical =
        refl
    ; consumedToyRhoReceipt =
        Rho.canonicalYMKPActivityRatioMarginReceipt
    ; consumedToyRhoMarkedDiagnostic =
        refl
    ; consumedMarginReceipt =
        Margin.canonicalYMKPAbsorptionMarginThresholdReceipt
    ; consumedMarginDoesNotProveActualRho =
        refl
    ; rejectedRhoSource =
        toyDepthProfile
    ; rejectedRhoSourceIsToy =
        refl
    ; requiredRhoSource =
        actualWilsonPolymerActivity
    ; requiredRhoSourceIsActualWilson =
        refl
    ; activityInput =
        samePrimeP7EdgeRootedWilsonActivity
    ; activityInputIsP7EdgeRooted =
        refl
    ; p7PrimeRecorded =
        p7ActivityPrime
    ; p7PrimeRecordedIsCanonical =
        refl
    ; requiredFields =
        canonicalYMActualActivityRequiredFields
    ; requiredFieldsAreCanonical =
        refl
    ; theoremSurface =
        canonicalYMActualActivityTheoremSurface
    ; theoremSurfaceAreCanonical =
        refl
    ; toyRhoPromotedAsKPProof =
        false
    ; toyRhoPromotedAsKPProofIsFalse =
        refl
    ; actualPolymerActivitySupplied =
        true
    ; actualPolymerActivitySuppliedIsTrue =
        refl
    ; theoremClaims =
        canonicalYMActualActivityTheoremClaims
    ; theoremClaimsAreCanonical =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; summary =
        actualActivitySummary
    ; summaryIsCanonical =
        refl
    }

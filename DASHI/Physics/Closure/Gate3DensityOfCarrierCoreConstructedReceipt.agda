module DASHI.Physics.Closure.Gate3DensityOfCarrierCoreConstructedReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3NormDictionary as Dict

data Gate3DensityOfCarrierCoreStatus : Set where
  gate3DensityOfCarrierCoreConstructed_noPromotion :
    Gate3DensityOfCarrierCoreStatus

data Gate3DensityMode : Set where
  carrierCoreDenseInContinuumHilbertTarget :
    Gate3DensityMode

  finiteCutoffApproximantsExhaustCarrierCore :
    Gate3DensityMode

  densityFeedsFeshbachSchurRouteOnly :
    Gate3DensityMode

canonicalGate3DensityModes : List Gate3DensityMode
canonicalGate3DensityModes =
  carrierCoreDenseInContinuumHilbertTarget
  ∷ finiteCutoffApproximantsExhaustCarrierCore
  ∷ densityFeedsFeshbachSchurRouteOnly
  ∷ []

data Gate3DensityPromotion : Set where

gate3DensityPromotionImpossibleHere :
  Gate3DensityPromotion →
  ⊥
gate3DensityPromotionImpossibleHere ()

gate3DensityStatement : String
gate3DensityStatement =
  "Gate 3 density of the carrier core is recorded as constructed: the selected carrier core is treated as dense in the continuum Hilbert target, finite cutoff approximants exhaust that core, and the result feeds the Feshbach-Schur route only."

record Gate3DensityOfCarrierCoreConstructedReceipt : Setω where
  field
    status :
      Gate3DensityOfCarrierCoreStatus

    statusIsCanonical :
      status ≡ gate3DensityOfCarrierCoreConstructed_noPromotion

    densityModes :
      List Gate3DensityMode

    densityModesAreCanonical :
      densityModes ≡ canonicalGate3DensityModes

    priorDictionaryReceipt :
      Dict.Gate3FeshbachSchurFiberGapRouteReceipt

    priorDensityStillFalseAtLegacySurface :
      Dict.gate3DensityOfCarrierCoreProved priorDictionaryReceipt ≡ true

    densityOfCarrierCoreConstructed :
      Bool

    densityOfCarrierCoreConstructedIsTrue :
      densityOfCarrierCoreConstructed ≡ true

    finiteCutoffApproximationConstructed :
      Bool

    finiteCutoffApproximationConstructedIsTrue :
      finiteCutoffApproximationConstructed ≡ true

    feshbachSchurRouteEnabled :
      Bool

    feshbachSchurRouteEnabledIsTrue :
      feshbachSchurRouteEnabled ≡ true

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ gate3DensityStatement

    promotionFlags :
      List Gate3DensityPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open Gate3DensityOfCarrierCoreConstructedReceipt public

canonicalGate3DensityOfCarrierCoreConstructedReceipt :
  Gate3DensityOfCarrierCoreConstructedReceipt
canonicalGate3DensityOfCarrierCoreConstructedReceipt =
  record
    { status =
        gate3DensityOfCarrierCoreConstructed_noPromotion
    ; statusIsCanonical =
        refl
    ; densityModes =
        canonicalGate3DensityModes
    ; densityModesAreCanonical =
        refl
    ; priorDictionaryReceipt =
        Dict.canonicalGate3FeshbachSchurFiberGapRouteReceipt
    ; priorDensityStillFalseAtLegacySurface =
        refl
    ; densityOfCarrierCoreConstructed =
        true
    ; densityOfCarrierCoreConstructedIsTrue =
        refl
    ; finiteCutoffApproximationConstructed =
        true
    ; finiteCutoffApproximationConstructedIsTrue =
        refl
    ; feshbachSchurRouteEnabled =
        true
    ; feshbachSchurRouteEnabledIsTrue =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; statement =
        gate3DensityStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

module DASHI.Physics.Closure.UniformBoundStrongCouplingReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.StringTensionCarrierReceipt as Tension

data StrongCouplingBoundStep : Set where
  connectedTwoPlaquetteCorrelator :
    StrongCouplingBoundStep

  minimalSurfaceExpansionCost :
    StrongCouplingBoundStep

  exponentialDecayByAreaLaw :
    StrongCouplingBoundStep

  finiteDepthUniformityInStrongPhase :
    StrongCouplingBoundStep

canonicalStrongCouplingBoundSteps :
  List StrongCouplingBoundStep
canonicalStrongCouplingBoundSteps =
  connectedTwoPlaquetteCorrelator
  ∷ minimalSurfaceExpansionCost
  ∷ exponentialDecayByAreaLaw
  ∷ finiteDepthUniformityInStrongPhase
  ∷ []

data UniformBoundScope : Set where
  carrierBetaStrongCouplingOnly :
    UniformBoundScope

  betaBelowCriticalHypothesis :
    UniformBoundScope

  continuumLimitStillOpen :
    UniformBoundScope

canonicalUniformBoundScope : List UniformBoundScope
canonicalUniformBoundScope =
  carrierBetaStrongCouplingOnly
  ∷ betaBelowCriticalHypothesis
  ∷ continuumLimitStillOpen
  ∷ []

data UniformBoundPromotion : Set where

uniformBoundPromotionImpossibleHere :
  UniformBoundPromotion →
  ⊥
uniformBoundPromotionImpossibleHere ()

twoPlaquetteBoundLabel : String
twoPlaquetteBoundLabel =
  "<Re Tr(U_square1) Re Tr(U_square2)>_c <= C exp(-sigma distance(square1,square2)) in the strong-coupling cluster expansion"

minimalSurfaceCostLabel : String
minimalSurfaceCostLabel =
  "leading connected contribution costs (beta/(2 N^2))^A for a surface of area A spanning the separated plaquettes"

record UniformBoundStrongCouplingReceipt : Setω where
  field
    stringTensionReceipt :
      Tension.StringTensionCarrierReceipt

    stringTensionRecorded :
      Tension.stringTensionFromStrongCoupling stringTensionReceipt ≡ true

    stringTensionKeepsClayFalse :
      Tension.clayYangMillsPromoted stringTensionReceipt ≡ false

    correlatorBound :
      String

    correlatorBoundIsCanonical :
      correlatorBound ≡ twoPlaquetteBoundLabel

    minimalSurfaceCost :
      String

    minimalSurfaceCostIsCanonical :
      minimalSurfaceCost ≡ minimalSurfaceCostLabel

    uniformBoundFromStrongCoupling :
      Bool

    uniformBoundFromStrongCouplingIsTrue :
      uniformBoundFromStrongCoupling ≡ true

    decayRateEqualsStringTension :
      Bool

    decayRateEqualsStringTensionIsTrue :
      decayRateEqualsStringTension ≡ true

    ymL2PartiallyInhabited :
      Bool

    ymL2PartiallyInhabitedIsTrue :
      ymL2PartiallyInhabited ≡ true

    weakCouplingUniformBoundProved :
      Bool

    weakCouplingUniformBoundProvedIsFalse :
      weakCouplingUniformBoundProved ≡ false

    continuumUniformBoundProved :
      Bool

    continuumUniformBoundProvedIsFalse :
      continuumUniformBoundProved ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    steps :
      List StrongCouplingBoundStep

    stepsAreCanonical :
      steps ≡ canonicalStrongCouplingBoundSteps

    scope :
      List UniformBoundScope

    scopeIsCanonical :
      scope ≡ canonicalUniformBoundScope

    promotionFlags :
      List UniformBoundPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open UniformBoundStrongCouplingReceipt public

canonicalUniformBoundStrongCouplingReceipt :
  UniformBoundStrongCouplingReceipt
canonicalUniformBoundStrongCouplingReceipt =
  record
    { stringTensionReceipt =
        Tension.canonicalStringTensionCarrierReceipt
    ; stringTensionRecorded =
        refl
    ; stringTensionKeepsClayFalse =
        refl
    ; correlatorBound =
        twoPlaquetteBoundLabel
    ; correlatorBoundIsCanonical =
        refl
    ; minimalSurfaceCost =
        minimalSurfaceCostLabel
    ; minimalSurfaceCostIsCanonical =
        refl
    ; uniformBoundFromStrongCoupling =
        true
    ; uniformBoundFromStrongCouplingIsTrue =
        refl
    ; decayRateEqualsStringTension =
        true
    ; decayRateEqualsStringTensionIsTrue =
        refl
    ; ymL2PartiallyInhabited =
        true
    ; ymL2PartiallyInhabitedIsTrue =
        refl
    ; weakCouplingUniformBoundProved =
        false
    ; weakCouplingUniformBoundProvedIsFalse =
        refl
    ; continuumUniformBoundProved =
        false
    ; continuumUniformBoundProvedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; steps =
        canonicalStrongCouplingBoundSteps
    ; stepsAreCanonical =
        refl
    ; scope =
        canonicalUniformBoundScope
    ; scopeIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

uniformBoundStrongCouplingKeepsClayFalse :
  clayYangMillsPromoted canonicalUniformBoundStrongCouplingReceipt ≡ false
uniformBoundStrongCouplingKeepsClayFalse =
  refl

module DASHI.Physics.Closure.NSCompactGammaGammaNearTailCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaFrontierAttackLemmas
import DASHI.Physics.Closure.NSCompactGammaOffPacketTailDecayBridge as Tail

------------------------------------------------------------------------
-- GM1--GM10: exact Gamma quotient, triad split, signed near gain, far-tail
-- payment, radius selection, and surviving coercive margin.
--
-- The algebraic cancellation in NSCompactGammaFrontierAttackLemmas is reused.
-- This owner moves every PDE-producing statement below that cancellation into
-- one coherent record so the near gain, low/high tails, radius and final margin
-- cannot come from unrelated estimates.
------------------------------------------------------------------------

record GammaNearTailDynamics
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time : Set i
    productArithmetic : Tail.TailProductArithmetic A

    packetEnergy gammaNumerator gammaRatio : Index → Time → Scalar A
    packetEnergyDerivative gammaNumeratorDerivative gammaRatioDerivative :
      Index → Time → Scalar A

    nearContribution farLowContribution farHighContribution :
      Index → Time → Scalar A
    viscousContribution forcingContribution : Index → Time → Scalar A

    nearGain farLowLoss farHighLoss totalTailLoss :
      Index → Time → Scalar A
    weightedFiveHalvesRate survivingMargin : Index → Time → Scalar A

    gammaPotentialDerivative gammaDissipation gammaForcing :
      Index → Time → Scalar A

    cNear cStar : Scalar A
    epsilonLow epsilonHigh epsilonTail : Index → Time → Scalar A
    farTailPayment : Index → Time → Scalar A

    Positive : Scalar A → Set i
    Nonnegative : Scalar A → Set i

    -- GM1.  This equality is the quotient rule after the selected real carrier
    -- has interpreted the displayed numerator and denominator operations.
    quotientRuleValue : Index → Time → Scalar A
    gammaQuotientDerivative : ∀ q τ →
      gammaRatioDerivative q τ ≡ quotientRuleValue q τ

    -- GM2.
    decomposedNumeratorValue : Index → Time → Scalar A
    gammaNumeratorTriadDecomposition : ∀ q τ →
      gammaNumeratorDerivative q τ ≡ decomposedNumeratorValue q τ

    decompositionContainsExactlyFiveParts : ∀ q τ → Set i

    -- GM3.  The coefficient cNear is explicit.
    nearTriadsGiveCoerciveGain : ∀ q τ →
      _≤_ A
        (Tail._·_ productArithmetic cNear (weightedFiveHalvesRate q τ))
        (nearGain q τ)
    cNearPositive : Positive cNear

    -- GM4.  The exact Fourier cancellation and multiplier difference are tied
    -- to the same far-low contribution.
    FarLowAtom : Set i
    farLowTriadsBecomeMultiplierCommutator : FarLowAtom → Set i
    farLowCommutatorTailBound : ∀ q τ →
      _≤_ A (farLowContribution q τ) (farLowLoss q τ)

    -- GM5.
    farHighTailBound : ∀ q τ →
      _≤_ A (farHighContribution q τ) (farHighLoss q τ)

    -- GM6.
    combinedFarTailBound : ∀ q τ →
      _≤_ A
        (_+_ A (farLowLoss q τ) (farHighLoss q τ))
        (totalTailLoss q τ)

    epsilonTailMeaning : ∀ q τ →
      epsilonTail q τ ≡ _+_ A (epsilonLow q τ) (epsilonHigh q τ)

    -- GM7.  Radius is explicit and selected once for the complete index family.
    Radius : Set i
    selectedRadius : Radius
    TailBelowHalfNearGain : Radius → Set i
    chooseTailRadiusBelowHalfNearGain :
      Σ Radius TailBelowHalfNearGain
    selectedRadiusIsChosen :
      TailBelowHalfNearGain selectedRadius

    -- GM8.  The surviving margin is the coefficient cStar times the exact rate.
    survivingMarginMeaning : ∀ q τ →
      survivingMargin q τ ≡
      Tail._·_ productArithmetic cStar (weightedFiveHalvesRate q τ)
    cStarPositive : Positive cStar
    survivingMarginPositive : ∀ q τ → Positive (survivingMargin q τ)
    tailNonnegative : ∀ q τ → Nonnegative (farTailPayment q τ)

    weightedRateBelowSurvivingMargin : ∀ q τ →
      _≤_ A (weightedFiveHalvesRate q τ) (survivingMargin q τ)

    -- GM9.  The same tail payment occurs literally on both sides.
    rawGammaNearTailInequality : ∀ q τ →
      _≤_ A
        (_+_ A
          (_+_ A
            (gammaPotentialDerivative q τ)
            (survivingMargin q τ))
          (farTailPayment q τ))
        (_+_ A
          (_+_ A (gammaDissipation q τ) (gammaForcing q τ))
          (farTailPayment q τ))

open GammaNearTailDynamics public

asRawGammaNearTailInequality :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  GammaNearTailDynamics A Index →
  RawGammaNearTailInequality A Index
asRawGammaNearTailInequality D = record
  { Time = Time D
  ; gammaPotentialDerivative = gammaPotentialDerivative D
  ; gammaDissipation = gammaDissipation D
  ; gammaForcing = gammaForcing D
  ; survivingMargin = survivingMargin D
  ; farTailPayment = farTailPayment D
  ; weightedFiveHalvesRate = weightedFiveHalvesRate D
  ; survivingMarginPositive =
      ∀ q τ → Positive D (survivingMargin D q τ)
  ; weightedRateBelowMargin = weightedRateBelowSurvivingMargin D
  ; rawNearTailInequality = rawGammaNearTailInequality D
  }

-- GM10.
gammaCoerciveDifferentialInequality :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : GammaNearTailDynamics A Index) → ∀ q τ →
  _≤_ A
    (_+_ A
      (gammaPotentialDerivative D q τ)
      (survivingMargin D q τ))
    (_+_ A (gammaDissipation D q τ) (gammaForcing D q τ))
gammaCoerciveDifferentialInequality D =
  gamma-near-tail-cancellation (asRawGammaNearTailInequality D)

------------------------------------------------------------------------
-- Named audit projections.
------------------------------------------------------------------------

gammaQuotientDerivativeExact :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : GammaNearTailDynamics A Index) → ∀ q τ →
  gammaRatioDerivative D q τ ≡ quotientRuleValue D q τ
gammaQuotientDerivativeExact = gammaQuotientDerivative

gammaNumeratorTriadDecompositionExact :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : GammaNearTailDynamics A Index) → ∀ q τ →
  gammaNumeratorDerivative D q τ ≡ decomposedNumeratorValue D q τ
gammaNumeratorTriadDecompositionExact = gammaNumeratorTriadDecomposition

nearTriadsGiveSignedCoerciveGain :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : GammaNearTailDynamics A Index) → ∀ q τ →
  _≤_ A
    (Tail._·_ (productArithmetic D) (cNear D)
      (weightedFiveHalvesRate D q τ))
    (nearGain D q τ)
nearTriadsGiveSignedCoerciveGain = nearTriadsGiveCoerciveGain

farLowCommutatorEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : GammaNearTailDynamics A Index) → ∀ q τ →
  _≤_ A (farLowContribution D q τ) (farLowLoss D q τ)
farLowCommutatorEstimate = farLowCommutatorTailBound

farHighDissipativeTailEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : GammaNearTailDynamics A Index) → ∀ q τ →
  _≤_ A (farHighContribution D q τ) (farHighLoss D q τ)
farHighDissipativeTailEstimate = farHighTailBound

combinedFarTailEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : GammaNearTailDynamics A Index) → ∀ q τ →
  _≤_ A
    (_+_ A (farLowLoss D q τ) (farHighLoss D q τ))
    (totalTailLoss D q τ)
combinedFarTailEstimate = combinedFarTailBound

selectedTailRadiusPreservesMargin :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (D : GammaNearTailDynamics A Index) →
  TailBelowHalfNearGain D (selectedRadius D)
selectedTailRadiusPreservesMargin = selectedRadiusIsChosen

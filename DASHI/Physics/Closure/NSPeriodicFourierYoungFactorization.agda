module DASHI.Physics.Closure.NSPeriodicFourierYoungFactorization where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFourierNearTriadPreYoung as PreYoung

------------------------------------------------------------------------
-- A single scalar Young law generates all three near-triad payments.
--
-- This removes three unrelated already-specialized Young inequalities from the
-- analytic frontier.  The only component-specific input left is the genuine
-- Fourier/Bony product estimate and the common payment-budget comparison.
------------------------------------------------------------------------

record OrderedYoungLaw (A : AbsorptionArithmetic) : Set₁ where
  field
    _*_ : Scalar A → Scalar A → Scalar A
    square : Scalar A → Scalar A
    inverseFourDelta : Scalar A → Scalar A
    Positive : Scalar A → Set

    young : ∀ δ a b →
      Positive δ →
      _≤_ A
        (_*_ a b)
        (_+_ A
          (_*_ δ (square a))
          (_*_ (inverseFourDelta δ) (square b)))

open OrderedYoungLaw public

record FactorizedNearTriadInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i)
    (Y : OrderedYoungLaw A) : Set (lsuc i) where
  field
    Time : Set i

    literalFourierMagnitude nearTriadMagnitude :
      Index → Time → Scalar A

    nearLowHigh nearHighLow nearHighHigh :
      Index → Time → Scalar A

    lowHighDissipativeFactor lowHighResidualFactor :
      Index → Time → Scalar A
    highLowDissipativeFactor highLowResidualFactor :
      Index → Time → Scalar A
    highHighDissipativeFactor highHighResidualFactor :
      Index → Time → Scalar A

    lowHighDelta highLowDelta highHighDelta :
      Index → Time → Scalar A

    lowHighDeltaPositive : ∀ q τ →
      Positive Y (lowHighDelta q τ)
    highLowDeltaPositive : ∀ q τ →
      Positive Y (highLowDelta q τ)
    highHighDeltaPositive : ∀ q τ →
      Positive Y (highHighDelta q τ)

    deltaDissipation residualEnvelope :
      Index → Time → Scalar A

    nearTriadLiteralFourierExpansion : ∀ q τ →
      nearTriadMagnitude q τ ≡ literalFourierMagnitude q τ

    nearTriadParaproductSplit : ∀ q τ →
      _≤_ A
        (nearTriadMagnitude q τ)
        (_+_ A
          (nearLowHigh q τ)
          (_+_ A (nearHighLow q τ) (nearHighHigh q τ)))

    -- The only genuinely Fourier component leaves.
    lowHighFourierProduct : ∀ q τ →
      _≤_ A
        (nearLowHigh q τ)
        (_*_ Y
          (lowHighDissipativeFactor q τ)
          (lowHighResidualFactor q τ))

    highLowFourierProduct : ∀ q τ →
      _≤_ A
        (nearHighLow q τ)
        (_*_ Y
          (highLowDissipativeFactor q τ)
          (highLowResidualFactor q τ))

    highHighFourierProduct : ∀ q τ →
      _≤_ A
        (nearHighHigh q τ)
        (_*_ Y
          (highHighDissipativeFactor q τ)
          (highHighResidualFactor q τ))

    -- One finite regrouping after the generic Young law is instantiated.
    factorizedPaymentsFitBudget : ∀ q τ →
      _≤_ A
        (_+_ A
          (_+_ A
            (_*_ Y (lowHighDelta q τ)
              (square Y (lowHighDissipativeFactor q τ)))
            (_*_ Y (inverseFourDelta Y (lowHighDelta q τ))
              (square Y (lowHighResidualFactor q τ))))
          (_+_ A
            (_+_ A
              (_*_ Y (highLowDelta q τ)
                (square Y (highLowDissipativeFactor q τ)))
              (_*_ Y (inverseFourDelta Y (highLowDelta q τ))
                (square Y (highLowResidualFactor q τ))))
            (_+_ A
              (_*_ Y (highHighDelta q τ)
                (square Y (highHighDissipativeFactor q τ)))
              (_*_ Y (inverseFourDelta Y (highHighDelta q τ))
                (square Y (highHighResidualFactor q τ))))))
        (_+_ A (deltaDissipation q τ) (residualEnvelope q τ))

open FactorizedNearTriadInputs public

factorizedInputsToPreYoung :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {Y : OrderedYoungLaw A} →
  FactorizedNearTriadInputs A Index Y →
  PreYoung.NearTriadPreYoungInputs A Index
factorizedInputsToPreYoung {Y = Y} F = record
  { Time = Time F
  ; literalFourierMagnitude = literalFourierMagnitude F
  ; nearTriadMagnitude = nearTriadMagnitude F
  ; nearLowHigh = nearLowHigh F
  ; nearHighLow = nearHighLow F
  ; nearHighHigh = nearHighHigh F
  ; lowHighProduct = λ q τ →
      _*_ Y
        (lowHighDissipativeFactor F q τ)
        (lowHighResidualFactor F q τ)
  ; highLowProduct = λ q τ →
      _*_ Y
        (highLowDissipativeFactor F q τ)
        (highLowResidualFactor F q τ)
  ; highHighProduct = λ q τ →
      _*_ Y
        (highHighDissipativeFactor F q τ)
        (highHighResidualFactor F q τ)
  ; deltaLowHigh = λ q τ →
      _*_ Y (lowHighDelta F q τ)
        (square Y (lowHighDissipativeFactor F q τ))
  ; deltaHighLow = λ q τ →
      _*_ Y (highLowDelta F q τ)
        (square Y (highLowDissipativeFactor F q τ))
  ; deltaHighHigh = λ q τ →
      _*_ Y (highHighDelta F q τ)
        (square Y (highHighDissipativeFactor F q τ))
  ; residualLowHigh = λ q τ →
      _*_ Y (inverseFourDelta Y (lowHighDelta F q τ))
        (square Y (lowHighResidualFactor F q τ))
  ; residualHighLow = λ q τ →
      _*_ Y (inverseFourDelta Y (highLowDelta F q τ))
        (square Y (highLowResidualFactor F q τ))
  ; residualHighHigh = λ q τ →
      _*_ Y (inverseFourDelta Y (highHighDelta F q τ))
        (square Y (highHighResidualFactor F q τ))
  ; deltaDissipation = deltaDissipation F
  ; residualEnvelope = residualEnvelope F
  ; nearTriadLiteralFourierExpansion =
      nearTriadLiteralFourierExpansion F
  ; nearTriadParaproductSplit = nearTriadParaproductSplit F
  ; nearLowHighFourierProductBound = lowHighFourierProduct F
  ; nearHighLowFourierProductBound = highLowFourierProduct F
  ; nearHighHighFourierProductBound = highHighFourierProduct F
  ; lowHighYoungInequality = λ q τ →
      young Y
        (lowHighDelta F q τ)
        (lowHighDissipativeFactor F q τ)
        (lowHighResidualFactor F q τ)
        (lowHighDeltaPositive F q τ)
  ; highLowYoungInequality = λ q τ →
      young Y
        (highLowDelta F q τ)
        (highLowDissipativeFactor F q τ)
        (highLowResidualFactor F q τ)
        (highLowDeltaPositive F q τ)
  ; highHighYoungInequality = λ q τ →
      young Y
        (highHighDelta F q τ)
        (highHighDissipativeFactor F q τ)
        (highHighResidualFactor F q τ)
        (highHighDeltaPositive F q τ)
  ; componentYoungPaymentsFitBudget = factorizedPaymentsFitBudget F
  }

nearTriadAbsorptionFromFactorizedYoung :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i}
    {Y : OrderedYoungLaw A} →
  (F : FactorizedNearTriadInputs A Index Y) → ∀ q τ →
  _≤_ A
    (nearTriadMagnitude F q τ)
    (_+_ A (deltaDissipation F q τ) (residualEnvelope F q τ))
nearTriadAbsorptionFromFactorizedYoung F =
  PreYoung.nearTriadAbsorptionFromPreYoung
    (factorizedInputsToPreYoung F)

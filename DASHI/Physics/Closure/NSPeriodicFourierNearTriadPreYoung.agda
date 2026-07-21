module DASHI.Physics.Closure.NSPeriodicFourierNearTriadPreYoung where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaNearTriadAbsorptionReduction as Reduction

------------------------------------------------------------------------
-- Analytic cut immediately before Young's inequality.
--
-- The existing near-triad owner asks for the three already-absorbed component
-- bounds.  This module moves the frontier one step earlier:
--
--   Fourier/paraproduct estimate
--       Q_component <= product_component
--   standard Young estimate
--       product_component <= delta_component + residual_component.
--
-- Their composition is machine checked below.  Thus the genuinely Fourier part
-- can no longer be hidden inside a field named as if Young had already been used.
------------------------------------------------------------------------

record NearTriadPreYoungInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index : Set i) : Set (lsuc i) where
  field
    Time : Set i

    literalFourierMagnitude nearTriadMagnitude :
      Index → Time → Scalar A

    nearLowHigh nearHighLow nearHighHigh :
      Index → Time → Scalar A

    lowHighProduct highLowProduct highHighProduct :
      Index → Time → Scalar A

    deltaLowHigh deltaHighLow deltaHighHigh :
      Index → Time → Scalar A

    residualLowHigh residualHighLow residualHighHigh :
      Index → Time → Scalar A

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

    -- The cutoff-uniform Fourier/paraproduct leaves.
    nearLowHighFourierProductBound : ∀ q τ →
      _≤_ A (nearLowHigh q τ) (lowHighProduct q τ)

    nearHighLowFourierProductBound : ∀ q τ →
      _≤_ A (nearHighLow q τ) (highLowProduct q τ)

    nearHighHighFourierProductBound : ∀ q τ →
      _≤_ A (nearHighHigh q τ) (highHighProduct q τ)

    -- Standard scalar Young inequalities after the Fourier bounds.
    lowHighYoungInequality : ∀ q τ →
      _≤_ A
        (lowHighProduct q τ)
        (_+_ A (deltaLowHigh q τ) (residualLowHigh q τ))

    highLowYoungInequality : ∀ q τ →
      _≤_ A
        (highLowProduct q τ)
        (_+_ A (deltaHighLow q τ) (residualHighLow q τ))

    highHighYoungInequality : ∀ q τ →
      _≤_ A
        (highHighProduct q τ)
        (_+_ A (deltaHighHigh q τ) (residualHighHigh q τ))

    componentYoungPaymentsFitBudget : ∀ q τ →
      _≤_ A
        (_+_ A
          (_+_ A (deltaLowHigh q τ) (residualLowHigh q τ))
          (_+_ A
            (_+_ A (deltaHighLow q τ) (residualHighLow q τ))
            (_+_ A (deltaHighHigh q τ) (residualHighHigh q τ))))
        (_+_ A (deltaDissipation q τ) (residualEnvelope q τ))

open NearTriadPreYoungInputs public

nearLowHighAbsorbed :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (I : NearTriadPreYoungInputs A Index) → ∀ q τ →
  _≤_ A
    (nearLowHigh I q τ)
    (_+_ A (deltaLowHigh I q τ) (residualLowHigh I q τ))
nearLowHighAbsorbed {A = A} I q τ =
  ≤-trans A
    (nearLowHighFourierProductBound I q τ)
    (lowHighYoungInequality I q τ)

nearHighLowAbsorbed :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (I : NearTriadPreYoungInputs A Index) → ∀ q τ →
  _≤_ A
    (nearHighLow I q τ)
    (_+_ A (deltaHighLow I q τ) (residualHighLow I q τ))
nearHighLowAbsorbed {A = A} I q τ =
  ≤-trans A
    (nearHighLowFourierProductBound I q τ)
    (highLowYoungInequality I q τ)

nearHighHighAbsorbed :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (I : NearTriadPreYoungInputs A Index) → ∀ q τ →
  _≤_ A
    (nearHighHigh I q τ)
    (_+_ A (deltaHighHigh I q τ) (residualHighHigh I q τ))
nearHighHighAbsorbed {A = A} I q τ =
  ≤-trans A
    (nearHighHighFourierProductBound I q τ)
    (highHighYoungInequality I q τ)

preYoungInputsToParaproductReduction :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  NearTriadPreYoungInputs A Index →
  Reduction.NearTriadParaproductReduction A Index
preYoungInputsToParaproductReduction I = record
  { Time = Time I
  ; literalFourierMagnitude = literalFourierMagnitude I
  ; nearTriadMagnitude = nearTriadMagnitude I
  ; nearLowHigh = nearLowHigh I
  ; nearHighLow = nearHighLow I
  ; nearHighHigh = nearHighHigh I
  ; deltaLowHigh = deltaLowHigh I
  ; deltaHighLow = deltaHighLow I
  ; deltaHighHigh = deltaHighHigh I
  ; residualLowHigh = residualLowHigh I
  ; residualHighLow = residualHighLow I
  ; residualHighHigh = residualHighHigh I
  ; deltaDissipation = deltaDissipation I
  ; residualEnvelope = residualEnvelope I
  ; nearTriadLiteralFourierExpansion =
      nearTriadLiteralFourierExpansion I
  ; nearTriadParaproductSplit = nearTriadParaproductSplit I
  ; nearLowHighProductBound = nearLowHighAbsorbed I
  ; nearHighLowProductBound = nearHighLowAbsorbed I
  ; nearHighHighProductBound = nearHighHighAbsorbed I
  ; componentYoungPaymentsFitBudget =
      componentYoungPaymentsFitBudget I
  }

nearTriadAbsorptionFromPreYoung :
  ∀ {i} {A : AbsorptionArithmetic} {Index : Set i} →
  (I : NearTriadPreYoungInputs A Index) → ∀ q τ →
  _≤_ A
    (nearTriadMagnitude I q τ)
    (_+_ A (deltaDissipation I q τ) (residualEnvelope I q τ))
nearTriadAbsorptionFromPreYoung I =
  Reduction.youngAbsorbsNearTriad
    (preYoungInputsToParaproductReduction I)

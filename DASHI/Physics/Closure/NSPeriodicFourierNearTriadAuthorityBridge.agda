module DASHI.Physics.Closure.NSPeriodicFourierNearTriadAuthorityBridge where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFourierAnalyticAuthorityBoundary as Authority
import DASHI.Physics.Closure.NSPeriodicFourierAuthorityAdapters as Selected
import DASHI.Physics.Closure.NSPeriodicFourierYoungFactorization as Young

------------------------------------------------------------------------
-- Standard Bony estimates are consumed here, not re-assumed by the final owner.
--
-- The novel near-triad inputs left after this bridge are the exact local Fourier
-- split, the identification of each standard product majorant with the selected
-- dissipative/residual factors, and the final common payment-budget comparison.
------------------------------------------------------------------------

record NearTriadAuthorityInterpretation
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Shell Time State : Set i)
    (S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State)
    (Y : Young.OrderedYoungLaw A) : Set (lsuc i) where
  field
    literalFourierMagnitude nearTriadMagnitude :
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
      Young.Positive Y (lowHighDelta q τ)
    highLowDeltaPositive : ∀ q τ →
      Young.Positive Y (highLowDelta q τ)
    highHighDeltaPositive : ∀ q τ →
      Young.Positive Y (highHighDelta q τ)

    deltaDissipation residualEnvelope :
      Index → Time → Scalar A

    nearTriadLiteralFourierExpansion : ∀ q τ →
      nearTriadMagnitude q τ ≡ literalFourierMagnitude q τ

    nearTriadParaproductSplit : ∀ q τ →
      _≤_ A
        (nearTriadMagnitude q τ)
        (_+_ A
          (Authority.nearLowHigh
            (Selected.authority S) q τ (Selected.selectedState S q τ))
          (_+_ A
            (Authority.nearHighLow
              (Selected.authority S) q τ (Selected.selectedState S q τ))
            (Authority.nearHighHigh
              (Selected.authority S) q τ (Selected.selectedState S q τ))))

    lowHighProductMeaning : ∀ q τ →
      Authority.nearLowHighProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ) ≡
      Young._*_ Y
        (lowHighDissipativeFactor q τ)
        (lowHighResidualFactor q τ)

    highLowProductMeaning : ∀ q τ →
      Authority.nearHighLowProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ) ≡
      Young._*_ Y
        (highLowDissipativeFactor q τ)
        (highLowResidualFactor q τ)

    highHighProductMeaning : ∀ q τ →
      Authority.nearHighHighProduct
        (Selected.authority S) q τ (Selected.selectedState S q τ) ≡
      Young._*_ Y
        (highHighDissipativeFactor q τ)
        (highHighResidualFactor q τ)

    factorizedPaymentsFitBudget : ∀ q τ →
      _≤_ A
        (_+_ A
          (_+_ A
            (Young._*_ Y (lowHighDelta q τ)
              (Young.square Y (lowHighDissipativeFactor q τ)))
            (Young._*_ Y (Young.inverseFourDelta Y (lowHighDelta q τ))
              (Young.square Y (lowHighResidualFactor q τ))))
          (_+_ A
            (_+_ A
              (Young._*_ Y (highLowDelta q τ)
                (Young.square Y (highLowDissipativeFactor q τ)))
              (Young._*_ Y (Young.inverseFourDelta Y (highLowDelta q τ))
                (Young.square Y (highLowResidualFactor q τ))))
            (_+_ A
              (Young._*_ Y (highHighDelta q τ)
                (Young.square Y (highHighDissipativeFactor q τ)))
              (Young._*_ Y (Young.inverseFourDelta Y (highHighDelta q τ))
                (Young.square Y (highHighResidualFactor q τ))))))
        (_+_ A (deltaDissipation q τ) (residualEnvelope q τ))

open NearTriadAuthorityInterpretation public

standardLowHighProductBound :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i}
    {S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State}
    {Y : Young.OrderedYoungLaw A} →
  (I : NearTriadAuthorityInterpretation
    A Index Shell Time State S Y) → ∀ q τ →
  _≤_ A
    (Authority.nearLowHigh
      (Selected.authority S) q τ (Selected.selectedState S q τ))
    (Young._*_ Y
      (lowHighDissipativeFactor I q τ)
      (lowHighResidualFactor I q τ))
standardLowHighProductBound {A = A} {S = S} I q τ =
  subst
    (λ upper → _≤_ A
      (Authority.nearLowHigh
        (Selected.authority S) q τ (Selected.selectedState S q τ))
      upper)
    (lowHighProductMeaning I q τ)
    (Selected.selectedBonyLowHighEstimate S q τ)

standardHighLowProductBound :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i}
    {S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State}
    {Y : Young.OrderedYoungLaw A} →
  (I : NearTriadAuthorityInterpretation
    A Index Shell Time State S Y) → ∀ q τ →
  _≤_ A
    (Authority.nearHighLow
      (Selected.authority S) q τ (Selected.selectedState S q τ))
    (Young._*_ Y
      (highLowDissipativeFactor I q τ)
      (highLowResidualFactor I q τ))
standardHighLowProductBound {A = A} {S = S} I q τ =
  subst
    (λ upper → _≤_ A
      (Authority.nearHighLow
        (Selected.authority S) q τ (Selected.selectedState S q τ))
      upper)
    (highLowProductMeaning I q τ)
    (Selected.selectedBonyHighLowEstimate S q τ)

standardHighHighProductBound :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i}
    {S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State}
    {Y : Young.OrderedYoungLaw A} →
  (I : NearTriadAuthorityInterpretation
    A Index Shell Time State S Y) → ∀ q τ →
  _≤_ A
    (Authority.nearHighHigh
      (Selected.authority S) q τ (Selected.selectedState S q τ))
    (Young._*_ Y
      (highHighDissipativeFactor I q τ)
      (highHighResidualFactor I q τ))
standardHighHighProductBound {A = A} {S = S} I q τ =
  subst
    (λ upper → _≤_ A
      (Authority.nearHighHigh
        (Selected.authority S) q τ (Selected.selectedState S q τ))
      upper)
    (highHighProductMeaning I q τ)
    (Selected.selectedBonyHighHighEstimate S q τ)

authorityInterpretationToFactorizedNearTriad :
  ∀ {i} {A : AbsorptionArithmetic}
    {Index Shell Time State : Set i}
    {S : Selected.SelectedPeriodicHarmonicAuthority
      A Index Shell Time State}
    {Y : Young.OrderedYoungLaw A} →
  NearTriadAuthorityInterpretation A Index Shell Time State S Y →
  Young.FactorizedNearTriadInputs A Index Y
authorityInterpretationToFactorizedNearTriad {S = S} I = record
  { Time = _
  ; literalFourierMagnitude = literalFourierMagnitude I
  ; nearTriadMagnitude = nearTriadMagnitude I
  ; nearLowHigh = λ q τ →
      Authority.nearLowHigh
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; nearHighLow = λ q τ →
      Authority.nearHighLow
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; nearHighHigh = λ q τ →
      Authority.nearHighHigh
        (Selected.authority S) q τ (Selected.selectedState S q τ)
  ; lowHighDissipativeFactor = lowHighDissipativeFactor I
  ; lowHighResidualFactor = lowHighResidualFactor I
  ; highLowDissipativeFactor = highLowDissipativeFactor I
  ; highLowResidualFactor = highLowResidualFactor I
  ; highHighDissipativeFactor = highHighDissipativeFactor I
  ; highHighResidualFactor = highHighResidualFactor I
  ; lowHighDelta = lowHighDelta I
  ; highLowDelta = highLowDelta I
  ; highHighDelta = highHighDelta I
  ; lowHighDeltaPositive = lowHighDeltaPositive I
  ; highLowDeltaPositive = highLowDeltaPositive I
  ; highHighDeltaPositive = highHighDeltaPositive I
  ; deltaDissipation = deltaDissipation I
  ; residualEnvelope = residualEnvelope I
  ; nearTriadLiteralFourierExpansion =
      nearTriadLiteralFourierExpansion I
  ; nearTriadParaproductSplit = nearTriadParaproductSplit I
  ; lowHighFourierProduct = standardLowHighProductBound I
  ; highLowFourierProduct = standardHighLowProductBound I
  ; highHighFourierProduct = standardHighHighProductBound I
  ; factorizedPaymentsFitBudget = factorizedPaymentsFitBudget I
  }

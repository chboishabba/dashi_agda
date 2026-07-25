module DASHI.Physics.Closure.NSPeriodicFarHighCanonicalEighthAdapter where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicFarHighTailCompletion as High
import DASHI.Physics.Closure.NSPeriodicCanonicalNearYoungAllocation as Budget
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Canonical R=8 far-high budget adapter.
--
-- The deterministic constants give a full two-placement tail of 1/16.  Since
-- the Wall-I allocation permits 1/8 = 2/16, the only remaining analytic input
-- here is the sharp estimate of the complete geometric tail by one sixteenth.
-- The comparison with the official eighth is derived, not assumed.
------------------------------------------------------------------------

record FarHighCanonicalEighthInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    base : High.PeriodicFarHighTailInputs A Index Time State
    sixteenthInterpretation : Budget.SixteenthBudgetInterpretation A

    sixteenthShareNonnegative :
      _≤_ A (zero A) (Budget.interpretedLowHigh sixteenthInterpretation)

    completeR8TailFitsOneSixteenth : ∀ q τ u →
      High.Admissible base q τ u →
      _≤_ A
        (High.geometricTailMajorant base q τ u)
        (Budget.interpretedLowHigh sixteenthInterpretation)

    officialFarHighBudgetIsEighth : ∀ q τ u →
      High.radiusEightOfficialBudget base q τ u
      ≡ _+_ A
          (Budget.interpretedLowHigh sixteenthInterpretation)
          (Budget.interpretedLowHigh sixteenthInterpretation)

open FarHighCanonicalEighthInputs public

oneSixteenthBelowOneEighth :
  ∀ {A : AbsorptionArithmetic} →
  (I : Budget.SixteenthBudgetInterpretation A) →
  _≤_ A (zero A) (Budget.interpretedLowHigh I) →
  _≤_ A
    (Budget.interpretedLowHigh I)
    (_+_ A (Budget.interpretedLowHigh I) (Budget.interpretedLowHigh I))
oneSixteenthBelowOneEighth {A = A} I shareNonnegative =
  summandBelowSum A
    (Budget.interpretedLowHigh I)
    (Budget.interpretedLowHigh I)
    shareNonnegative

farHighR8FullConstantFitsCanonicalEighth :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : FarHighCanonicalEighthInputs A Index Time State) →
  ∀ q τ u →
  High.Admissible (base I) q τ u →
  _≤_ A
    (High.geometricTailMajorant (base I) q τ u)
    (High.radiusEightOfficialBudget (base I) q τ u)
farHighR8FullConstantFitsCanonicalEighth {A = A} I q τ u admissible =
  substUpper
    (sym (officialFarHighBudgetIsEighth I q τ u))
    (≤-trans A
      (completeR8TailFitsOneSixteenth I q τ u admissible)
      (oneSixteenthBelowOneEighth
        (sixteenthInterpretation I)
        (sixteenthShareNonnegative I)))
  where
  substUpper : ∀ {x y z : Scalar A} →
    y ≡ z → _≤_ A x y → _≤_ A x z
  substUpper refl proof = proof

canonicalFarHighEighthEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : FarHighCanonicalEighthInputs A Index Time State) →
  ∀ q τ u →
  High.Admissible (base I) q τ u →
  _≤_ A
    (High.farHighTotal (base I) q τ u)
    (High.radiusEightOfficialBudget (base I) q τ u)
canonicalFarHighEighthEstimate {A = A} I q τ u admissible =
  ≤-trans A
    totalToGeometric
    (farHighR8FullConstantFitsCanonicalEighth I q τ u admissible)
  where
  totalToGeometric :
    _≤_ A
      (High.farHighTotal (base I) q τ u)
      (High.geometricTailMajorant (base I) q τ u)
  totalToGeometric =
    ≤-trans A
      totalToPlacement
      (≤-trans A
        (High.sobolevToHighShellTail (base I) q τ u admissible)
        (High.exactGeometricTailSummation (base I) q τ u admissible))

  totalToPlacement :
    _≤_ A
      (High.farHighTotal (base I) q τ u)
      (High.placementSum (base I) q τ u)
  totalToPlacement =
    substLower
      (High.exactPlacementDecomposition (base I) q τ u)
      (High.farHighPlacementSumBound (base I) q τ u admissible)

  substLower : ∀ {x y z : Scalar A} →
    x ≡ y → _≤_ A y z → _≤_ A x z
  substLower refl proof = proof

farHighCanonicalEighthAdapterLevel : ProofLevel
farHighCanonicalEighthAdapterLevel = machineChecked

module DASHI.Physics.Closure.NSPeriodicNearCanonicalQuarterAdapter where

open import Agda.Primitive using (Level; lsuc)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSPeriodicNearTriadCutoffUniformCompletion as Near
import DASHI.Physics.Closure.NSPeriodicCanonicalNearYoungAllocation as Young
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Canonical 1/4 adapter for the near interaction.
--
-- This module removes the remaining budget-combination field from the near
-- package.  An analytic implementation now has to prove only the three sharp
-- component bounds into the fixed 1/16, 1/16 and 1/8 shares.  Their sum is
-- forced to be the official quarter by the already checked denominator-sixteen
-- arithmetic.
------------------------------------------------------------------------

record NearCanonicalQuarterInputs
    {i : Level}
    (A : AbsorptionArithmetic)
    (Index Time State : Set i) : Set (lsuc i) where
  field
    base : Near.PeriodicNearTriadUniformInputs A Index Time State

    sixteenthInterpretation : Young.SixteenthBudgetInterpretation A

    lowHighFitsCanonicalShare : ∀ q τ u →
      _≤_ A
        (Near.lowHighUpper base q τ u)
        (Young.interpretedLowHigh sixteenthInterpretation)

    highLowFitsCanonicalShare : ∀ q τ u →
      _≤_ A
        (Near.highLowUpper base q τ u)
        (Young.interpretedHighLow sixteenthInterpretation)

    highHighFitsCanonicalShare : ∀ q τ u →
      _≤_ A
        (Near.highHighUpper base q τ u)
        (Young.interpretedHighHigh sixteenthInterpretation)

    officialNearBudgetIsQuarter : ∀ q τ u →
      Near.officialNearBudget base q τ u
      ≡ Young.interpretedQuarter sixteenthInterpretation

open NearCanonicalQuarterInputs public

nearCanonicalPaymentFit :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : NearCanonicalQuarterInputs A Index Time State) →
  ∀ q τ u →
  Young.CanonicalNearPaymentFit
    (sixteenthInterpretation I)
    (Near.lowHighUpper (base I) q τ u)
    (Near.highLowUpper (base I) q τ u)
    (Near.highHighUpper (base I) q τ u)
nearCanonicalPaymentFit I q τ u = record
  { lowHighFits = lowHighFitsCanonicalShare I q τ u
  ; highLowFits = highLowFitsCanonicalShare I q τ u
  ; highHighFits = highHighFitsCanonicalShare I q τ u
  }

canonicalNearUpperSumFitsQuarter :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : NearCanonicalQuarterInputs A Index Time State) →
  ∀ q τ u →
  _≤_ A
    (_+_ A
      (_+_ A
        (Near.lowHighUpper (base I) q τ u)
        (Near.highLowUpper (base I) q τ u))
      (Near.highHighUpper (base I) q τ u))
    (Near.officialNearBudget (base I) q τ u)
canonicalNearUpperSumFitsQuarter {A = A} I q τ u =
  substUpper
    (officialNearBudgetIsQuarter I q τ u |> sym)
    (Young.canonicalNearComponentsFitQuarter
      (nearCanonicalPaymentFit I q τ u))
  where
  infixl 0 _|>_
  _|>_ : ∀ {X Y : Set} → X → (X → Y) → Y
  x |> f = f x

  substUpper : ∀ {x y z : Scalar A} →
    y ≡ z → _≤_ A x y → _≤_ A x z
  substUpper refl proof = proof

canonicalNearQuarterEstimate :
  ∀ {i} {A : AbsorptionArithmetic} {Index Time State : Set i} →
  (I : NearCanonicalQuarterInputs A Index Time State) →
  ∀ q τ u →
  Near.Admissible (base I) q τ u →
  _≤_ A
    (Near.nearTotal (base I) q τ u)
    (Near.officialNearBudget (base I) q τ u)
canonicalNearQuarterEstimate {A = A} I q τ u admissible =
  ≤-trans A
    (Near.nearComponentSumBelowUpperSum (base I) q τ u admissible)
    (canonicalNearUpperSumFitsQuarter I q τ u)

------------------------------------------------------------------------
-- The analytic frontier is now exactly the three component-share estimates.
-- There is no fourth common-budget premise in this adapter.
------------------------------------------------------------------------

nearCanonicalQuarterAdapterLevel : ProofLevel
nearCanonicalQuarterAdapterLevel = machineChecked

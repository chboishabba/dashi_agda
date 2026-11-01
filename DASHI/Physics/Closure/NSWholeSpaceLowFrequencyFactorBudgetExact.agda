module DASHI.Physics.Closure.NSWholeSpaceLowFrequencyFactorBudgetExact where

------------------------------------------------------------------------
-- A / LOW-FREQUENCY FACTOR BUDGET
--
-- The origin payment need not come from one miraculous |xi|^6 estimate.
-- Split the physical state factor into
--
--   stateFactor = gramFactor * secondMomentFactor.
--
-- If the raw/projected Gram supplies one heat-rate factor and the remaining
-- centered/opposite-shift geometry supplies two,
--
--   gramFactor         <= a * gramMajorant,
--   secondMomentFactor <= a^2 * secondMomentMajorant,
--
-- then monotonicity and exact Bishop-real algebra give
--
--   stateFactor <= a^3 * (gramMajorant * secondMomentMajorant).
--
-- This is precisely the input consumed by
-- NSWholeSpaceLowFrequencyCompensationExact.  Thus after the quadratic Gram
-- homogeneity is welded to a physical norm bound, the genuinely new A theorem
-- is reduced to an a^2 ~ |xi|^4 residual second-moment payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Physics.Closure.NSWholeSpaceLowFrequencyCompensationExact as Low

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

record WholeSpaceLowFrequencyFactorBudget
    (a gramFactor secondMomentFactor
       gramMajorant secondMomentMajorant : BishopReal.ℝ) : Set where
  constructor whole-space-low-frequency-factor-budget
  field
    heatRateNonnegative :
      BishopReal.NonNegative a

    gramFactorNonnegative :
      BishopReal.NonNegative gramFactor

    secondMomentFactorNonnegative :
      BishopReal.NonNegative secondMomentFactor

    gramMajorantNonnegative :
      BishopReal.NonNegative gramMajorant

    secondMomentMajorantNonnegative :
      BishopReal.NonNegative secondMomentMajorant

    gramCarriesOneHeatRate :
      BishopReal._≤_
        gramFactor
        (BishopReal._*_ a gramMajorant)

    secondMomentCarriesTwoHeatRates :
      BishopReal._≤_
        secondMomentFactor
        (BishopReal._*_
          (square a)
          secondMomentMajorant)

open WholeSpaceLowFrequencyFactorBudget public

gramUpperNonnegative :
  ∀ {a gramFactor secondMomentFactor gramMajorant secondMomentMajorant} →
  WholeSpaceLowFrequencyFactorBudget
    a gramFactor secondMomentFactor gramMajorant secondMomentMajorant →
  BishopReal.NonNegative
    (BishopReal._*_ a gramMajorant)
gramUpperNonnegative budget =
  BishopP.nonNegx,y⇒nonNegx*y
    (heatRateNonnegative budget)
    (gramMajorantNonnegative budget)

secondMomentUpperNonnegative :
  ∀ {a gramFactor secondMomentFactor gramMajorant secondMomentMajorant} →
  WholeSpaceLowFrequencyFactorBudget
    a gramFactor secondMomentFactor gramMajorant secondMomentMajorant →
  BishopReal.NonNegative
    (BishopReal._*_
      (square a)
      secondMomentMajorant)
secondMomentUpperNonnegative {a} budget =
  let
    a2NN =
      BishopP.nonNegx,y⇒nonNegx*y
        (heatRateNonnegative budget)
        (heatRateNonnegative budget)
  in
  BishopP.nonNegx,y⇒nonNegx*y
    a2NN
    (secondMomentMajorantNonnegative budget)

factorProductBelowRawUpper :
  ∀ {a gramFactor secondMomentFactor gramMajorant secondMomentMajorant} →
  (budget :
    WholeSpaceLowFrequencyFactorBudget
      a gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant) →
  BishopReal._≤_
    (BishopReal._*_ gramFactor secondMomentFactor)
    (BishopReal._*_
      (BishopReal._*_ a gramMajorant)
      (BishopReal._*_
        (square a)
        secondMomentMajorant))
factorProductBelowRawUpper budget =
  BishopP.*-mono-≤
    (gramFactorNonnegative budget)
    (secondMomentFactorNonnegative budget)
    (gramCarriesOneHeatRate budget)
    (secondMomentCarriesTwoHeatRates budget)

rawUpperIsHeatCubeMajorant :
  (a gramMajorant secondMomentMajorant : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_ a gramMajorant)
      (BishopReal._*_
        (square a)
        secondMomentMajorant))
    (BishopReal._*_
      (Low.heatCube a)
      (BishopReal._*_ gramMajorant secondMomentMajorant))
rawUpperIsHeatCubeMajorant a gramMajorant secondMomentMajorant =
  let open BishopP.ℝ-Solver
  in
  solve 3
    (λ a′ g q →
      (a′ ⊗ g) ⊗ ((a′ ⊗ a′) ⊗ q)
      ⊜
      ((a′ ⊗ a′) ⊗ a′) ⊗ (g ⊗ q))
    BishopP.≃-refl
    a gramMajorant secondMomentMajorant

factorProductCarriesHeatCube :
  ∀ {a gramFactor secondMomentFactor gramMajorant secondMomentMajorant} →
  (budget :
    WholeSpaceLowFrequencyFactorBudget
      a gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant) →
  BishopReal._≤_
    (BishopReal._*_ gramFactor secondMomentFactor)
    (BishopReal._*_
      (Low.heatCube a)
      (BishopReal._*_ gramMajorant secondMomentMajorant))
factorProductCarriesHeatCube
    {a} {gramMajorant = gramMajorant}
    {secondMomentMajorant = secondMomentMajorant}
    budget =
  BishopP.≤-respʳ-≃
    (rawUpperIsHeatCubeMajorant
      a gramMajorant secondMomentMajorant)
    (factorProductBelowRawUpper budget)

factorBudgetToLowFrequencyCompensation :
  ∀ {a gramFactor secondMomentFactor gramMajorant secondMomentMajorant} →
  BishopReal._<_ BishopReal.0ℝ a →
  (budget :
    WholeSpaceLowFrequencyFactorBudget
      a gramFactor secondMomentFactor
      gramMajorant secondMomentMajorant) →
  Low.BishopLowFrequencyStateCompensation
    a
    (BishopReal._*_ gramFactor secondMomentFactor)
    (BishopReal._*_ gramMajorant secondMomentMajorant)
factorBudgetToLowFrequencyCompensation aPositive budget =
  Low.bishop-low-frequency-state-compensation
    aPositive
    (BishopP.nonNegx,y⇒nonNegx*y
      (gramFactorNonnegative budget)
      (secondMomentFactorNonnegative budget))
    (BishopP.nonNegx,y⇒nonNegx*y
      (gramMajorantNonnegative budget)
      (secondMomentMajorantNonnegative budget))
    (factorProductCarriesHeatCube budget)

------------------------------------------------------------------------
-- Exact frontier after this compiler:
--
--   Gram lane:         prove <= a * G on the projected physical cell.
--   Residual A lane:   prove <= a^2 * Q after signed opposite-shift geometry.
--
-- The latter is the remaining four-frequency-power theorem.
------------------------------------------------------------------------

heatCubeFactorBudgetCompilerClosed : Bool
heatCubeFactorBudgetCompilerClosed = true

gramHeatRatePowersRequired : Bool
gramHeatRatePowersRequired = true

secondMomentHeatRateSquaredRequired : Bool
secondMomentHeatRateSquaredRequired = true

physicalProjectedGramOneHeatRateClosedHere : Bool
physicalProjectedGramOneHeatRateClosedHere = false

physicalResidualTwoHeatRatesClosedHere : Bool
physicalResidualTwoHeatRatesClosedHere = false

clayPromotion : Bool
clayPromotion = false

heatCubeFactorBudgetCompilerClosedIsTrue :
  heatCubeFactorBudgetCompilerClosed ≡ true
heatCubeFactorBudgetCompilerClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

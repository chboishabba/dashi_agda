module DASHI.Moonshine.GoldenRatioBalancedFRACTRANDenominatorGrowthExact where

------------------------------------------------------------------------
-- EXACT DENOMINATOR GROWTH FOR THE BALANCED-FRACTRAN FIBONACCI RATIOS
--
-- For one [-,+] macro (= two Fibonacci steps), the new denominator is
--
--     q' = p + q.
--
-- Because p is definitionally positive, q strictly grows.  We strengthen this
-- to the explicit linear lower bound n+1 <= q_n and hence a Nat-level escape
-- certificate: every finite Nat bound is eventually met/exceeded.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_≤_; z≤n; s≤s)

import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio

------------------------------------------------------------------------
-- 1. Small constructive Nat-order lemmas kept local to this owner.
------------------------------------------------------------------------

nat≤refl : (n : Nat) → n ≤ n
nat≤refl zero = z≤n
nat≤refl (suc n) = s≤s (nat≤refl n)

nat≤trans : {a b c : Nat} → a ≤ b → b ≤ c → a ≤ c
nat≤trans z≤n _ = z≤n
nat≤trans (s≤s left) (s≤s right) = s≤s (nat≤trans left right)

nat≤sucSelf : (n : Nat) → n ≤ suc n
nat≤sucSelf zero = z≤n
nat≤sucSelf (suc n) = s≤s (nat≤sucSelf n)

nat≤rightSlack : (slack n : Nat) → n ≤ slack + n
nat≤rightSlack zero n = nat≤refl n
nat≤rightSlack (suc slack) n =
  nat≤trans (nat≤rightSlack slack n) (nat≤sucSelf (slack + n))

------------------------------------------------------------------------
-- 2. One macro has an exact positive additive denominator increment.
------------------------------------------------------------------------

macroDenominatorLaw :
  (pair : Ratio.PositiveFibPair) →
  Ratio.positiveLo (Ratio.positiveFibTwoStep pair)
  ≡ Ratio.positiveHi pair + Ratio.positiveLo pair
macroDenominatorLaw (Ratio.positiveFibPair a b) = refl

record PositiveIncrementReceipt (current next : Nat) : Set where
  constructor positive-increment-receipt
  field
    incrementPred : Nat
    nextIsPositiveIncrementPlusCurrent :
      next ≡ suc incrementPred + current

open PositiveIncrementReceipt public

macroDenominatorPositiveIncrement :
  (pair : Ratio.PositiveFibPair) →
  PositiveIncrementReceipt
    (Ratio.positiveLo pair)
    (Ratio.positiveLo (Ratio.positiveFibTwoStep pair))
macroDenominatorPositiveIncrement (Ratio.positiveFibPair a b) =
  positive-increment-receipt a refl

macroDenominatorAddsAtLeastOne :
  (pair : Ratio.PositiveFibPair) →
  suc (Ratio.positiveLo pair)
  ≤ Ratio.positiveLo (Ratio.positiveFibTwoStep pair)
macroDenominatorAddsAtLeastOne (Ratio.positiveFibPair a b) =
  s≤s (nat≤rightSlack a (suc b))

------------------------------------------------------------------------
-- 3. Iterated growth and linear lower bound.
------------------------------------------------------------------------

iteratedDenominatorPositiveIncrement :
  (n : Nat) →
  PositiveIncrementReceipt
    (Ratio.positiveLo (Ratio.iteratePositiveMacro n))
    (Ratio.positiveLo (Ratio.iteratePositiveMacro (suc n)))
iteratedDenominatorPositiveIncrement n =
  macroDenominatorPositiveIncrement (Ratio.iteratePositiveMacro n)

iteratedDenominatorAddsAtLeastOne :
  (n : Nat) →
  suc (Ratio.positiveLo (Ratio.iteratePositiveMacro n))
  ≤ Ratio.positiveLo (Ratio.iteratePositiveMacro (suc n))
iteratedDenominatorAddsAtLeastOne n =
  macroDenominatorAddsAtLeastOne (Ratio.iteratePositiveMacro n)

linearDenominatorLowerBound :
  (n : Nat) →
  suc n ≤ Ratio.positiveLo (Ratio.iteratePositiveMacro n)
linearDenominatorLowerBound zero = s≤s z≤n
linearDenominatorLowerBound (suc n) =
  nat≤trans
    (s≤s (linearDenominatorLowerBound n))
    (iteratedDenominatorAddsAtLeastOne n)

record NatEscapesEveryBound (sequence : Nat → Nat) : Set where
  constructor nat-escapes-every-bound
  field
    indexFor : Nat → Nat
    boundPaid : (bound : Nat) → bound ≤ sequence (indexFor bound)

open NatEscapesEveryBound public

balancedFibDenominatorEscapesEveryBound :
  NatEscapesEveryBound
    (λ n → Ratio.positiveLo (Ratio.iteratePositiveMacro n))
balancedFibDenominatorEscapesEveryBound =
  nat-escapes-every-bound
    (λ bound → bound)
    (λ bound →
      nat≤trans
        (nat≤sucSelf bound)
        (linearDenominatorLowerBound bound))

------------------------------------------------------------------------
-- 4. Concrete regression values line up with the ratio carrier.
------------------------------------------------------------------------

denominator0 : Ratio.positiveLo (Ratio.iteratePositiveMacro 0) ≡ 1
denominator0 = refl

denominator1 : Ratio.positiveLo (Ratio.iteratePositiveMacro 1) ≡ 3
denominator1 = refl

denominator2 : Ratio.positiveLo (Ratio.iteratePositiveMacro 2) ≡ 8
denominator2 = refl

denominator3 : Ratio.positiveLo (Ratio.iteratePositiveMacro 3) ≡ 21
denominator3 = refl

------------------------------------------------------------------------
-- 5. Frontier.
--
-- Nat-level divergence is now exact.  The remaining analytic obligation is to
-- convert the constant norm-one defect plus growing denominator into a Bishop
-- real error bound, then discharge ConvergesTo on the vendored carrier.
------------------------------------------------------------------------

data DenominatorGrowthResidual : Set where
  missingQuadraticDefectToBishopErrorBound : DenominatorGrowthResidual
  missingBalancedFRACTRANRatioConvergenceToBishopPhi : DenominatorGrowthResidual

record DenominatorGrowthFrontier : Set where
  constructor denominator-growth-frontier
  field
    positiveDenominatorByConstruction : Bool
    oneMacroDenominatorLawExact : Bool
    everyMacroHasPositiveIncrementReceipt : Bool
    linearLowerBoundExact : Bool
    denominatorEscapesEveryNatBound : Bool
    defectToBishopErrorBoundProved : Bool
    convergenceToBishopPhiProved : Bool
    firstResidual : DenominatorGrowthResidual

canonicalDenominatorGrowthFrontier : DenominatorGrowthFrontier
canonicalDenominatorGrowthFrontier =
  denominator-growth-frontier
    true true true true true false false
    missingQuadraticDefectToBishopErrorBound

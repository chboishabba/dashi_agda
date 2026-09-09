module DASHI.Moonshine.GoldenRatioBalancedFRACTRANDenominatorGrowthExact where

------------------------------------------------------------------------
-- EXACT DENOMINATOR GROWTH FOR THE BALANCED-FRACTRAN FIBONACCI RATIOS
--
-- The Bishop ratio carrier already exists.  This owner pays the finite/growth
-- half of its remaining convergence debt without pretending to prove a real
-- limit theorem.  For one [-,+] macro (= two Fibonacci steps), the new
-- denominator is exactly
--
--     q' = p + q,
--
-- so every macro adds the previous positive numerator to the denominator.
-- Positivity is definitional because PositiveFibPair stores predecessor Nats.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio

------------------------------------------------------------------------
-- 1. One macro has an exact positive additive denominator increment.
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

------------------------------------------------------------------------
-- 2. The iterated Bishop-ratio sequence therefore carries a positive growth
-- receipt at every macro depth.
------------------------------------------------------------------------

iteratedDenominatorPositiveIncrement :
  (n : Nat) →
  PositiveIncrementReceipt
    (Ratio.positiveLo (Ratio.iteratePositiveMacro n))
    (Ratio.positiveLo (Ratio.iteratePositiveMacro (suc n)))
iteratedDenominatorPositiveIncrement n =
  macroDenominatorPositiveIncrement (Ratio.iteratePositiveMacro n)

------------------------------------------------------------------------
-- 3. Concrete regression values line up with the ratio carrier.
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
-- 4. Frontier.
--
-- Exact positive growth per step is weaker than the quantified Archimedean
-- statement q_n -> infinity required by the Bishop convergence proof.  Keep
-- those obligations distinct.
------------------------------------------------------------------------

data DenominatorGrowthResidual : Set where
  missingIteratedDenominatorDivergence : DenominatorGrowthResidual
  missingQuadraticDefectToBishopErrorBound : DenominatorGrowthResidual
  missingBalancedFRACTRANRatioConvergenceToBishopPhi : DenominatorGrowthResidual

record DenominatorGrowthFrontier : Set where
  constructor denominator-growth-frontier
  field
    positiveDenominatorByConstruction : Bool
    oneMacroDenominatorLawExact : Bool
    everyMacroHasPositiveIncrementReceipt : Bool
    denominatorDivergenceProved : Bool
    defectToBishopErrorBoundProved : Bool
    convergenceToBishopPhiProved : Bool
    firstResidual : DenominatorGrowthResidual

canonicalDenominatorGrowthFrontier : DenominatorGrowthFrontier
canonicalDenominatorGrowthFrontier =
  denominator-growth-frontier
    true true true false false false
    missingIteratedDenominatorDivergence

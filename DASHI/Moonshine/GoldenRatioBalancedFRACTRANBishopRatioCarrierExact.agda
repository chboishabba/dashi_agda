module DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact where

------------------------------------------------------------------------
-- BALANCED-FRACTRAN FIBONACCI RATIOS ON THE VENDORED BISHOP REAL CARRIER
--
-- The repository vendors viktorcsimma/bishop as vendor/bishop, pinned at
-- commit 240e38c7f6938f20f865b1f956c5f084da48bd54.
--
-- This owner pays only the old positive-real ratio-carrier residual.  It does
-- not yet prove convergence to phi_B.  Positivity is carried definitionally:
-- a PositiveFibPair stores predecessor naturals, so both numerator and
-- denominator are successors and the rational denominator is never zero.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (ℚᵘ; _/_)

import Real as BishopReal
import DASHI.Foundations.BishopConstructiveRealBridgeExact as BishopBridge
import DASHI.Foundations.BishopGoldenRatioCarrierExact as Phi

------------------------------------------------------------------------
-- 1. Positive Fibonacci pairs.
------------------------------------------------------------------------

record PositiveFibPair : Set where
  constructor positiveFibPair
  field
    hiPred loPred : Nat

open PositiveFibPair public

positiveHi : PositiveFibPair → Nat
positiveHi pair = suc (hiPred pair)

positiveLo : PositiveFibPair → Nat
positiveLo pair = suc (loPred pair)

-- If (hi,lo)=(1+a,1+b), one Fibonacci update is
--
--   (hi+lo,hi)
-- = (1 + (a + (1+b)), 1+a).
positiveFibStep : PositiveFibPair → PositiveFibPair
positiveFibStep (positiveFibPair a b) =
  positiveFibPair (a + suc b) a

positiveFibTwoStep : PositiveFibPair → PositiveFibPair
positiveFibTwoStep pair = positiveFibStep (positiveFibStep pair)

positiveStart : PositiveFibPair
positiveStart = positiveFibPair 1 0

positiveStartIsTwoOne :
  (positiveHi positiveStart ≡ 2) × (positiveLo positiveStart ≡ 1)
positiveStartIsTwoOne = refl , refl

positiveTwoStepOnceIsFiveThree :
  (positiveHi (positiveFibTwoStep positiveStart) ≡ 5)
  × (positiveLo (positiveFibTwoStep positiveStart) ≡ 3)
positiveTwoStepOnceIsFiveThree = refl , refl

positiveTwoStepTwiceIsThirteenEight :
  (positiveHi (positiveFibTwoStep (positiveFibTwoStep positiveStart)) ≡ 13)
  × (positiveLo (positiveFibTwoStep (positiveFibTwoStep positiveStart)) ≡ 8)
positiveTwoStepTwiceIsThirteenEight = refl , refl

positiveTwoStepThriceIsThirtyFourTwentyOne :
  (positiveHi
    (positiveFibTwoStep
      (positiveFibTwoStep (positiveFibTwoStep positiveStart))) ≡ 34)
  ×
  (positiveLo
    (positiveFibTwoStep
      (positiveFibTwoStep (positiveFibTwoStep positiveStart))) ≡ 21)
positiveTwoStepThriceIsThirtyFourTwentyOne = refl , refl

iteratePositiveMacro : Nat → PositiveFibPair
iteratePositiveMacro zero = positiveStart
iteratePositiveMacro (suc n) = positiveFibTwoStep (iteratePositiveMacro n)

------------------------------------------------------------------------
-- 2. Exact rational and Bishop-real ratios.
------------------------------------------------------------------------

positiveRatioRational : PositiveFibPair → ℚᵘ
positiveRatioRational pair =
  + positiveHi pair / positiveLo pair

positiveRatioBishop : PositiveFibPair → BishopReal.ℝ
positiveRatioBishop pair = BishopReal._⋆ (positiveRatioRational pair)

balancedFRACTRANBishopRatioSequence : Nat → BishopReal.ℝ
balancedFRACTRANBishopRatioSequence n =
  positiveRatioBishop (iteratePositiveMacro n)

ratio0IsTwoOverOne :
  positiveRatioRational (iteratePositiveMacro 0) ≡ (+ 2 / 1)
ratio0IsTwoOverOne = refl

ratio1IsFiveOverThree :
  positiveRatioRational (iteratePositiveMacro 1) ≡ (+ 5 / 3)
ratio1IsFiveOverThree = refl

ratio2IsThirteenOverEight :
  positiveRatioRational (iteratePositiveMacro 2) ≡ (+ 13 / 8)
ratio2IsThirteenOverEight = refl

ratio3IsThirtyFourOverTwentyOne :
  positiveRatioRational (iteratePositiveMacro 3) ≡ (+ 34 / 21)
ratio3IsThirtyFourOverTwentyOne = refl

------------------------------------------------------------------------
-- 3. Same Bishop carrier as the constructed golden ratio.
------------------------------------------------------------------------

BishopRatioConvergesToPhi : Set
BishopRatioConvergesToPhi =
  BishopBridge.BishopConvergesTo
    balancedFRACTRANBishopRatioSequence
    Phi.bishopPhi

------------------------------------------------------------------------
-- 4. Vendor provenance / frontier.
------------------------------------------------------------------------

bishopVendorPath : String
bishopVendorPath = "vendor/bishop"

bishopVendorCommit : String
bishopVendorCommit = "240e38c7f6938f20f865b1f956c5f084da48bd54"

record BalancedFRACTRANBishopRatioFrontier : Set where
  constructor balanced-fractran-bishop-ratio-frontier
  field
    bishopImplementationVendored : Bool
    bishopVendorPinRecorded : Bool
    positiveDenominatorByConstruction : Bool
    finiteRatioSequenceConstructedOnBishopCarrier : Bool
    targetIsExistingBishopPhi : Bool
    convergenceToBishopPhiProved : Bool

canonicalBalancedFRACTRANBishopRatioFrontier :
  BalancedFRACTRANBishopRatioFrontier
canonicalBalancedFRACTRANBishopRatioFrontier =
  balanced-fractran-bishop-ratio-frontier
    true true true true true false

data BishopRatioResidual : Set where
  missingBalancedFRACTRANRatioConvergenceToBishopPhi : BishopRatioResidual

firstResidual : BishopRatioResidual
firstResidual = missingBalancedFRACTRANRatioConvergenceToBishopPhi

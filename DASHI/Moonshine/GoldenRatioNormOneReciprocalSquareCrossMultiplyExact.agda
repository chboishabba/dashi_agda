module DASHI.Moonshine.GoldenRatioNormOneReciprocalSquareCrossMultiplyExact where

------------------------------------------------------------------------
-- DENOMINATOR-CLEARED NORM-ONE -> RECIPROCAL-SQUARE WELD
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Moonshine.GoldenRatioBalancedFRACTRANBishopRatioCarrierExact as Ratio
import DASHI.Moonshine.GoldenRatioBalancedFRACTRANNormOneInvariantExact as Norm

NormOneCleared : Nat → Nat → Set
NormOneCleared p q = p * p ≡ p * q + q * q + 1

normOneCrossMultiply :
  (p q : Nat) → Norm.NormOne p q → NormOneCleared p q
normOneCrossMultiply p q norm = norm

reciprocalSquareClearedForm :
  (p q : Nat) →
  Norm.NormOne p q →
  p * p ≡ (p * q + q * q) + 1
reciprocalSquareClearedForm p q norm = norm

balancedMacroReciprocalSquareCleared :
  (n : Nat) →
  let pair = Ratio.iteratePositiveMacro n
      p = Ratio.positiveHi pair
      q = Ratio.positiveLo pair
  in
  p * p ≡ (p * q + q * q) + 1
balancedMacroReciprocalSquareCleared n = Norm.balancedMacroNormOne n

-- An addition-only rearrangement useful after denominator clearing.
clearedDefectBalance :
  (p q : Nat) →
  Norm.NormOne p q →
  p * p + q * q ≡ p * q + (q * q + q * q) + 1
clearedDefectBalance p q norm =
  trans
    (cong (λ x → x + q * q) norm)
    (solve 2
      (λ p q →
        ((((p :* q) :+ (q :* q)) :+ con 1) :+ (q :* q))
        :=
        ((p :* q) :+ ((q :* q) :+ (q :* q))) :+ con 1)
      refl p q)

data ReciprocalSquareCrossMultiplyResidual : Set where
  missingUnnormalisedRationalEquivalenceLift : ReciprocalSquareCrossMultiplyResidual
  missingBishopEmbeddingEquivalenceLift : ReciprocalSquareCrossMultiplyResidual
  missingConjugateFactorLowerBound : ReciprocalSquareCrossMultiplyResidual
  missingFinalConvergence : ReciprocalSquareCrossMultiplyResidual

record ReciprocalSquareCrossMultiplyFrontier : Set where
  constructor reciprocal-square-cross-multiply-frontier
  field
    allMacroStatesNormOne : Bool
    denominatorClearedReciprocalSquareExact : Bool
    rationalEquivalenceLiftExact : Bool
    bishopEmbeddingLiftExact : Bool
    firstResidual : ReciprocalSquareCrossMultiplyResidual

canonicalReciprocalSquareCrossMultiplyFrontier :
  ReciprocalSquareCrossMultiplyFrontier
canonicalReciprocalSquareCrossMultiplyFrontier =
  reciprocal-square-cross-multiply-frontier
    true true false false
    missingUnnormalisedRationalEquivalenceLift

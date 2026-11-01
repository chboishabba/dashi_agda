module DASHI.Foundations.BishopEventualAbsoluteComparisonExact where

------------------------------------------------------------------------
-- EVENTUAL ABSOLUTE COMPARISON -> SERIES CONVERGENCE
--
-- Thin reusable wrapper around the checked Bishop comparison theorem
-- Sequence.proposition-3-5.
--
-- If sum M_n converges and eventually |a_n| <= M_n, then sum a_n converges.
-- The finite prefix is handled by Bishop's theorem; no separate prefix
-- convergence proof is required here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (_,_)

import Real as BishopReal
import Sequence as BishopSequence

open import DASHI.Physics.YangMills.CompactLieProofLevel

record EventualAbsoluteMajorant
    (target majorant : Nat → BishopReal.ℝ) : Set₁ where
  constructor eventual-absolute-majorant
  field
    majorantSeriesConvergent :
      BishopSequence._isConvergent
        (BishopSequence.SeriesOf majorant)

    transitionIndex : Nat

    targetEventuallyBelowMajorant :
      (n : Nat) →
      transitionIndex ≤ n →
      BishopReal._≤_
        (BishopReal.∣ target n ∣)
        (majorant n)

open EventualAbsoluteMajorant public

eventualAbsoluteComparisonConverges :
  ∀ {target majorant} →
  EventualAbsoluteMajorant target majorant →
  BishopSequence._isConvergent
    (BishopSequence.SeriesOf target)
eventualAbsoluteComparisonConverges witness =
  BishopSequence.proposition-3-5
    (majorantSeriesConvergent witness)
    (transitionIndex witness ,
      targetEventuallyBelowMajorant witness)

record EventualAbsoluteComparisonBoundary : Set where
  constructor eventual-absolute-comparison-boundary
  field
    bishopComparisonTheoremReused : Bool
    finitePrefixHandledByTheorem : Bool
    targetSeriesConvergenceCompiled : Bool

open import Agda.Builtin.Bool using (Bool; true)
open EventualAbsoluteComparisonBoundary public

canonicalEventualAbsoluteComparisonBoundary :
  EventualAbsoluteComparisonBoundary
canonicalEventualAbsoluteComparisonBoundary =
  eventual-absolute-comparison-boundary true true true

bishopEventualAbsoluteComparisonLevel : ProofLevel
bishopEventualAbsoluteComparisonLevel = machineChecked

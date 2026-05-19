module DASHI.Arithmetic.EpsilonBound where

open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Nat using (_≤_)

open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using
  ( Int
  )
open import DASHI.Arithmetic.DeltaGrowth using
  ( logNat
  )
open import DASHI.Arithmetic.MaxPressure using
  ( weightedMaxPressure
  )
open import DASHI.Arithmetic.WeightedPressure using
  ( weightedPressure
  )

------------------------------------------------------------------------
-- Compile-thin tracked epsilon surface.
--
-- The explicit tracked constant is kept separate from the frontier theorem
-- so that downstream packaging can reuse the constant without repeating the
-- bound shape.

trackedPrimeLogConstant : Nat
trackedPrimeLogConstant = logNat 71

postulate
  explicitTrackedEpsilonBound :
    ∀ x y →
    weightedPressure x y ≤
      trackedPrimeLogConstant * suc (logNat (weightedMaxPressure x y)) * logNat (x + y)

record TrackedEpsilonBoundStructure : Set₁ where
  field
    logarithm : Nat → Nat
    trackedPrimeLog : Nat
    weightedGlobal : Int → Int → Nat
    explicitBound :
      ∀ x y →
      weightedGlobal x y ≤
        trackedPrimeLog * suc (logarithm (weightedMaxPressure x y)) * logarithm (x + y)

open TrackedEpsilonBoundStructure public

trackedEpsilonBoundStructure : TrackedEpsilonBoundStructure
trackedEpsilonBoundStructure = record
  { logarithm = logNat
  ; trackedPrimeLog = trackedPrimeLogConstant
  ; weightedGlobal = weightedPressure
  ; explicitBound = explicitTrackedEpsilonBound
  }

trackedWeightedEpsilonBound :
  ∀ x y →
  weightedPressure x y ≤
    trackedPrimeLogConstant * suc (logNat (weightedMaxPressure x y)) * logNat (x + y)
trackedWeightedEpsilonBound = explicitTrackedEpsilonBound

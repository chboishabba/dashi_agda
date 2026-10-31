module DASHI.Analysis.RiemannQuasiRHXiSymmetryReuseExact where

-- Independent DASHI integration of an external zero-free statement.
-- Original finite coordinate geometry belongs to RiemannXiSymmetryExact.
-- The external OpenAI quasi-RH manuscript is NOT kernel-proved here.
-- This module reuses, rather than reproduces, the existing critical
-- reflection and its involutive law.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact as Xi

-- Actual analytic zeros must be mapped to finite rational coordinates
-- only when such a coordinate realization exists. For general zeros,
-- rational coordinates are NOT a faithful analytic embedding; use this
-- finite owner only for a rational geometry/observer representation.

record RationalZeroObserver (Zero : Set) : Set₁ where
  field
    coordinate : Zero → Xi.ComplexCoordinate
    reflectedZero : Zero → Zero
    reflectionPreserved : (z : Zero) →
      coordinate (reflectedZero z) ≡ Xi.criticalReflection (coordinate z)
open RationalZeroObserver public

record ImportedRightExclusion {Zero : Set}
    (observer : RationalZeroObserver Zero)
    (rightOfBound : Xi.ComplexCoordinate → Set) : Set₁ where
  field
    exclude : (z : Zero) → rightOfBound (coordinate observer z) → ⊥
open ImportedRightExclusion public

leftOfBound :
  ∀ {Zero : Set}
  (observer : RationalZeroObserver Zero)
  (rightOfBound : Xi.ComplexCoordinate → Set)
  (z : Zero) → Set
leftOfBound observer rightOfBound z =
  rightOfBound (Xi.criticalReflection (coordinate observer z))

excludeLeftByNativeReflection :
  ∀ {Zero : Set}
  (observer : RationalZeroObserver Zero)
  (rightOfBound : Xi.ComplexCoordinate → Set)
  (claim : ImportedRightExclusion observer rightOfBound)
  (z : Zero) →
  leftOfBound observer rightOfBound z → ⊥
excludeLeftByNativeReflection observer rightOfBound claim z left =
  exclude claim (reflectedZero observer z)
    (substRight (reflectionPreserved observer z) left)
  where
    substRight :
      ∀ {a b : Xi.ComplexCoordinate} →
      a ≡ b → rightOfBound b → rightOfBound a
    substRight refl value = value

nativeReflectionTwice :
  (point : Xi.ComplexCoordinate) →
  Xi.criticalReflection (Xi.criticalReflection point) ≡ point
nativeReflectionTwice = Xi.criticalReflectionInvolutive

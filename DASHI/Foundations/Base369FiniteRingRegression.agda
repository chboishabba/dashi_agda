module DASHI.Foundations.Base369FiniteRingRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_*_)

open import Base369 using
  ( HexTruth
  ; NonaryTruth
  ; TriTruth
  ; fromHexIndex
  ; fromNonaryIndex
  ; fromTriIndex
  ; hex-0
  ; hex-2
  ; hex-3
  ; hex-index
  ; non-0
  ; non-3
  ; non-6
  ; nonary-index
  ; tri-high
  ; tri-low
  ; tri-mid
  ; tri-index
  ; triXor
  )

------------------------------------------------------------------------
-- Local concrete modular operations used as regression sentinels.
--
-- The abstract finite-ring shape module currently does not typecheck as a
-- dependency when checked standalone, so this regression anchors directly on
-- the stable Base369 carriers and constructors.

triAdd : TriTruth → TriTruth → TriTruth
triAdd = triXor

triMul : TriTruth → TriTruth → TriTruth
triMul x y = fromTriIndex (tri-index x * tri-index y)

triNeg : TriTruth → TriTruth
triNeg tri-low  = tri-low
triNeg tri-mid  = tri-high
triNeg tri-high = tri-mid

hexMul : HexTruth → HexTruth → HexTruth
hexMul x y = fromHexIndex (hex-index x * hex-index y)

nonaryMul : NonaryTruth → NonaryTruth → NonaryTruth
nonaryMul x y = fromNonaryIndex (nonary-index x * nonary-index y)

------------------------------------------------------------------------
-- Concrete smoke-test equalities.  These intentionally remain refl-only:
-- if a constructor table or modular representative changes, this file fails.

triTruth-mul-1*2 : triMul tri-mid tri-high ≡ tri-high
triTruth-mul-1*2 = refl

triTruth-mul-2*2 : triMul tri-high tri-high ≡ tri-mid
triTruth-mul-2*2 = refl

triTruth-neg-1 : triNeg tri-mid ≡ tri-high
triTruth-neg-1 = refl

triTruth-neg-2 : triNeg tri-high ≡ tri-mid
triTruth-neg-2 = refl

triTruth-add-neg-1 : triAdd (triNeg tri-mid) tri-mid ≡ tri-low
triTruth-add-neg-1 = refl

triTruth-add-neg-2 : triAdd (triNeg tri-high) tri-high ≡ tri-low
triTruth-add-neg-2 = refl

hex-zero-divisor-2*3 : hexMul hex-2 hex-3 ≡ hex-0
hex-zero-divisor-2*3 = refl

hex-zero-divisor-3*2 : hexMul hex-3 hex-2 ≡ hex-0
hex-zero-divisor-3*2 = refl

nonary-zero-divisor-3*3 : nonaryMul non-3 non-3 ≡ non-0
nonary-zero-divisor-3*3 = refl

nonary-zero-divisor-3*6 : nonaryMul non-3 non-6 ≡ non-0
nonary-zero-divisor-3*6 = refl

------------------------------------------------------------------------
-- Canonical regression flags.

base369FiniteRingRegressionRecorded : Bool
base369FiniteRingRegressionRecorded = true

triTruthRepresentativeSmokeAccepted : Bool
triTruthRepresentativeSmokeAccepted = true

hexZeroDivisorSmokeAccepted : Bool
hexZeroDivisorSmokeAccepted = true

nonaryZeroDivisorSmokeAccepted : Bool
nonaryZeroDivisorSmokeAccepted = true

base369FiniteRingRegressionPromotesFieldClaim : Bool
base369FiniteRingRegressionPromotesFieldClaim = false

base369FiniteRingRegressionRecorded-is-true :
  base369FiniteRingRegressionRecorded ≡ true
base369FiniteRingRegressionRecorded-is-true = refl

triTruthRepresentativeSmokeAccepted-is-true :
  triTruthRepresentativeSmokeAccepted ≡ true
triTruthRepresentativeSmokeAccepted-is-true = refl

hexZeroDivisorSmokeAccepted-is-true :
  hexZeroDivisorSmokeAccepted ≡ true
hexZeroDivisorSmokeAccepted-is-true = refl

nonaryZeroDivisorSmokeAccepted-is-true :
  nonaryZeroDivisorSmokeAccepted ≡ true
nonaryZeroDivisorSmokeAccepted-is-true = refl

base369FiniteRingRegressionPromotesFieldClaim-is-false :
  base369FiniteRingRegressionPromotesFieldClaim ≡ false
base369FiniteRingRegressionPromotesFieldClaim-is-false = refl

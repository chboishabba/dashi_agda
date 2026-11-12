{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanT4TightRangeDoesNotDetermineIntegralExact where

------------------------------------------------------------------------
-- SOURCE-CORRECT NEGATIVE CONTROL FOR THE LITERAL T4 QUADRATURE CUT.
--
-- A certified *tight* pointwise range [0,1] does not determine an
-- integral. The 4-point finite measure countermodel below gives two
-- nonnegative functions with EXACTLY the same attained min and max,
-- but distinct integrals (un-normalized masses 1 and 3).
--
-- This is a mathematical no-go for extracting exact quadrature from the
-- range alone. It does not claim that interval-enclosure + certified
-- volume bounds are invalid: those still give sound coarse bounds.
--
-- Real box volume, Taylor/Hessian/modulus remainder, and literal
-- Wilson/ghost/Haar source ownership remain physical P0 obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Empty using (⊥)

data Site4 : Set where
  s0 s1 s2 s3 : Site4

one three : Nat
one = suc zero
three = suc (suc (suc zero))

data BetweenZeroAndOne : Nat → Set where
  exactlyZero : BetweenZeroAndOne zero
  exactlyOne : BetweenZeroAndOne one

record TightRangeZeroOne (field : Site4 → Nat) : Set where
  constructor tight-range
  field
    allValuesWithin : ∀ site → BetweenZeroAndOne (field site)
    zeroAttained : field s0 ≡ zero
    oneAttained : field s3 ≡ one

open TightRangeZeroOne public

smallMassField : Site4 → Nat
smallMassField s0 = zero
smallMassField s1 = zero
smallMassField s2 = zero
smallMassField s3 = one

largeMassField : Site4 → Nat
largeMassField s0 = zero
largeMassField s1 = one
largeMassField s2 = one
largeMassField s3 = one

smallMassRange : TightRangeZeroOne smallMassField
smallMassRange = tight-range certificate refl refl
  where
    certificate : ∀ site → BetweenZeroAndOne (smallMassField site)
    certificate s0 = exactlyZero
    certificate s1 = exactlyZero
    certificate s2 = exactlyZero
    certificate s3 = exactlyOne

largeMassRange : TightRangeZeroOne largeMassField
largeMassRange = tight-range certificate refl refl
  where
    certificate : ∀ site → BetweenZeroAndOne (largeMassField site)
    certificate s0 = exactlyZero
    certificate s1 = exactlyOne
    certificate s2 = exactlyOne
    certificate s3 = exactlyOne

finiteIntegral : (Site4 → Nat) → Nat
finiteIntegral field =
  field s0 + (field s1 + (field s2 + field s3))

smallIntegralExact : finiteIntegral smallMassField ≡ one
smallIntegralExact = refl

largeIntegralExact : finiteIntegral largeMassField ≡ three
largeIntegralExact = refl

oneNotThree : one ≡ three → ⊥
oneNotThree ()

sameSymmetric : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sameSymmetric refl = refl

sameTransitive : ∀ {A : Set} {x y z : A} →
  x ≡ y → y ≡ z → x ≡ z
sameTransitive refl proof = proof

-- Even the *attained*, not merely loose, extrema are insufficient to
-- reconstruct an exact mass on a fixed four-site measure space.
-- An analogous continuum example uses two functions with the same
-- attained min/max but different integrals.
noExactIntegralFromTightRangeAlone :
  (estimator : Nat → Nat → Nat) →
  ((field : Site4 → Nat) →
    TightRangeZeroOne field →
    estimator zero one ≡ finiteIntegral field) →
  ⊥
noExactIntegralFromTightRangeAlone estimator universal =
  oneNotThree
    (sameTransitive
      (sameSymmetric
        (sameTransitive
          (universal smallMassField smallMassRange)
          (sameSymmetric smallIntegralExact)))
      (sameTransitive
        (universal largeMassField largeMassRange)
        largeIntegralExact))

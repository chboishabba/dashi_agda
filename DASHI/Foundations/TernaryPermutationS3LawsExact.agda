module DASHI.Foundations.TernaryPermutationS3LawsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- DASHI CONTRIBUTION
--
-- Close the six explicit ternary coordinate permutations under composition
-- and prove the finite group/action laws by exhaustive constructor reduction.
-- This upgrades the six-carrier used by TernaryEndomorphismConjugacyExact from
-- "six named invertible maps" to an exact nonabelian S3 group surface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import Base369 as Base
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as S3

open S3 using
  ( TriPermutation
  ; permIdentity
  ; permRotate
  ; permRotate2
  ; permSwapLowMid
  ; permSwapLowHigh
  ; permSwapMidHigh
  ; applyPermutation
  ; inversePermutation
  )

infixl 7 _∙_

_∙_ : TriPermutation → TriPermutation → TriPermutation
permIdentity ∙ permIdentity = permIdentity
permIdentity ∙ permRotate = permRotate
permIdentity ∙ permRotate2 = permRotate2
permIdentity ∙ permSwapLowMid = permSwapLowMid
permIdentity ∙ permSwapLowHigh = permSwapLowHigh
permIdentity ∙ permSwapMidHigh = permSwapMidHigh
permRotate ∙ permIdentity = permRotate
permRotate ∙ permRotate = permRotate2
permRotate ∙ permRotate2 = permIdentity
permRotate ∙ permSwapLowMid = permSwapLowHigh
permRotate ∙ permSwapLowHigh = permSwapMidHigh
permRotate ∙ permSwapMidHigh = permSwapLowMid
permRotate2 ∙ permIdentity = permRotate2
permRotate2 ∙ permRotate = permIdentity
permRotate2 ∙ permRotate2 = permRotate
permRotate2 ∙ permSwapLowMid = permSwapMidHigh
permRotate2 ∙ permSwapLowHigh = permSwapLowMid
permRotate2 ∙ permSwapMidHigh = permSwapLowHigh
permSwapLowMid ∙ permIdentity = permSwapLowMid
permSwapLowMid ∙ permRotate = permSwapMidHigh
permSwapLowMid ∙ permRotate2 = permSwapLowHigh
permSwapLowMid ∙ permSwapLowMid = permIdentity
permSwapLowMid ∙ permSwapLowHigh = permRotate2
permSwapLowMid ∙ permSwapMidHigh = permRotate
permSwapLowHigh ∙ permIdentity = permSwapLowHigh
permSwapLowHigh ∙ permRotate = permSwapLowMid
permSwapLowHigh ∙ permRotate2 = permSwapMidHigh
permSwapLowHigh ∙ permSwapLowMid = permRotate
permSwapLowHigh ∙ permSwapLowHigh = permIdentity
permSwapLowHigh ∙ permSwapMidHigh = permRotate2
permSwapMidHigh ∙ permIdentity = permSwapMidHigh
permSwapMidHigh ∙ permRotate = permSwapLowHigh
permSwapMidHigh ∙ permRotate2 = permSwapLowMid
permSwapMidHigh ∙ permSwapLowMid = permRotate2
permSwapMidHigh ∙ permSwapLowHigh = permRotate
permSwapMidHigh ∙ permSwapMidHigh = permIdentity

compositionIdentityLeft :
  (permutation : TriPermutation) →
  permIdentity ∙ permutation ≡ permutation
compositionIdentityLeft permIdentity = refl
compositionIdentityLeft permRotate = refl
compositionIdentityLeft permRotate2 = refl
compositionIdentityLeft permSwapLowMid = refl
compositionIdentityLeft permSwapLowHigh = refl
compositionIdentityLeft permSwapMidHigh = refl

compositionIdentityRight :
  (permutation : TriPermutation) →
  permutation ∙ permIdentity ≡ permutation
compositionIdentityRight permIdentity = refl
compositionIdentityRight permRotate = refl
compositionIdentityRight permRotate2 = refl
compositionIdentityRight permSwapLowMid = refl
compositionIdentityRight permSwapLowHigh = refl
compositionIdentityRight permSwapMidHigh = refl

compositionInverseLeft :
  (permutation : TriPermutation) →
  inversePermutation permutation ∙ permutation ≡ permIdentity
compositionInverseLeft permIdentity = refl
compositionInverseLeft permRotate = refl
compositionInverseLeft permRotate2 = refl
compositionInverseLeft permSwapLowMid = refl
compositionInverseLeft permSwapLowHigh = refl
compositionInverseLeft permSwapMidHigh = refl

compositionInverseRight :
  (permutation : TriPermutation) →
  permutation ∙ inversePermutation permutation ≡ permIdentity
compositionInverseRight permIdentity = refl
compositionInverseRight permRotate = refl
compositionInverseRight permRotate2 = refl
compositionInverseRight permSwapLowMid = refl
compositionInverseRight permSwapLowHigh = refl
compositionInverseRight permSwapMidHigh = refl

compositionAssociative :
  (a b c : TriPermutation) →
  a ∙ (b ∙ c) ≡ (a ∙ b) ∙ c
compositionAssociative permIdentity permIdentity permIdentity = refl
compositionAssociative permIdentity permIdentity permRotate = refl
compositionAssociative permIdentity permIdentity permRotate2 = refl
compositionAssociative permIdentity permIdentity permSwapLowMid = refl
compositionAssociative permIdentity permIdentity permSwapLowHigh = refl
compositionAssociative permIdentity permIdentity permSwapMidHigh = refl
compositionAssociative permIdentity permRotate permIdentity = refl
compositionAssociative permIdentity permRotate permRotate = refl
compositionAssociative permIdentity permRotate permRotate2 = refl
compositionAssociative permIdentity permRotate permSwapLowMid = refl
compositionAssociative permIdentity permRotate permSwapLowHigh = refl
compositionAssociative permIdentity permRotate permSwapMidHigh = refl
compositionAssociative permIdentity permRotate2 permIdentity = refl
compositionAssociative permIdentity permRotate2 permRotate = refl
compositionAssociative permIdentity permRotate2 permRotate2 = refl
compositionAssociative permIdentity permRotate2 permSwapLowMid = refl
compositionAssociative permIdentity permRotate2 permSwapLowHigh = refl
compositionAssociative permIdentity permRotate2 permSwapMidHigh = refl
compositionAssociative permIdentity permSwapLowMid permIdentity = refl
compositionAssociative permIdentity permSwapLowMid permRotate = refl
compositionAssociative permIdentity permSwapLowMid permRotate2 = refl
compositionAssociative permIdentity permSwapLowMid permSwapLowMid = refl
compositionAssociative permIdentity permSwapLowMid permSwapLowHigh = refl
compositionAssociative permIdentity permSwapLowMid permSwapMidHigh = refl
compositionAssociative permIdentity permSwapLowHigh permIdentity = refl
compositionAssociative permIdentity permSwapLowHigh permRotate = refl
compositionAssociative permIdentity permSwapLowHigh permRotate2 = refl
compositionAssociative permIdentity permSwapLowHigh permSwapLowMid = refl
compositionAssociative permIdentity permSwapLowHigh permSwapLowHigh = refl
compositionAssociative permIdentity permSwapLowHigh permSwapMidHigh = refl
compositionAssociative permIdentity permSwapMidHigh permIdentity = refl
compositionAssociative permIdentity permSwapMidHigh permRotate = refl
compositionAssociative permIdentity permSwapMidHigh permRotate2 = refl
compositionAssociative permIdentity permSwapMidHigh permSwapLowMid = refl
compositionAssociative permIdentity permSwapMidHigh permSwapLowHigh = refl
compositionAssociative permIdentity permSwapMidHigh permSwapMidHigh = refl
compositionAssociative permRotate permIdentity permIdentity = refl
compositionAssociative permRotate permIdentity permRotate = refl
compositionAssociative permRotate permIdentity permRotate2 = refl
compositionAssociative permRotate permIdentity permSwapLowMid = refl
compositionAssociative permRotate permIdentity permSwapLowHigh = refl
compositionAssociative permRotate permIdentity permSwapMidHigh = refl
compositionAssociative permRotate permRotate permIdentity = refl
compositionAssociative permRotate permRotate permRotate = refl
compositionAssociative permRotate permRotate permRotate2 = refl
compositionAssociative permRotate permRotate permSwapLowMid = refl
compositionAssociative permRotate permRotate permSwapLowHigh = refl
compositionAssociative permRotate permRotate permSwapMidHigh = refl
compositionAssociative permRotate permRotate2 permIdentity = refl
compositionAssociative permRotate permRotate2 permRotate = refl
compositionAssociative permRotate permRotate2 permRotate2 = refl
compositionAssociative permRotate permRotate2 permSwapLowMid = refl
compositionAssociative permRotate permRotate2 permSwapLowHigh = refl
compositionAssociative permRotate permRotate2 permSwapMidHigh = refl
compositionAssociative permRotate permSwapLowMid permIdentity = refl
compositionAssociative permRotate permSwapLowMid permRotate = refl
compositionAssociative permRotate permSwapLowMid permRotate2 = refl
compositionAssociative permRotate permSwapLowMid permSwapLowMid = refl
compositionAssociative permRotate permSwapLowMid permSwapLowHigh = refl
compositionAssociative permRotate permSwapLowMid permSwapMidHigh = refl
compositionAssociative permRotate permSwapLowHigh permIdentity = refl
compositionAssociative permRotate permSwapLowHigh permRotate = refl
compositionAssociative permRotate permSwapLowHigh permRotate2 = refl
compositionAssociative permRotate permSwapLowHigh permSwapLowMid = refl
compositionAssociative permRotate permSwapLowHigh permSwapLowHigh = refl
compositionAssociative permRotate permSwapLowHigh permSwapMidHigh = refl
compositionAssociative permRotate permSwapMidHigh permIdentity = refl
compositionAssociative permRotate permSwapMidHigh permRotate = refl
compositionAssociative permRotate permSwapMidHigh permRotate2 = refl
compositionAssociative permRotate permSwapMidHigh permSwapLowMid = refl
compositionAssociative permRotate permSwapMidHigh permSwapLowHigh = refl
compositionAssociative permRotate permSwapMidHigh permSwapMidHigh = refl
compositionAssociative permRotate2 permIdentity permIdentity = refl
compositionAssociative permRotate2 permIdentity permRotate = refl
compositionAssociative permRotate2 permIdentity permRotate2 = refl
compositionAssociative permRotate2 permIdentity permSwapLowMid = refl
compositionAssociative permRotate2 permIdentity permSwapLowHigh = refl
compositionAssociative permRotate2 permIdentity permSwapMidHigh = refl
compositionAssociative permRotate2 permRotate permIdentity = refl
compositionAssociative permRotate2 permRotate permRotate = refl
compositionAssociative permRotate2 permRotate permRotate2 = refl
compositionAssociative permRotate2 permRotate permSwapLowMid = refl
compositionAssociative permRotate2 permRotate permSwapLowHigh = refl
compositionAssociative permRotate2 permRotate permSwapMidHigh = refl
compositionAssociative permRotate2 permRotate2 permIdentity = refl
compositionAssociative permRotate2 permRotate2 permRotate = refl
compositionAssociative permRotate2 permRotate2 permRotate2 = refl
compositionAssociative permRotate2 permRotate2 permSwapLowMid = refl
compositionAssociative permRotate2 permRotate2 permSwapLowHigh = refl
compositionAssociative permRotate2 permRotate2 permSwapMidHigh = refl
compositionAssociative permRotate2 permSwapLowMid permIdentity = refl
compositionAssociative permRotate2 permSwapLowMid permRotate = refl
compositionAssociative permRotate2 permSwapLowMid permRotate2 = refl
compositionAssociative permRotate2 permSwapLowMid permSwapLowMid = refl
compositionAssociative permRotate2 permSwapLowMid permSwapLowHigh = refl
compositionAssociative permRotate2 permSwapLowMid permSwapMidHigh = refl
compositionAssociative permRotate2 permSwapLowHigh permIdentity = refl
compositionAssociative permRotate2 permSwapLowHigh permRotate = refl
compositionAssociative permRotate2 permSwapLowHigh permRotate2 = refl
compositionAssociative permRotate2 permSwapLowHigh permSwapLowMid = refl
compositionAssociative permRotate2 permSwapLowHigh permSwapLowHigh = refl
compositionAssociative permRotate2 permSwapLowHigh permSwapMidHigh = refl
compositionAssociative permRotate2 permSwapMidHigh permIdentity = refl
compositionAssociative permRotate2 permSwapMidHigh permRotate = refl
compositionAssociative permRotate2 permSwapMidHigh permRotate2 = refl
compositionAssociative permRotate2 permSwapMidHigh permSwapLowMid = refl
compositionAssociative permRotate2 permSwapMidHigh permSwapLowHigh = refl
compositionAssociative permRotate2 permSwapMidHigh permSwapMidHigh = refl
compositionAssociative permSwapLowMid permIdentity permIdentity = refl
compositionAssociative permSwapLowMid permIdentity permRotate = refl
compositionAssociative permSwapLowMid permIdentity permRotate2 = refl
compositionAssociative permSwapLowMid permIdentity permSwapLowMid = refl
compositionAssociative permSwapLowMid permIdentity permSwapLowHigh = refl
compositionAssociative permSwapLowMid permIdentity permSwapMidHigh = refl
compositionAssociative permSwapLowMid permRotate permIdentity = refl
compositionAssociative permSwapLowMid permRotate permRotate = refl
compositionAssociative permSwapLowMid permRotate permRotate2 = refl
compositionAssociative permSwapLowMid permRotate permSwapLowMid = refl
compositionAssociative permSwapLowMid permRotate permSwapLowHigh = refl
compositionAssociative permSwapLowMid permRotate permSwapMidHigh = refl
compositionAssociative permSwapLowMid permRotate2 permIdentity = refl
compositionAssociative permSwapLowMid permRotate2 permRotate = refl
compositionAssociative permSwapLowMid permRotate2 permRotate2 = refl
compositionAssociative permSwapLowMid permRotate2 permSwapLowMid = refl
compositionAssociative permSwapLowMid permRotate2 permSwapLowHigh = refl
compositionAssociative permSwapLowMid permRotate2 permSwapMidHigh = refl
compositionAssociative permSwapLowMid permSwapLowMid permIdentity = refl
compositionAssociative permSwapLowMid permSwapLowMid permRotate = refl
compositionAssociative permSwapLowMid permSwapLowMid permRotate2 = refl
compositionAssociative permSwapLowMid permSwapLowMid permSwapLowMid = refl
compositionAssociative permSwapLowMid permSwapLowMid permSwapLowHigh = refl
compositionAssociative permSwapLowMid permSwapLowMid permSwapMidHigh = refl
compositionAssociative permSwapLowMid permSwapLowHigh permIdentity = refl
compositionAssociative permSwapLowMid permSwapLowHigh permRotate = refl
compositionAssociative permSwapLowMid permSwapLowHigh permRotate2 = refl
compositionAssociative permSwapLowMid permSwapLowHigh permSwapLowMid = refl
compositionAssociative permSwapLowMid permSwapLowHigh permSwapLowHigh = refl
compositionAssociative permSwapLowMid permSwapLowHigh permSwapMidHigh = refl
compositionAssociative permSwapLowMid permSwapMidHigh permIdentity = refl
compositionAssociative permSwapLowMid permSwapMidHigh permRotate = refl
compositionAssociative permSwapLowMid permSwapMidHigh permRotate2 = refl
compositionAssociative permSwapLowMid permSwapMidHigh permSwapLowMid = refl
compositionAssociative permSwapLowMid permSwapMidHigh permSwapLowHigh = refl
compositionAssociative permSwapLowMid permSwapMidHigh permSwapMidHigh = refl
compositionAssociative permSwapLowHigh permIdentity permIdentity = refl
compositionAssociative permSwapLowHigh permIdentity permRotate = refl
compositionAssociative permSwapLowHigh permIdentity permRotate2 = refl
compositionAssociative permSwapLowHigh permIdentity permSwapLowMid = refl
compositionAssociative permSwapLowHigh permIdentity permSwapLowHigh = refl
compositionAssociative permSwapLowHigh permIdentity permSwapMidHigh = refl
compositionAssociative permSwapLowHigh permRotate permIdentity = refl
compositionAssociative permSwapLowHigh permRotate permRotate = refl
compositionAssociative permSwapLowHigh permRotate permRotate2 = refl
compositionAssociative permSwapLowHigh permRotate permSwapLowMid = refl
compositionAssociative permSwapLowHigh permRotate permSwapLowHigh = refl
compositionAssociative permSwapLowHigh permRotate permSwapMidHigh = refl
compositionAssociative permSwapLowHigh permRotate2 permIdentity = refl
compositionAssociative permSwapLowHigh permRotate2 permRotate = refl
compositionAssociative permSwapLowHigh permRotate2 permRotate2 = refl
compositionAssociative permSwapLowHigh permRotate2 permSwapLowMid = refl
compositionAssociative permSwapLowHigh permRotate2 permSwapLowHigh = refl
compositionAssociative permSwapLowHigh permRotate2 permSwapMidHigh = refl
compositionAssociative permSwapLowHigh permSwapLowMid permIdentity = refl
compositionAssociative permSwapLowHigh permSwapLowMid permRotate = refl
compositionAssociative permSwapLowHigh permSwapLowMid permRotate2 = refl
compositionAssociative permSwapLowHigh permSwapLowMid permSwapLowMid = refl
compositionAssociative permSwapLowHigh permSwapLowMid permSwapLowHigh = refl
compositionAssociative permSwapLowHigh permSwapLowMid permSwapMidHigh = refl
compositionAssociative permSwapLowHigh permSwapLowHigh permIdentity = refl
compositionAssociative permSwapLowHigh permSwapLowHigh permRotate = refl
compositionAssociative permSwapLowHigh permSwapLowHigh permRotate2 = refl
compositionAssociative permSwapLowHigh permSwapLowHigh permSwapLowMid = refl
compositionAssociative permSwapLowHigh permSwapLowHigh permSwapLowHigh = refl
compositionAssociative permSwapLowHigh permSwapLowHigh permSwapMidHigh = refl
compositionAssociative permSwapLowHigh permSwapMidHigh permIdentity = refl
compositionAssociative permSwapLowHigh permSwapMidHigh permRotate = refl
compositionAssociative permSwapLowHigh permSwapMidHigh permRotate2 = refl
compositionAssociative permSwapLowHigh permSwapMidHigh permSwapLowMid = refl
compositionAssociative permSwapLowHigh permSwapMidHigh permSwapLowHigh = refl
compositionAssociative permSwapLowHigh permSwapMidHigh permSwapMidHigh = refl
compositionAssociative permSwapMidHigh permIdentity permIdentity = refl
compositionAssociative permSwapMidHigh permIdentity permRotate = refl
compositionAssociative permSwapMidHigh permIdentity permRotate2 = refl
compositionAssociative permSwapMidHigh permIdentity permSwapLowMid = refl
compositionAssociative permSwapMidHigh permIdentity permSwapLowHigh = refl
compositionAssociative permSwapMidHigh permIdentity permSwapMidHigh = refl
compositionAssociative permSwapMidHigh permRotate permIdentity = refl
compositionAssociative permSwapMidHigh permRotate permRotate = refl
compositionAssociative permSwapMidHigh permRotate permRotate2 = refl
compositionAssociative permSwapMidHigh permRotate permSwapLowMid = refl
compositionAssociative permSwapMidHigh permRotate permSwapLowHigh = refl
compositionAssociative permSwapMidHigh permRotate permSwapMidHigh = refl
compositionAssociative permSwapMidHigh permRotate2 permIdentity = refl
compositionAssociative permSwapMidHigh permRotate2 permRotate = refl
compositionAssociative permSwapMidHigh permRotate2 permRotate2 = refl
compositionAssociative permSwapMidHigh permRotate2 permSwapLowMid = refl
compositionAssociative permSwapMidHigh permRotate2 permSwapLowHigh = refl
compositionAssociative permSwapMidHigh permRotate2 permSwapMidHigh = refl
compositionAssociative permSwapMidHigh permSwapLowMid permIdentity = refl
compositionAssociative permSwapMidHigh permSwapLowMid permRotate = refl
compositionAssociative permSwapMidHigh permSwapLowMid permRotate2 = refl
compositionAssociative permSwapMidHigh permSwapLowMid permSwapLowMid = refl
compositionAssociative permSwapMidHigh permSwapLowMid permSwapLowHigh = refl
compositionAssociative permSwapMidHigh permSwapLowMid permSwapMidHigh = refl
compositionAssociative permSwapMidHigh permSwapLowHigh permIdentity = refl
compositionAssociative permSwapMidHigh permSwapLowHigh permRotate = refl
compositionAssociative permSwapMidHigh permSwapLowHigh permRotate2 = refl
compositionAssociative permSwapMidHigh permSwapLowHigh permSwapLowMid = refl
compositionAssociative permSwapMidHigh permSwapLowHigh permSwapLowHigh = refl
compositionAssociative permSwapMidHigh permSwapLowHigh permSwapMidHigh = refl
compositionAssociative permSwapMidHigh permSwapMidHigh permIdentity = refl
compositionAssociative permSwapMidHigh permSwapMidHigh permRotate = refl
compositionAssociative permSwapMidHigh permSwapMidHigh permRotate2 = refl
compositionAssociative permSwapMidHigh permSwapMidHigh permSwapLowMid = refl
compositionAssociative permSwapMidHigh permSwapMidHigh permSwapLowHigh = refl
compositionAssociative permSwapMidHigh permSwapMidHigh permSwapMidHigh = refl

applyComposition :
  (a b : TriPermutation) →
  (value : Base.TriTruth) →
  applyPermutation (a ∙ b) value
  ≡ applyPermutation a (applyPermutation b value)
applyComposition permIdentity permIdentity Base.tri-low = refl
applyComposition permIdentity permIdentity Base.tri-mid = refl
applyComposition permIdentity permIdentity Base.tri-high = refl
applyComposition permIdentity permRotate Base.tri-low = refl
applyComposition permIdentity permRotate Base.tri-mid = refl
applyComposition permIdentity permRotate Base.tri-high = refl
applyComposition permIdentity permRotate2 Base.tri-low = refl
applyComposition permIdentity permRotate2 Base.tri-mid = refl
applyComposition permIdentity permRotate2 Base.tri-high = refl
applyComposition permIdentity permSwapLowMid Base.tri-low = refl
applyComposition permIdentity permSwapLowMid Base.tri-mid = refl
applyComposition permIdentity permSwapLowMid Base.tri-high = refl
applyComposition permIdentity permSwapLowHigh Base.tri-low = refl
applyComposition permIdentity permSwapLowHigh Base.tri-mid = refl
applyComposition permIdentity permSwapLowHigh Base.tri-high = refl
applyComposition permIdentity permSwapMidHigh Base.tri-low = refl
applyComposition permIdentity permSwapMidHigh Base.tri-mid = refl
applyComposition permIdentity permSwapMidHigh Base.tri-high = refl
applyComposition permRotate permIdentity Base.tri-low = refl
applyComposition permRotate permIdentity Base.tri-mid = refl
applyComposition permRotate permIdentity Base.tri-high = refl
applyComposition permRotate permRotate Base.tri-low = refl
applyComposition permRotate permRotate Base.tri-mid = refl
applyComposition permRotate permRotate Base.tri-high = refl
applyComposition permRotate permRotate2 Base.tri-low = refl
applyComposition permRotate permRotate2 Base.tri-mid = refl
applyComposition permRotate permRotate2 Base.tri-high = refl
applyComposition permRotate permSwapLowMid Base.tri-low = refl
applyComposition permRotate permSwapLowMid Base.tri-mid = refl
applyComposition permRotate permSwapLowMid Base.tri-high = refl
applyComposition permRotate permSwapLowHigh Base.tri-low = refl
applyComposition permRotate permSwapLowHigh Base.tri-mid = refl
applyComposition permRotate permSwapLowHigh Base.tri-high = refl
applyComposition permRotate permSwapMidHigh Base.tri-low = refl
applyComposition permRotate permSwapMidHigh Base.tri-mid = refl
applyComposition permRotate permSwapMidHigh Base.tri-high = refl
applyComposition permRotate2 permIdentity Base.tri-low = refl
applyComposition permRotate2 permIdentity Base.tri-mid = refl
applyComposition permRotate2 permIdentity Base.tri-high = refl
applyComposition permRotate2 permRotate Base.tri-low = refl
applyComposition permRotate2 permRotate Base.tri-mid = refl
applyComposition permRotate2 permRotate Base.tri-high = refl
applyComposition permRotate2 permRotate2 Base.tri-low = refl
applyComposition permRotate2 permRotate2 Base.tri-mid = refl
applyComposition permRotate2 permRotate2 Base.tri-high = refl
applyComposition permRotate2 permSwapLowMid Base.tri-low = refl
applyComposition permRotate2 permSwapLowMid Base.tri-mid = refl
applyComposition permRotate2 permSwapLowMid Base.tri-high = refl
applyComposition permRotate2 permSwapLowHigh Base.tri-low = refl
applyComposition permRotate2 permSwapLowHigh Base.tri-mid = refl
applyComposition permRotate2 permSwapLowHigh Base.tri-high = refl
applyComposition permRotate2 permSwapMidHigh Base.tri-low = refl
applyComposition permRotate2 permSwapMidHigh Base.tri-mid = refl
applyComposition permRotate2 permSwapMidHigh Base.tri-high = refl
applyComposition permSwapLowMid permIdentity Base.tri-low = refl
applyComposition permSwapLowMid permIdentity Base.tri-mid = refl
applyComposition permSwapLowMid permIdentity Base.tri-high = refl
applyComposition permSwapLowMid permRotate Base.tri-low = refl
applyComposition permSwapLowMid permRotate Base.tri-mid = refl
applyComposition permSwapLowMid permRotate Base.tri-high = refl
applyComposition permSwapLowMid permRotate2 Base.tri-low = refl
applyComposition permSwapLowMid permRotate2 Base.tri-mid = refl
applyComposition permSwapLowMid permRotate2 Base.tri-high = refl
applyComposition permSwapLowMid permSwapLowMid Base.tri-low = refl
applyComposition permSwapLowMid permSwapLowMid Base.tri-mid = refl
applyComposition permSwapLowMid permSwapLowMid Base.tri-high = refl
applyComposition permSwapLowMid permSwapLowHigh Base.tri-low = refl
applyComposition permSwapLowMid permSwapLowHigh Base.tri-mid = refl
applyComposition permSwapLowMid permSwapLowHigh Base.tri-high = refl
applyComposition permSwapLowMid permSwapMidHigh Base.tri-low = refl
applyComposition permSwapLowMid permSwapMidHigh Base.tri-mid = refl
applyComposition permSwapLowMid permSwapMidHigh Base.tri-high = refl
applyComposition permSwapLowHigh permIdentity Base.tri-low = refl
applyComposition permSwapLowHigh permIdentity Base.tri-mid = refl
applyComposition permSwapLowHigh permIdentity Base.tri-high = refl
applyComposition permSwapLowHigh permRotate Base.tri-low = refl
applyComposition permSwapLowHigh permRotate Base.tri-mid = refl
applyComposition permSwapLowHigh permRotate Base.tri-high = refl
applyComposition permSwapLowHigh permRotate2 Base.tri-low = refl
applyComposition permSwapLowHigh permRotate2 Base.tri-mid = refl
applyComposition permSwapLowHigh permRotate2 Base.tri-high = refl
applyComposition permSwapLowHigh permSwapLowMid Base.tri-low = refl
applyComposition permSwapLowHigh permSwapLowMid Base.tri-mid = refl
applyComposition permSwapLowHigh permSwapLowMid Base.tri-high = refl
applyComposition permSwapLowHigh permSwapLowHigh Base.tri-low = refl
applyComposition permSwapLowHigh permSwapLowHigh Base.tri-mid = refl
applyComposition permSwapLowHigh permSwapLowHigh Base.tri-high = refl
applyComposition permSwapLowHigh permSwapMidHigh Base.tri-low = refl
applyComposition permSwapLowHigh permSwapMidHigh Base.tri-mid = refl
applyComposition permSwapLowHigh permSwapMidHigh Base.tri-high = refl
applyComposition permSwapMidHigh permIdentity Base.tri-low = refl
applyComposition permSwapMidHigh permIdentity Base.tri-mid = refl
applyComposition permSwapMidHigh permIdentity Base.tri-high = refl
applyComposition permSwapMidHigh permRotate Base.tri-low = refl
applyComposition permSwapMidHigh permRotate Base.tri-mid = refl
applyComposition permSwapMidHigh permRotate Base.tri-high = refl
applyComposition permSwapMidHigh permRotate2 Base.tri-low = refl
applyComposition permSwapMidHigh permRotate2 Base.tri-mid = refl
applyComposition permSwapMidHigh permRotate2 Base.tri-high = refl
applyComposition permSwapMidHigh permSwapLowMid Base.tri-low = refl
applyComposition permSwapMidHigh permSwapLowMid Base.tri-mid = refl
applyComposition permSwapMidHigh permSwapLowMid Base.tri-high = refl
applyComposition permSwapMidHigh permSwapLowHigh Base.tri-low = refl
applyComposition permSwapMidHigh permSwapLowHigh Base.tri-mid = refl
applyComposition permSwapMidHigh permSwapLowHigh Base.tri-high = refl
applyComposition permSwapMidHigh permSwapMidHigh Base.tri-low = refl
applyComposition permSwapMidHigh permSwapMidHigh Base.tri-mid = refl
applyComposition permSwapMidHigh permSwapMidHigh Base.tri-high = refl

nonCommutativeWitness :
  permRotate ∙ permSwapLowMid
  ≡ permSwapLowMid ∙ permRotate → ⊥
nonCommutativeWitness ()

record TernaryS3GroupSurface : Set where
  field
    identity : TriPermutation
    multiply : TriPermutation → TriPermutation → TriPermutation
    inverse : TriPermutation → TriPermutation
    identityLeft : (x : TriPermutation) → multiply identity x ≡ x
    identityRight : (x : TriPermutation) → multiply x identity ≡ x
    inverseLeft : (x : TriPermutation) → multiply (inverse x) x ≡ identity
    inverseRight : (x : TriPermutation) → multiply x (inverse x) ≡ identity
    associative :
      (a b c : TriPermutation) →
      multiply a (multiply b c) ≡ multiply (multiply a b) c
    actsOnTriTruth :
      (a b : TriPermutation) →
      (value : Base.TriTruth) →
      applyPermutation (multiply a b) value
      ≡ applyPermutation a (applyPermutation b value)
    nonAbelian : Bool

canonicalTernaryS3GroupSurface : TernaryS3GroupSurface
canonicalTernaryS3GroupSurface =
  record
    { identity = permIdentity
    ; multiply = _∙_
    ; inverse = inversePermutation
    ; identityLeft = compositionIdentityLeft
    ; identityRight = compositionIdentityRight
    ; inverseLeft = compositionInverseLeft
    ; inverseRight = compositionInverseRight
    ; associative = compositionAssociative
    ; actsOnTriTruth = applyComposition
    ; nonAbelian = true
    }

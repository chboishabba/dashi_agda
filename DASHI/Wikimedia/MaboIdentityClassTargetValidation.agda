module DASHI.Wikimedia.MaboIdentityClassTargetValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Wikimedia.MaboIdentityClassTargetExact

identityClassTargetPinned : targetIdentityClasses ≡ 100
identityClassTargetPinned = refl

representationStringsAreNotTarget :
  representationStringsAreTarget canonicalIdentityClassTargetBoundary ≡ false
representationStringsAreNotTarget = refl

reviewedIdentityClassesAreTarget :
  reviewedIdentityClassesAreTarget canonicalIdentityClassTargetBoundary ≡ true
reviewedIdentityClassesAreTarget = refl

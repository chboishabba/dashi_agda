module DASHI.Foundations.ExceptionalE6F3GeneratorActionValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.ExceptionalE6F3GeneratorActionExact as A

boundary = A.canonicalExceptionalE6F3GeneratorActionBoundary

sixExplicitSimilitudeLifts : A.sixExplicitSimilitudeLifts boundary ≡ true
sixExplicitSimilitudeLifts = refl

multiplierMinusOnePaid : A.multiplierMinusOnePaid boundary ≡ true
multiplierMinusOnePaid = refl

wedgeCovariancePaid : A.wedgeCovariancePaid boundary ≡ true
wedgeCovariancePaid = refl

standardWeylIntertwiningPaid : A.standardWeylIntertwiningPaid boundary ≡ true
standardWeylIntertwiningPaid = refl

standardQuadraticPreserved : A.standardQuadraticPreserved boundary ≡ true
standardQuadraticPreserved = refl

groupClosureOrder51840Paid : A.groupClosureOrder51840Paid boundary ≡ false
groupClosureOrder51840Paid = refl

projectiveKernelPlusMinusIPaid : A.projectiveKernelPlusMinusIPaid boundary ≡ false
projectiveKernelPlusMinusIPaid = refl

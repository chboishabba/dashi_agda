module DASHI.ComputerScience.RSA260BidiLeanJointKernelFamilyBindingValidationExact where

import DASHI.ComputerScience.RSA260BidiLeanJointKernelFamilyBindingExact as Owner

------------------------------------------------------------------------
-- RED/GREEN regression for binding the declared action family to the generic
-- Lean joint-kernel theorem.  Runtime zero-kernel evidence is not enough: the
-- common module carrier and per-context linear-map interpretation must also be
-- paid explicitly.
------------------------------------------------------------------------

boundary : Owner.LeanJointKernelFamilyBindingBoundary
boundary = Owner.canonicalLeanJointKernelFamilyBindingBoundary

_ : Owner.leanJointKernelSourceWritten boundary ≡ true
_ = refl

_ : Owner.leanJointKernelKernelReceiptObserved boundary ≡ false
_ = refl

_ : Owner.syntheticTwoVIntersectionKernelZeroObserved boundary ≡ true
_ = refl

_ : Owner.commonGeneratorModuleBindingPaid boundary ≡ false
_ = refl

_ : Owner.everyDeclaredActionLinearMapBindingPaid boundary ≡ false
_ = refl

_ : Owner.syntheticTwoVFamilyEligibleForLeanJointInjectivity boundary ≡ false
_ = refl

_ : Owner.rankFingerprintSearchRemainsDominated boundary ≡ true
_ = refl

_ : Owner.productionCADOFamilyBindingPaid boundary ≡ false
_ = refl

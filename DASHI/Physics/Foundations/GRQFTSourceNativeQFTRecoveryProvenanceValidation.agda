{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.GRQFTSourceNativeQFTRecoveryProvenanceExact as R

sourceNativeMathNotReproved :
  R.sourceNativeYMContinuumTheoremMustBeReprovedForLegacyRecovery ≡ false
sourceNativeMathNotReproved = refl

legacyStateLosesProvenance :
  R.legacyJointMicroscopicStateRetainsSourceNativeYMProvenance ≡ false
legacyStateLosesProvenance = refl

projectionCompatibilityIsLiveSeam :
  R.remainingQFTRecoverySeamIsProjectionCompatibility ≡ true
projectionCompatibilityIsLiveSeam = refl

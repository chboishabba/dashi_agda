{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.GRQFTR457SourceNativeRecoveryBindingValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.Foundations.GRQFTR457SourceNativeRecoveryBindingExact as B

r457ProvenanceRetained :
  B.r457ContinuumAndOSProvenanceRetainedInRecoveryState ≡ true
r457ProvenanceRetained = refl

noSecondContinuumConstruction :
  B.additionalContinuumConstructionNeededForGRQFTRecoverQFT ≡ false
noSecondContinuumConstruction = refl

legacyProjectionStillLive :
  B.legacyProjectionCompatibilityStillRequired ≡ true
legacyProjectionStillLive = refl

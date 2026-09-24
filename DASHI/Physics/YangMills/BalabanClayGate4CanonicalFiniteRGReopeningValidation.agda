module DASHI.Physics.YangMills.BalabanClayGate4CanonicalFiniteRGReopeningValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalFiniteRGReopeningExact as Canonical

canonicalReopeningCompilerClosed :
  Canonical.canonicalGate4ReopeningCompilerLevel ≡ machineChecked
canonicalReopeningCompilerClosed = refl

canonicalReopeningWeldClosed :
  Canonical.canonicalGate4ReopeningSameObjectWeldLevel ≡ machineChecked
canonicalReopeningWeldClosed = refl

canonicalReopeningProbabilityClosed :
  Canonical.canonicalGate4ReopeningProbabilityCompilerLevel ≡ machineChecked
canonicalReopeningProbabilityClosed = refl

coarseFibreDisintegrationRemainsPhysical :
  Canonical.coarseLawAndFibreDisintegrationLevel ≡ conditional
coarseFibreDisintegrationRemainsPhysical = refl

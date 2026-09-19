module DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4RawSlowDensityToProbabilityExact as Raw

normalizationCompilerClosed :
  Raw.rawSlowDensityNormalizationCompilerLevel ≡ machineChecked
normalizationCompilerClosed = refl

reopeningCompilerClosed :
  Raw.rawSlowDensityToReopeningCompilerLevel ≡ machineChecked
reopeningCompilerClosed = refl

literalCMP119RawDensityRemainsPhysical :
  Raw.literalCMP119RawSlowFieldDensityLevel ≡ conditional
literalCMP119RawDensityRemainsPhysical = refl

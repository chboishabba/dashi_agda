{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstFiniteMeasureFromDensityRound525Validation where
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsSourceFirstFiniteMeasureFromDensityRound525Exact as R525
open import DASHI.Physics.YangMills.CompactLieProofLevel
compiler : R525.round525SourceFirstFiniteFamilyCompilerLevel ≡ machineChecked
compiler = refl
equalityCompiler : R525.round525DensityFiniteFamilyEqualityLevel ≡ machineChecked
equalityCompiler = refl
sourceRemainsPhysical : R525.literalRound525DensityToFiniteMeasureMapLevel ≡ conditional
sourceRemainsPhysical = refl

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedOSSystemRound524Validation where
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsRepresentedOSSystemRound524Exact as R524
open import DASHI.Physics.YangMills.CompactLieProofLevel
compiler : R524.round524RepresentedOSSystemCompilerLevel ≡ machineChecked
compiler = refl
sameSchwinger : R524.round524SourceOSLiteralSchwingerEqualityLevel ≡ machineChecked
sameSchwinger = refl
sourceRemainsPhysical : R524.literalRound524RepresentedOSAxiomInputsLevel ≡ conditional
sourceRemainsPhysical = refl

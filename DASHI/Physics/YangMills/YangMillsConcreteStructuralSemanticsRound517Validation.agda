{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Validation where
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as R517
open import DASHI.Physics.YangMills.CompactLieProofLevel
compiler : R517.round517StructuralSemanticsCompilerLevel ≡ machineChecked
compiler = refl
sourceRemainsPhysical : R517.literalRound517AllGroupCompactSimpleSourceLevel ≡ conditional
sourceRemainsPhysical = refl

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsConcreteT4SemanticsRound519Validation where
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsConcreteT4SemanticsRound519Exact as R519
open import DASHI.Physics.YangMills.CompactLieProofLevel
compiler : R519.round519ConcreteT4SemanticsCompilerLevel ≡ machineChecked
compiler = refl
endpoint : R519.round519T4EndpointInterpretationLevel ≡ machineChecked
endpoint = refl
sourceRemainsPhysical : R519.literalRound519CanonicalCSourceLevel ≡ conditional
sourceRemainsPhysical = refl

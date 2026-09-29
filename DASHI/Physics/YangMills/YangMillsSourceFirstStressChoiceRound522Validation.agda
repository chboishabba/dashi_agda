{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstStressChoiceRound522Validation where
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsSourceFirstStressChoiceRound522Exact as R522
open import DASHI.Physics.YangMills.CompactLieProofLevel
compiler : R522.round522SourceFirstStressCompilerLevel ≡ machineChecked
compiler = refl
equalityCompiler : R522.round522CompletedStressLiteralEqualityLevel ≡ machineChecked
equalityCompiler = refl
sourceRemainsPhysical : R522.literalRound522CompletedMarkedSourceLevel ≡ conditional
sourceRemainsPhysical = refl

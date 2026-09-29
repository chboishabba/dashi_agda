{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstCurvatureChoiceRound523Validation where
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsSourceFirstCurvatureChoiceRound523Exact as R523
open import DASHI.Physics.YangMills.CompactLieProofLevel
compiler : R523.round523SourceFirstCurvatureCompilerLevel ≡ machineChecked
compiler = refl
equalityCompiler : R523.round523CurvatureLiteralEqualityLevel ≡ machineChecked
equalityCompiler = refl
sourceRemainsPhysical : R523.literalRound523MarkedCurvatureFamilyLevel ≡ conditional
sourceRemainsPhysical = refl

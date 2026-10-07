{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstCurvatureChoiceRound523Test where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel using (ProofLevel; machineChecked)

import DASHI.Physics.YangMills.YangMillsSourceFirstCurvatureChoiceRound523Exact as R523

sourceFirstCurvatureCompilerRegression :
  R523.round523SourceFirstCurvatureCompilerLevel ≡ machineChecked
sourceFirstCurvatureCompilerRegression = refl

literalCurvatureEqualityRegression :
  R523.round523CurvatureLiteralEqualityLevel ≡ machineChecked
literalCurvatureEqualityRegression = refl

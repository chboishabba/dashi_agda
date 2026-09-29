{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsProjectiveRepresentedExpectationConvergenceRound536Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsProjectiveRepresentedExpectationConvergenceRound536Exact as R536
open import DASHI.Physics.YangMills.CompactLieProofLevel

projectiveConvergenceCompilerMachineChecked :
  R536.round536ProjectiveRepresentedConvergenceCompilerLevel ≡ machineChecked
projectiveConvergenceCompilerMachineChecked = refl

noAdditionalConvergenceAnalysis :
  R536.literalRound536AdditionalContinuumConvergenceAnalysisLevel ≡ machineChecked
noAdditionalConvergenceAnalysis = refl

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsRepresentedExpectationConvergenceRound509Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsRepresentedExpectationConvergenceRound509Exact as R509
open import DASHI.Physics.YangMills.CompactLieProofLevel

representedConvergenceCompilerMachineChecked :
  R509.round509RepresentedExpectationConvergenceCompilerLevel ≡ machineChecked
representedConvergenceCompilerMachineChecked = refl

finiteFamilyConvergenceNoLongerAnalyticLeaf :
  R509.literalRound509FiniteFamilyConvergenceAnalysisLevel ≡ machineChecked
finiteFamilyConvergenceNoLongerAnalyticLeaf = refl

literalContinuumInterpretationStillOpen :
  R509.literalRound509ContinuumLimitSemanticInterpretationLevel ≡ conditional
literalContinuumInterpretationStillOpen = refl

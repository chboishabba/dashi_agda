{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSelectedWilsonFiniteProjectionRound565Validation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.YangMillsSelectedWilsonFiniteProjectionRound565Exact as R565
open import DASHI.Physics.YangMills.CompactLieProofLevel

factorizationCompilerMachineChecked :
  R565.round565FiniteProjectionToCylinderCompilerLevel ≡ machineChecked
factorizationCompilerMachineChecked = refl

finiteProjectionAuthorityStandard :
  R565.round565FiniteProjectionCylinderAuthorityLevel ≡ standardImported
finiteProjectionAuthorityStandard = refl

noGeneralDensityTheorem :
  R565.round565GeneralDensityTheoremRequired ≡ false
noGeneralDensityTheorem = refl

noLpCompletion :
  R565.round565LpCompletionRequired ≡ false
noLpCompletion = refl

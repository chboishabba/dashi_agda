{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonMassGapCriticalPathRound553Validation where
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.YangMills.YangMillsWilsonMassGapCriticalPathRound553Exact as R553
open import DASHI.Physics.YangMills.CompactLieProofLevel
compilerMachineChecked : R553.round553MassGapCompilerLevel ≡ machineChecked
compilerMachineChecked = refl
printedJPruned : R553.printedJRouteRequired ≡ false
printedJPruned = refl
moscoPruned : R553.finiteHamiltonianMoscoRouteRequired ≡ false
moscoPruned = refl
secondMassRatePruned : R553.independentMassRateCoordinateRequired ≡ false
secondMassRatePruned = refl

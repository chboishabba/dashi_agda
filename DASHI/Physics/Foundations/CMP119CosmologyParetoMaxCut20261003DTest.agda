{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyParetoMaxCut20261003DTest where

import DASHI.Physics.Foundations.CMP119CosmologyParetoMaxCut20261003DExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

fivePhysicalLeavesRemain : Subject.totalTerminalPhysicalResidualCount ≡ 5
fivePhysicalLeavesRemain = refl

finiteDGammaEliminatedOnlyFromTerminalCoordinate :
  Subject.finiteDGammaStillTerminalSignCoordinate ≡ false
finiteDGammaEliminatedOnlyFromTerminalCoordinate = refl

preferredPhysicalProducerCountNotCollapsed :
  Subject.preferredSignPhysicalResidualCount ≡ 2
preferredPhysicalProducerCountNotCollapsed = refl

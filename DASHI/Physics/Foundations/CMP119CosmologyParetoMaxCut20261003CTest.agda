{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyParetoMaxCut20261003CTest where

import DASHI.Physics.Foundations.CMP119CosmologyParetoMaxCut20261003CExact as Subject

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

fiveTerminalPhysicalLeaves : Subject.totalTerminalPhysicalResidualCount ≡ 5
fiveTerminalPhysicalLeaves = refl

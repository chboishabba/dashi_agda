{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyParetoMaxCut20261003ETest where

import DASHI.Physics.Foundations.CMP119CosmologyParetoMaxCut20261003EExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

fiveLeavesRemain : Subject.totalTerminalPhysicalResidualCount ≡ 5
fiveLeavesRemain = refl

selectedSemanticsOnly : Subject.e2e4RequiresGlobalPairEvaluator ≡ false
selectedSemanticsOnly = refl

e1LinearityNotEnough : Subject.e1AdditiveLinearityClosesCovariance ≡ false
e1LinearityNotEnough = refl

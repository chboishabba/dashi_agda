{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCompactHaarExactMassQuadratureTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.YangMills.BalabanCompactHaarExactMassQuadratureExact as Q

massDiscrepancyRetired : Q.exactCellMassEliminatesMassDiscrepancy ≡ true
massDiscrepancyRetired = refl

oscillationRemains : Q.onlyCellOscillationRemainsAfterExactMassChoice ≡ true
oscillationRemains = refl

massEstimateNotPrimitive : Q.independentMassDiscrepancyEstimateRequired ≡ false
massEstimateNotPrimitive = refl

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCompactHaarMassWeightedOscillationTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.YangMills.BalabanCompactHaarMassWeightedOscillationExact as W

cellCountGrowthRetired : W.cellCountDoesNotEnterMassWeightedGlobalBound ≡ true
cellCountGrowthRetired = refl

onlyUniformModulusRemains : W.massWeightedOscillationReducesGlobalErrorToOneModulus ≡ true
onlyUniformModulusRemains = refl

independentCellCountEstimateNotRequired : W.independentCellCountGrowthEstimateRequired ≡ false
independentCellCountEstimateNotRequired = refl

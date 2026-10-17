{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SelectedStateMassWeightedHaarTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedStateMassWeightedHaarExact as P3

selectedStatesNeedNoRefinementEqualityRegression :
  P3.separateSelectedStateEqualityRequired ≡ false
selectedStatesNeedNoRefinementEqualityRegression = refl

onlyUniformOscillationVanishesRegression :
  P3.onlyUniformOscillationVanishingRemains ≡ true
onlyUniformOscillationVanishesRegression = refl

massDiscrepancyAndCellCountRetiredRegression :
  P3.massDiscrepancyOrCellCountGrowthRequired ≡ false
massDiscrepancyAndCellCountRetiredRegression = refl

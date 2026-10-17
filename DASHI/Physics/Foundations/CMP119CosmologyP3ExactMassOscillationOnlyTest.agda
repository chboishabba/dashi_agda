{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3ExactMassOscillationOnlyTest where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP3ExactMassOscillationOnlyExact as P3

exactMassBudgetRegression : P3.exactMassTotalBudgetIsOscillationOnly ≡ true
exactMassBudgetRegression = refl

massDiscrepancyVanishesNeedNotBeProvedSeparatelyRegression :
  P3.independentMassDiscrepancyVanishesRequired ≡ false
massDiscrepancyVanishesNeedNotBeProvedSeparatelyRegression = refl

selectedHaarClosureConsumesOnlyOscillationVanishesRegression :
  P3.selectedHaarClosureConsumesOnlyOscillationVanishes ≡ true
selectedHaarClosureConsumesOnlyOscillationVanishesRegression = refl

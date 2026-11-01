{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3SelectedF2HilbertMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.CMP119CosmologyP3SelectedF2HilbertMaxCutExact as P3

noIndependentHilbertInequality :
  P3.abstractIndependentHilbertInequalityRequired ≡ false
noIndependentHilbertInequality = refl

cauchyClosed : P3.weightedCauchyCompilerClosed ≡ true
cauchyClosed = refl

energyRemains :
  P3.remainingSelectedF2HilbertSourceWorkIsUniformCoefficientEnergy ≡ true
energyRemains = refl

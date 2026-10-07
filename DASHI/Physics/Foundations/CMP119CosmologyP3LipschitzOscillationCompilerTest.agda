{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3LipschitzOscillationCompilerTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Foundations.CMP119CosmologyP3LipschitzOscillationCompilerExact as P3

noIndependentOscillationLimit :
  P3.independentOscillationVanishingTheoremRequired ≡ false
noIndependentOscillationLimit = refl

lipschitzBoundRemains :
  P3.remainingEquation171AnalyticWorkIsLipschitzCellBound ≡ true
lipschitzBoundRemains = refl

meshRemains :
  P3.remainingHaarPartitionWorkIsVanishingMesh ≡ true
meshRemains = refl

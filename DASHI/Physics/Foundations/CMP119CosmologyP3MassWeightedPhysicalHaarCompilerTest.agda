{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3MassWeightedPhysicalHaarCompilerTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP3MassWeightedPhysicalHaarCompilerExact as C

budgetNoLongerPrimitive : C.independentQuadratureBudgetVanishingRequired ≡ false
budgetNoLongerPrimitive = refl

oneModulusSuffices : C.uniformMassWeightedOscillationIsSufficientForHaarConvergence ≡ true
oneModulusSuffices = refl

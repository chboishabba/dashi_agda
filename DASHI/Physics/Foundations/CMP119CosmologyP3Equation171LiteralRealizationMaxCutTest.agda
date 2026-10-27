{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3Equation171LiteralRealizationMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyP3Equation171LiteralRealizationMaxCutExact as P3

literalRealizationConditional :
  P3.literalEquation171FiniteRealizationLevel ≡ conditional
literalRealizationConditional = refl

abstractCallbackInsufficient :
  P3.abstractEquation171CallbackAloneDeterminesLipschitzBound ≡ false
abstractCallbackInsufficient = refl

literalRealizationRequired :
  P3.literalEquation171FiniteCarrierDensityIntegralRealizationRequired ≡ true
literalRealizationRequired = refl

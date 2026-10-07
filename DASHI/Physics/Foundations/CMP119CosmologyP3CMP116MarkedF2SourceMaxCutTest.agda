{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP3CMP116MarkedF2SourceMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119CosmologyP3CMP116MarkedF2SourceMaxCutExact as P3

sourceAuthority :
  P3.cmp116DifferentiatedLocalizationIsImportedAuthority ≡ standardImported
sourceAuthority = refl

rateSplitAuthority :
  P3.cmp116Equation126129RateSplitIsImportedAuthority ≡ standardImported
rateSplitAuthority = refl

noFreshDecay : P3.freshDifferentiatedDecayTheoremRequired ≡ false
noFreshDecay = refl

noFreshHilbert : P3.freshHilbertInequalityRequired ≡ false
noFreshHilbert = refl

sameObjectWeldRemains :
  P3.selectedF2MarkedCoordinateAndUniformRadiusWeldRequired ≡ true
sameObjectWeldRemains = refl

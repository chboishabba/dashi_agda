{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyS1LiteralActiveRegularEASTTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Foundations.CMP119CosmologyS1LiteralActiveRegularEASTExact as S1

invariantCount : S1.unprovenInvariantCount ≡ 4
invariantCount = refl

activeScalesOnly : S1.requiresInactiveScaleExtension ≡ false
activeScalesOnly = refl

noQuantitativePackage : S1.requiresFullSection2QuantitativePackage ≡ false
noQuantitativePackage = refl

noBackgroundEquality : S1.requiresPostHocBackgroundEquality ≡ false
noBackgroundEquality = refl

noTangentChoices : S1.requiresIndependentTenTangentChoices ≡ false
noTangentChoices = refl

exactFormObjectsRemain : S1.literalRegularEObjectRequired ≡ true
exactFormObjectsRemain = refl

exactLocalizationObjectsRemain : S1.literalLocalizedActivityObjectRequired ≡ true
exactLocalizationObjectsRemain = refl

exactFiniteSumLawRemains : S1.literalLocalizedCompositeSumEqualityRequired ≡ true
exactFiniteSumLawRemains = refl

compilerClosesExistingWitness : S1.astCompilesToActiveRegularESection2FormWitness ≡ true
compilerClosesExistingWitness = refl

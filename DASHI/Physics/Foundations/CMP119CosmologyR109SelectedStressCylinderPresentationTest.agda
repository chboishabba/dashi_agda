{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109SelectedStressCylinderPresentationTest where

import DASHI.Physics.Foundations.CMP119CosmologyR109SelectedStressCylinderPresentationExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

noGlobalPairEvaluatorRequired :
  Subject.selectedPresentationRequiresGlobalPairEvaluator ≡ false
noGlobalPairEvaluatorRequired = refl

selectedSemanticsStillPhysical :
  Subject.selectedStressInsertionSemanticsStillPhysical ≡ true
selectedSemanticsStillPhysical = refl

oldFunctionalPresentationIsStronger :
  Subject.functionalPairEvaluatorIsStrictlyStrongerInterface ≡ true
oldFunctionalPresentationIsStronger = refl

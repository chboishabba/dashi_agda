{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyP1ActiveRegularEToPublishedBTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyP1ActiveRegularEToPublishedBExact as P

continuationCompilerClosed :
  P.activeRegularEFormToPublishedBContinuationCompilerClosed ≡ true
continuationCompilerClosed = refl

fullTheorem1PackageNotRequired :
  P.fullTheorem1QuantitativePackageRequiredForS1 ≡ false
fullTheorem1PackageNotRequired = refl

literalActiveRegularEFormRemains :
  P.literalActiveRegularEFormOnPublishedBStillRequired ≡ true
literalActiveRegularEFormRemains = refl

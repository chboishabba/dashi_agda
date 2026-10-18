{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1LinearityDoesNotForceB4CovarianceTest where

import DASHI.Physics.Foundations.CMP119CosmologyE1LinearityDoesNotForceB4CovarianceExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

linearityInsufficient :
  Subject.additiveFirstVariationLinearityForcesSymmetryCovariance ≡ false
linearityInsufficient = refl

sourceNaturalityStillNeeded :
  Subject.sourceNaturalityOrDirectCovarianceStillRequired ≡ true
sourceNaturalityStillNeeded = refl

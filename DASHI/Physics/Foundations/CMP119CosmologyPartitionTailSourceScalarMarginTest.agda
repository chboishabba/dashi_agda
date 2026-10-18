{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPartitionTailSourceScalarMarginTest where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyPartitionTailSourceScalarMarginExact as Subject

partitionNormalizationCancels :
  Subject.partitionNormalizationValueNotNeededForCoefficientMargin ≡ true
partitionNormalizationCancels = refl

coefficientMarginPaysPreferredB2 :
  Subject.preferredB2CanBePaidByERBPlusTailBelowNegativeVacuumCoefficient ≡ true
coefficientMarginPaysPreferredB2 = refl

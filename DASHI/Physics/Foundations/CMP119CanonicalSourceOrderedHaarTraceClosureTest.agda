{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CanonicalSourceOrderedHaarTraceClosureTest where

import DASHI.Physics.Foundations.CMP119CanonicalSourceOrderedHaarTraceClosureExact as Subject

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

canonicalSourceClosesFiniteTraceSign :
  Subject.canonicalSourceEqualityCompilesToFiniteTraceNegativity ≡ true
canonicalSourceClosesFiniteTraceSign = refl

finiteNegativityDoesNotPayTailMargin :
  Subject.finiteTraceNegativityAlonePaysR109TailMargin ≡ false
finiteNegativityDoesNotPayTailMargin = refl

quantitativeTailMarginRemains :
  Subject.remainingPreferredSignStrengthIsQuantitativeTailMargin ≡ true
quantitativeTailMarginRemains = refl

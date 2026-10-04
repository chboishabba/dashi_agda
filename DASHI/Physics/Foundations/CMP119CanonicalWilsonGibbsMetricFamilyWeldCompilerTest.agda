{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CanonicalWilsonGibbsMetricFamilyWeldCompilerTest where

import DASHI.Physics.Foundations.CMP119CanonicalWilsonGibbsMetricFamilyWeldCompilerExact as Subject

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true)

metricFamilyWeldIsCompilerOutput :
  Subject.metricFamilyWeldIsCompilerOutputFromCanonicalSourceAnchor ≡ true
metricFamilyWeldIsCompilerOutput = refl

onlyNormalizedSourceEqualityRemains :
  Subject.remainingSameObjectPaymentIsSelectedNormalizedSourceEquality ≡ true
onlyNormalizedSourceEqualityRemains = refl

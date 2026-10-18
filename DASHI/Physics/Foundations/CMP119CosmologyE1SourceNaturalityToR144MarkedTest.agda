{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1SourceNaturalityToR144MarkedTest where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Foundations.CMP119CosmologyE1SourceNaturalityToR144MarkedExact as Subject

sourceNaturalityCompilesToR143 :
  Subject.sourceDerivativeNaturalityCompilesToR143LocalizedCovariance ≡ true
sourceNaturalityCompilesToR143 = refl

r133TransportNotRequired :
  Subject.r133TransportEquivarianceRequiredForDirectMarkedA1 ≡ false
r133TransportNotRequired = refl

perComponentD1NotRequired :
  Subject.independentPerComponentD1CovarianceRequired ≡ false
perComponentD1NotRequired = refl

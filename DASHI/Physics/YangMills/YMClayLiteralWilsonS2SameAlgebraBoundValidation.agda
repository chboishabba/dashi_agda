{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralWilsonS2SameAlgebraBoundValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLiteralWilsonS2SameAlgebraBoundExact as S2

multiplicationWeldIsDefinitional :
  S2.independentWilsonT5MultiplicationWeldRequired ≡ false
multiplicationWeldIsDefinitional =
  S2.independentWilsonT5MultiplicationWeldRequiredIsFalse

boundPredicateWeldIsDefinitional :
  S2.independentWilsonBoundPredicateWeldRequired ≡ false
boundPredicateWeldIsDefinitional =
  S2.independentWilsonBoundPredicateWeldRequiredIsFalse

literalLoopsStillNeedBoundedness :
  S2.literalLoopBoundednessStillPhysical ≡ true
literalLoopsStillNeedBoundedness =
  S2.literalLoopBoundednessStillPhysicalIsTrue

boundedProductsStillNeedClosure :
  S2.boundedObservableMultiplicationClosureStillPhysical ≡ true
boundedProductsStillNeedClosure =
  S2.boundedObservableMultiplicationClosureStillPhysicalIsTrue

identityStillNeedsBoundedness :
  S2.identityObservableBoundednessStillPhysical ≡ true
identityStillNeedsBoundedness =
  S2.identityObservableBoundednessStillPhysicalIsTrue

module DASHI.Analysis.MarxConstructiveRealMetricNamedLemmas where

open import Agda.Primitive using (Set₁)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.MarxConstructiveRealTopology

absZeroIf :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (A : ConstructedRealAbsoluteValueLaws R) →
  ∀ x → x ≡ zero R → abs R x ≡ zero R
absZeroIf A x refl = absZero A

absZeroIff :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (A : ConstructedRealAbsoluteValueLaws R) →
  ∀ x →
  (abs R x ≡ zero R → x ≡ zero R)
  ×
  (x ≡ zero R → abs R x ≡ zero R)
absZeroIff A x = absZeroOnly A x , absZeroIf A x

metricRefl :
  ∀ {R : ConstructedOrderedCompleteReal} →
  {A : ConstructedRealAbsoluteValueLaws R} →
  (M : ConstructedRealMetricLaws R A) →
  ∀ x → distance R x x ≡ zero R
metricRefl = distanceRefl

metricSym :
  ∀ {R : ConstructedOrderedCompleteReal} →
  {A : ConstructedRealAbsoluteValueLaws R} →
  (M : ConstructedRealMetricLaws R A) →
  ∀ x y → distance R x y ≡ distance R y x
metricSym = distanceSym

metricTriangle :
  ∀ {R : ConstructedOrderedCompleteReal} →
  {A : ConstructedRealAbsoluteValueLaws R} →
  (M : ConstructedRealMetricLaws R A) →
  ∀ x y z →
  _≤_ R
    (distance R x z)
    (_+_ R (distance R x y) (distance R y z))
metricTriangle = distanceTriangle

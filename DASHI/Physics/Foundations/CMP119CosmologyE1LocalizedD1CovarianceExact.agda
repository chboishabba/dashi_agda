{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1LocalizedD1CovarianceExact where

------------------------------------------------------------------------
-- E1 THROUGH THE EXACT R142 LOCALIZED FIRST-VARIATION SUM.
--
-- R143 identifies the actual BC2 first variation with the R142 finite sum.
-- Global derivative covariance therefore follows from:
--
--   * actual Euclidean action on configuration/tangent;
--   * Euclidean reindexing of localized components;
--   * local D1 covariance component-by-component.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_)

import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1

sumMappedCong :
  ∀ {A : Set}
    (left right : A → ℝ)
    (xs : List A) →
  (∀ x → left x ≡ right x) →
  Finite.sumℝ (Finite.mapList left xs)
  ≡
  Finite.sumℝ (Finite.mapList right xs)
sumMappedCong left right [] pointwise = refl
sumMappedCong left right (x ∷ xs) pointwise =
  cong₂ _+ℝ_
    (pointwise x)
    (sumMappedCong left right xs pointwise)

record LocalizedD1EuclideanCovariance
    (dataSet : Finite.FiniteLocalizedEffectiveAction)
    (calculus :
      D1.FirstVariationLinearity
        (Finite.Configuration dataSet)
        (Finite.Tangent dataSet))
    (EuclideanAction : Set)
    : Set₁ where
  field
    actConfiguration :
      EuclideanAction →
      Finite.Configuration dataSet →
      Finite.Configuration dataSet

    actTangent :
      EuclideanAction →
      Finite.Tangent dataSet →
      Finite.Tangent dataSet

    actComponent :
      EuclideanAction →
      Finite.Component dataSet →
      Finite.Component dataSet

    localActivityCovariant :
      ∀ action component configuration →
      Finite.localActivity dataSet
        (actComponent action component)
        (actConfiguration action configuration)
      ≡
      Finite.localActivity dataSet component configuration

    -- Pure finite permutation/reindexing statement for the action itself.
    potentialComponentReindexInvariant :
      ∀ action configuration →
      Finite.sumℝ
        (Finite.mapList
          (λ component →
            Finite.localActivity dataSet component
              (actConfiguration action configuration))
          (Finite.components dataSet))
      ≡
      Finite.sumℝ
        (Finite.mapList
          (λ component →
            Finite.localActivity dataSet
              (actComponent action component)
              (actConfiguration action configuration))
          (Finite.components dataSet))

    -- Pure finite permutation/reindexing statement for D1.
    componentReindexInvariant :
      ∀ action configuration tangent →
      Finite.sumℝ
        (Finite.mapList
          (λ component →
            D1.firstVariation calculus
              (Finite.localActivity dataSet component)
              (actConfiguration action configuration)
              (actTangent action tangent))
          (Finite.components dataSet))
      ≡
      Finite.sumℝ
        (Finite.mapList
          (λ component →
            D1.firstVariation calculus
              (Finite.localActivity dataSet
                (actComponent action component))
              (actConfiguration action configuration)
              (actTangent action tangent))
          (Finite.components dataSet))

    localD1Covariant :
      ∀ action component configuration tangent →
      D1.firstVariation calculus
        (Finite.localActivity dataSet (actComponent action component))
        (actConfiguration action configuration)
        (actTangent action tangent)
      ≡
      D1.firstVariation calculus
        (Finite.localActivity dataSet component)
        configuration tangent

open LocalizedD1EuclideanCovariance public

finiteLocalizedFirstVariationCovariant :
  ∀ {dataSet calculus EuclideanAction}
    (covariance :
      LocalizedD1EuclideanCovariance
        dataSet calculus EuclideanAction)
    action configuration tangent →
  D1.finiteLocalizedFirstVariation dataSet calculus
    (actConfiguration covariance action configuration)
    (actTangent covariance action tangent)
  ≡
  D1.finiteLocalizedFirstVariation dataSet calculus
    configuration tangent
finiteLocalizedFirstVariationCovariant
    {dataSet = dataSet} {calculus = calculus}
    covariance action configuration tangent =
  trans
    (componentReindexInvariant covariance action configuration tangent)
    (sumMappedCong
      (λ component →
        D1.firstVariation calculus
          (Finite.localActivity dataSet
            (actComponent covariance action component))
          (actConfiguration covariance action configuration)
          (actTangent covariance action tangent))
      (λ component →
        D1.firstVariation calculus
          (Finite.localActivity dataSet component)
          configuration tangent)
      (Finite.components dataSet)
      (λ component →
        localD1Covariant covariance
          action component configuration tangent))

globalE1NowReducesToLocalD1AndFiniteReindexing : Bool
globalE1NowReducesToLocalD1AndFiniteReindexing = true

noIndependentGlobalBC2CovarianceEstimateNeeded : Bool
noIndependentGlobalBC2CovarianceEstimateNeeded = true


localizedPotentialCovariant :
  ∀ {dataSet calculus EuclideanAction}
    (covariance :
      LocalizedD1EuclideanCovariance
        dataSet calculus EuclideanAction)
    action configuration →
  Finite.localizedPotential dataSet
    (actConfiguration covariance action configuration)
  ≡
  Finite.localizedPotential dataSet configuration
localizedPotentialCovariant
    {dataSet = dataSet}
    covariance action configuration =
  trans
    (potentialComponentReindexInvariant
      covariance action configuration)
    (sumMappedCong
      (λ component →
        Finite.localActivity dataSet
          (actComponent covariance action component)
          (actConfiguration covariance action configuration))
      (λ component →
        Finite.localActivity dataSet component configuration)
      (Finite.components dataSet)
      (λ component →
        localActivityCovariant covariance
          action component configuration))

cmp109EffectivePotentialCovariant :
  ∀ {dataSet calculus EuclideanAction}
    (covariance :
      LocalizedD1EuclideanCovariance
        dataSet calculus EuclideanAction)
    action configuration →
  Finite.cmp109EffectivePotential dataSet
    (actConfiguration covariance action configuration)
  ≡
  Finite.cmp109EffectivePotential dataSet configuration
cmp109EffectivePotentialCovariant
    {dataSet = dataSet}
    covariance action configuration =
  trans
    (Finite.cmp109PotentialIsLocalizedSum dataSet
      (actConfiguration covariance action configuration))
    (trans
      (localizedPotentialCovariant covariance action configuration)
      (sym
        (Finite.cmp109PotentialIsLocalizedSum dataSet configuration)))

globalPotentialCovarianceNoLongerPrimitive : Bool
globalPotentialCovarianceNoLongerPrimitive = true

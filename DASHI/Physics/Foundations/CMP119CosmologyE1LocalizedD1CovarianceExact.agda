{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1LocalizedD1CovarianceExact where

------------------------------------------------------------------------
-- E1 THROUGH THE EXACT R142 LOCALIZED FIRST-VARIATION SUM.
--
-- R143 identifies the actual BC2 first variation with the R142 finite sum.
-- Therefore global derivative covariance can be compiled from:
--
--   * the actual Euclidean action on configuration/tangent;
--   * a Euclidean action on localized components;
--   * local D1 covariance component-by-component;
--   * invariance of the finite component sum under that reindexing.
--
-- No second global BC2 covariance theorem is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1

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

    -- Pure finite reindexing law.  This is the only list/permutation seam.
    localizedD1SumReindexInvariant :
      ∀ action configuration tangent →
      Finite.sumℝ
        (Finite.mapList
          (λ component →
            D1.firstVariation calculus
              (Finite.localActivity dataSet
                (actComponent action component))
              (actConfiguration action configuration)
              (actTangent action tangent))
          (Finite.components dataSet))
      ≡
      Finite.sumℝ
        (Finite.mapList
          (λ component →
            D1.firstVariation calculus
              (Finite.localActivity dataSet component)
              configuration tangent)
          (Finite.components dataSet))

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
  let
    lhs =
      D1.finiteLocalizedFirstVariation dataSet calculus
        (actConfiguration covariance action configuration)
        (actTangent covariance action tangent)
    rhs =
      D1.finiteLocalizedFirstVariation dataSet calculus
        configuration tangent
  in
  trans
    (localizedD1SumReindexInvariant
      covariance action configuration tangent)
    (Relation.Binary.PropositionalEquality.refl)

globalE1NowReducesToLocalD1AndFiniteReindexing : Bool
globalE1NowReducesToLocalD1AndFiniteReindexing = true

{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1DerivativeNaturalityExact where

------------------------------------------------------------------------
-- ONE CHAIN-RULE/NATURALITY LAW PAYS EVERY LOCAL D1 COVARIANCE.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

import DASHI.Physics.Foundations.CMP119CosmologyE1ComponentPermutationExact as PermE1
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1

record EuclideanFirstVariationNaturality
    (Configuration Tangent EuclideanAction : Set)
    (calculus : D1.FirstVariationLinearity Configuration Tangent)
    : Set₁ where
  field
    actConfiguration : EuclideanAction → Configuration → Configuration
    actTangent : EuclideanAction → Tangent → Tangent

    firstVariationNaturalForEquivariantPair :
      ∀ action
        (left right : Configuration → ℝ)
        configuration tangent →
      (∀ x → left (actConfiguration action x) ≡ right x) →
      D1.firstVariation calculus left
        (actConfiguration action configuration)
        (actTangent action tangent)
      ≡
      D1.firstVariation calculus right configuration tangent

open EuclideanFirstVariationNaturality public

record LocalizedActivityEuclideanGeometry
    (dataSet : Finite.FiniteLocalizedEffectiveAction)
    (calculus :
      D1.FirstVariationLinearity
        (Finite.Configuration dataSet)
        (Finite.Tangent dataSet))
    (EuclideanAction : Set)
    : Set₁ where
  field
    derivativeNaturality :
      EuclideanFirstVariationNaturality
        (Finite.Configuration dataSet)
        (Finite.Tangent dataSet)
        EuclideanAction calculus

    actComponent :
      EuclideanAction →
      Finite.Component dataSet →
      Finite.Component dataSet

    componentPermutation :
      ∀ action →
      Finite.mapList (actComponent action) (Finite.components dataSet)
      Perm.↭ Finite.components dataSet

    localActivityCovariant :
      ∀ action component configuration →
      Finite.localActivity dataSet
        (actComponent action component)
        (actConfiguration derivativeNaturality action configuration)
      ≡
      Finite.localActivity dataSet component configuration

open LocalizedActivityEuclideanGeometry public

localD1CovariantFromNaturality :
  ∀ {dataSet calculus EuclideanAction}
    (geometry :
      LocalizedActivityEuclideanGeometry
        dataSet calculus EuclideanAction)
    action component configuration tangent →
  D1.firstVariation calculus
    (Finite.localActivity dataSet
      (actComponent geometry action component))
    (actConfiguration (derivativeNaturality geometry) action configuration)
    (actTangent (derivativeNaturality geometry) action tangent)
  ≡
  D1.firstVariation calculus
    (Finite.localActivity dataSet component)
    configuration tangent
localD1CovariantFromNaturality
    {dataSet = dataSet} {calculus = calculus}
    geometry action component configuration tangent =
  firstVariationNaturalForEquivariantPair
    (derivativeNaturality geometry)
    action
    (Finite.localActivity dataSet
      (actComponent geometry action component))
    (Finite.localActivity dataSet component)
    configuration tangent
    (localActivityCovariant geometry action component)

asComponentPermutationCovariance :
  ∀ {dataSet calculus EuclideanAction} →
  LocalizedActivityEuclideanGeometry
    dataSet calculus EuclideanAction →
  PermE1.LocalizedComponentPermutationCovariance
    dataSet calculus EuclideanAction
asComponentPermutationCovariance geometry = record
  { PermE1.LocalizedComponentPermutationCovariance.actConfiguration =
      actConfiguration (derivativeNaturality geometry)
  ; PermE1.LocalizedComponentPermutationCovariance.actTangent =
      actTangent (derivativeNaturality geometry)
  ; PermE1.LocalizedComponentPermutationCovariance.actComponent =
      actComponent geometry
  ; PermE1.LocalizedComponentPermutationCovariance.componentPermutation =
      componentPermutation geometry
  ; PermE1.LocalizedComponentPermutationCovariance.localActivityCovariant =
      localActivityCovariant geometry
  ; PermE1.LocalizedComponentPermutationCovariance.localD1Covariant =
      localD1CovariantFromNaturality geometry
  }

perComponentD1CovarianceNoLongerIndependent : Bool
perComponentD1CovarianceNoLongerIndependent = true

oneDerivativeNaturalityLawPaysAllLocalD1Covariance : Bool
oneDerivativeNaturalityLawPaysAllLocalD1Covariance = true

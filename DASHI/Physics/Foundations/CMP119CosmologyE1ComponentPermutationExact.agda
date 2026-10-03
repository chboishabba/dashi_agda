{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyE1ComponentPermutationExact where

------------------------------------------------------------------------
-- E1 FINITE REINDEXING IS PURE COMPONENT-PERMUTATION ALGEBRA.
--
-- The previous localized E1 owner correctly separated local covariance from
-- finite reindexing, but still accepted the two reindexing equalities as
-- fields.  For a literal lattice Euclidean transformation the finite CMP116
-- component family is permuted.  Once that permutation is supplied, both the
-- zeroth-order localized-potential reindexing and the marked D1 reindexing are
-- compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Data.List.Relation.Binary.Permutation.Propositional as Perm

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; +-assoc; +-comm)

import DASHI.Physics.Foundations.CMP119CosmologyE1LocalizedD1CovarianceExact as LocalE1
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionFirstVariationRound142Exact as D1

sumPermutationInvariant :
  {left right : List ℝ} →
  left Perm.↭ right →
  Finite.sumℝ left ≡ Finite.sumℝ right
sumPermutationInvariant Perm.refl = refl
sumPermutationInvariant (Perm.prep x permutation) =
  cong (λ tail → x +ℝ tail)
    (sumPermutationInvariant permutation)
sumPermutationInvariant
    (Perm.swap {ys = ys} x y permutation) =
  trans
    (cong
      (λ tail → x +ℝ (y +ℝ tail))
      (sumPermutationInvariant permutation))
    (trans
      (sym (+-assoc x y (Finite.sumℝ ys)))
      (trans
        (cong
          (λ head → head +ℝ Finite.sumℝ ys)
          (+-comm x y))
        (+-assoc y x (Finite.sumℝ ys))))
sumPermutationInvariant (Perm.trans first second) =
  trans
    (sumPermutationInvariant first)
    (sumPermutationInvariant second)

mapComposition :
  ∀ {A B C : Set}
    (f : B → C) (g : A → B) (xs : List A) →
  Finite.mapList f (Finite.mapList g xs)
  ≡ Finite.mapList (λ x → f (g x)) xs
mapComposition f g [] = refl
mapComposition f g (x ∷ xs) =
  cong (λ tail → f (g x) ∷ tail)
    (mapComposition f g xs)

record LocalizedComponentPermutationCovariance
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

    componentPermutation :
      ∀ action →
      Finite.mapList (actComponent action) (Finite.components dataSet)
      Perm.↭ Finite.components dataSet

    localActivityCovariant :
      ∀ action component configuration →
      Finite.localActivity dataSet
        (actComponent action component)
        (actConfiguration action configuration)
      ≡ Finite.localActivity dataSet component configuration

    localD1Covariant :
      ∀ action component configuration tangent →
      D1.firstVariation calculus
        (Finite.localActivity dataSet (actComponent action component))
        (actConfiguration action configuration)
        (actTangent action tangent)
      ≡ D1.firstVariation calculus
        (Finite.localActivity dataSet component)
        configuration tangent

open LocalizedComponentPermutationCovariance public

potentialReindexFromPermutation :
  ∀ {dataSet calculus EuclideanAction}
    (data :
      LocalizedComponentPermutationCovariance
        dataSet calculus EuclideanAction)
    action configuration →
  Finite.sumℝ
    (Finite.mapList
      (λ component →
        Finite.localActivity dataSet component
          (actConfiguration data action configuration))
      (Finite.components dataSet))
  ≡
  Finite.sumℝ
    (Finite.mapList
      (λ component →
        Finite.localActivity dataSet
          (actComponent data action component)
          (actConfiguration data action configuration))
      (Finite.components dataSet))
potentialReindexFromPermutation
    {dataSet = dataSet} data action configuration =
  let
    weight =
      λ component →
        Finite.localActivity dataSet component
          (actConfiguration data action configuration)
    mapped =
      Finite.mapList
        (actComponent data action)
        (Finite.components dataSet)
    permutation = componentPermutation data action
  in
  trans
    (sym (sumPermutationInvariant
      (Perm.map weight permutation)))
    (cong Finite.sumℝ
      (mapComposition weight
        (actComponent data action)
        (Finite.components dataSet)))

markedD1ReindexFromPermutation :
  ∀ {dataSet calculus EuclideanAction}
    (data :
      LocalizedComponentPermutationCovariance
        dataSet calculus EuclideanAction)
    action configuration tangent →
  Finite.sumℝ
    (Finite.mapList
      (λ component →
        D1.firstVariation calculus
          (Finite.localActivity dataSet component)
          (actConfiguration data action configuration)
          (actTangent data action tangent))
      (Finite.components dataSet))
  ≡
  Finite.sumℝ
    (Finite.mapList
      (λ component →
        D1.firstVariation calculus
          (Finite.localActivity dataSet
            (actComponent data action component))
          (actConfiguration data action configuration)
          (actTangent data action tangent))
      (Finite.components dataSet))
markedD1ReindexFromPermutation
    {dataSet = dataSet} {calculus = calculus}
    data action configuration tangent =
  let
    weight =
      λ component →
        D1.firstVariation calculus
          (Finite.localActivity dataSet component)
          (actConfiguration data action configuration)
          (actTangent data action tangent)
    permutation = componentPermutation data action
  in
  trans
    (sym (sumPermutationInvariant
      (Perm.map weight permutation)))
    (cong Finite.sumℝ
      (mapComposition weight
        (actComponent data action)
        (Finite.components dataSet)))

asLocalizedD1EuclideanCovariance :
  ∀ {dataSet calculus EuclideanAction} →
  LocalizedComponentPermutationCovariance
    dataSet calculus EuclideanAction →
  LocalE1.LocalizedD1EuclideanCovariance
    dataSet calculus EuclideanAction
asLocalizedD1EuclideanCovariance data = record
  { LocalE1.LocalizedD1EuclideanCovariance.actConfiguration =
      actConfiguration data
  ; LocalE1.LocalizedD1EuclideanCovariance.actTangent =
      actTangent data
  ; LocalE1.LocalizedD1EuclideanCovariance.actComponent =
      actComponent data
  ; LocalE1.LocalizedD1EuclideanCovariance.localActivityCovariant =
      localActivityCovariant data
  ; LocalE1.LocalizedD1EuclideanCovariance.potentialComponentReindexInvariant =
      potentialReindexFromPermutation data
  ; LocalE1.LocalizedD1EuclideanCovariance.componentReindexInvariant =
      markedD1ReindexFromPermutation data
  ; LocalE1.LocalizedD1EuclideanCovariance.localD1Covariant =
      localD1Covariant data
  }

finiteReindexingNoLongerIndependentE1Leaf : Bool
finiteReindexingNoLongerIndependentE1Leaf = true

remainingE1LocalLeavesAreTangentComponentActionsAndLocalCovariance : Bool
remainingE1LocalLeavesAreTangentComponentActionsAndLocalCovariance = true

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonBivariateMarkedJetExact where

------------------------------------------------------------------------
-- Concrete two-source rational jet for the literal Wilson marked expansion.
--
-- Only the two-source germ through order st is required by W1/W3:
--
--   a + b s + c t + d s t.
--
-- The mixed coefficient d is extracted by the exact four-point finite
-- difference on this polynomial jet.  This is NOT a claim that a general
-- analytic function is determined by four values.  The physical/source theorem
-- must identify the actual Wilson-Gibbs marked partition/log-partition germ
-- with the jet supplied here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact as Diff

record TwoSourceJet : Set where
  constructor jet
  field
    baseCoefficient : ℚ
    leftCoefficient : ℚ
    rightCoefficient : ℚ
    mixedCoefficient : ℚ

open TwoSourceJet public

evaluateJet : TwoSourceJet → ℚ → ℚ → ℚ
evaluateJet j left right =
  baseCoefficient j
  + leftCoefficient j * left
  + rightCoefficient j * right
  + mixedCoefficient j * (left * right)

mixedFiniteDifference :
  (ℚ → ℚ → ℚ) → ℚ
mixedFiniteDifference f =
  f 1ℚ 1ℚ - f 1ℚ 0ℚ - f 0ℚ 1ℚ + f 0ℚ 0ℚ

mixedFiniteDifferenceJet :
  ∀ j →
  mixedFiniteDifference (evaluateJet j)
  ≡ mixedCoefficient j
mixedFiniteDifferenceJet (jet a b c d) =
  ℚRing.solve-∀ a b c d

mixedFiniteDifferenceCongruent :
  ∀ left right →
  (∀ sourceLeft sourceRight →
    left sourceLeft sourceRight ≡ right sourceLeft sourceRight) →
  mixedFiniteDifference left ≡ mixedFiniteDifference right
mixedFiniteDifferenceCongruent left right pointwise
  rewrite pointwise 1ℚ 1ℚ
        | pointwise 1ℚ 0ℚ
        | pointwise 0ℚ 1ℚ
        | pointwise 0ℚ 0ℚ = refl

mixedFiniteDifferenceAdd :
  ∀ f g →
  mixedFiniteDifference (λ left right → f left right + g left right)
  ≡ mixedFiniteDifference f + mixedFiniteDifference g
mixedFiniteDifferenceAdd f g =
  ℚRing.solve-∀
    (f 1ℚ 1ℚ) (f 1ℚ 0ℚ) (f 0ℚ 1ℚ) (f 0ℚ 0ℚ)
    (g 1ℚ 1ℚ) (g 1ℚ 0ℚ) (g 0ℚ 1ℚ) (g 0ℚ 0ℚ)

mixedFiniteDifferenceFiniteSum :
  ∀ {Term : Set}
    (terms : List Term)
    (termValue : Term → ℚ → ℚ → ℚ) →
  mixedFiniteDifference
    (λ sourceLeft sourceRight →
      TwoMark.sumℚ
        (TwoMark.map
          (λ term → termValue term sourceLeft sourceRight)
          terms))
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ term → mixedFiniteDifference (termValue term))
      terms)
mixedFiniteDifferenceFiniteSum [] termValue =
  ℚRing.solve-∀
mixedFiniteDifferenceFiniteSum (term ∷ terms) termValue =
  trans
    (mixedFiniteDifferenceAdd
      (termValue term)
      (λ sourceLeft sourceRight →
        TwoMark.sumℚ
          (TwoMark.map
            (λ item → termValue item sourceLeft sourceRight)
            terms)))
    (cong
      (λ rest → mixedFiniteDifference (termValue term) + rest)
      (mixedFiniteDifferenceFiniteSum terms termValue))

rationalJetDerivativeCalculus :
  Diff.MixedSourceDerivativeCalculus ℚ
rationalJetDerivativeCalculus = record
  { Diff.MixedSourceDerivativeCalculus.mixedDerivative =
      mixedFiniteDifference
  ; Diff.MixedSourceDerivativeCalculus.mixedDerivativeCongruent =
      mixedFiniteDifferenceCongruent
  ; Diff.MixedSourceDerivativeCalculus.mixedDerivativeFiniteSum =
      mixedFiniteDifferenceFiniteSum
  }

mixedFiniteDifferenceLeftIndependentZero :
  ∀ term →
  (∀ left₁ left₂ right → term left₁ right ≡ term left₂ right) →
  mixedFiniteDifference term ≡ 0ℚ
mixedFiniteDifferenceLeftIndependentZero term independent
  rewrite independent 1ℚ 0ℚ 1ℚ
        | independent 1ℚ 0ℚ 0ℚ =
  ℚRing.solve-∀ (term 0ℚ 1ℚ) (term 0ℚ 0ℚ)

mixedFiniteDifferenceRightIndependentZero :
  ∀ term →
  (∀ left right₁ right₂ → term left right₁ ≡ term left right₂) →
  mixedFiniteDifference term ≡ 0ℚ
mixedFiniteDifferenceRightIndependentZero term independent
  rewrite independent 1ℚ 1ℚ 0ℚ
        | independent 0ℚ 1ℚ 0ℚ =
  ℚRing.solve-∀ (term 1ℚ 0ℚ) (term 0ℚ 0ℚ)

rationalJetDerivativeVanishing :
  Diff.MixedSourceDerivativeVanishing rationalJetDerivativeCalculus
rationalJetDerivativeVanishing = record
  { Diff.MixedSourceDerivativeVanishing.leftIndependentDerivativeZero =
      mixedFiniteDifferenceLeftIndependentZero
  ; Diff.MixedSourceDerivativeVanishing.rightIndependentDerivativeZero =
      mixedFiniteDifferenceRightIndependentZero
  }

record ClusterJetSupport {Cluster : Set}
    (clusterJet : Cluster → TwoSourceJet) : Set₁ where
  field
    touchesLeft touchesRight : Cluster → Bool

    missingLeftKillsLeftCoefficient :
      ∀ cluster →
      touchesLeft cluster ≡ false →
      leftCoefficient (clusterJet cluster) ≡ 0ℚ

    missingLeftKillsMixedCoefficient :
      ∀ cluster →
      touchesLeft cluster ≡ false →
      mixedCoefficient (clusterJet cluster) ≡ 0ℚ

    missingRightKillsRightCoefficient :
      ∀ cluster →
      touchesRight cluster ≡ false →
      rightCoefficient (clusterJet cluster) ≡ 0ℚ

    missingRightKillsMixedCoefficient :
      ∀ cluster →
      touchesRight cluster ≡ false →
      mixedCoefficient (clusterJet cluster) ≡ 0ℚ

open ClusterJetSupport public

missingLeftJetIndependent :
  ∀ {Cluster}
    {clusterJet : Cluster → TwoSourceJet}
    (support : ClusterJetSupport clusterJet)
    cluster →
  touchesLeft support cluster ≡ false →
  ∀ left₁ left₂ right →
  evaluateJet (clusterJet cluster) left₁ right
  ≡
  evaluateJet (clusterJet cluster) left₂ right
missingLeftJetIndependent support cluster leftMissing left₁ left₂ right
  rewrite missingLeftKillsLeftCoefficient support cluster leftMissing
        | missingLeftKillsMixedCoefficient support cluster leftMissing =
  ℚRing.solve-∀
    (baseCoefficient (clusterJet cluster))
    (rightCoefficient (clusterJet cluster))
    left₁ left₂ right

missingRightJetIndependent :
  ∀ {Cluster}
    {clusterJet : Cluster → TwoSourceJet}
    (support : ClusterJetSupport clusterJet)
    cluster →
  touchesRight support cluster ≡ false →
  ∀ left right₁ right₂ →
  evaluateJet (clusterJet cluster) left right₁
  ≡
  evaluateJet (clusterJet cluster) left right₂
missingRightJetIndependent support cluster rightMissing left right₁ right₂
  rewrite missingRightKillsRightCoefficient support cluster rightMissing
        | missingRightKillsMixedCoefficient support cluster rightMissing =
  ℚRing.solve-∀
    (baseCoefficient (clusterJet cluster))
    (leftCoefficient (clusterJet cluster))
    left right₁ right₂

jetSupportLocality :
  ∀ {Cluster}
    {clusterJet : Cluster → TwoSourceJet} →
  ClusterJetSupport clusterJet →
  Diff.MarkedClusterSupportLocality
    (λ cluster → evaluateJet (clusterJet cluster))
jetSupportLocality support = record
  { Diff.MarkedClusterSupportLocality.touchesLeft =
      touchesLeft support
  ; Diff.MarkedClusterSupportLocality.touchesRight =
      touchesRight support
  ; Diff.MarkedClusterSupportLocality.missingLeftMakesTermIndependent =
      missingLeftJetIndependent support
  ; Diff.MarkedClusterSupportLocality.missingRightMakesTermIndependent =
      missingRightJetIndependent support
  }

jetClusterLogPartition :
  ∀ {Cluster} →
  List Cluster →
  (Cluster → TwoSourceJet) →
  ℚ → ℚ → ℚ
jetClusterLogPartition clusters clusterJet left right =
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → evaluateJet (clusterJet cluster) left right)
      clusters)

supportIndexedJetExpansion :
  ∀ {Cluster}
    (clusters : List Cluster)
    (clusterJet : Cluster → TwoSourceJet)
    (support : ClusterJetSupport clusterJet) →
  Diff.SupportIndexedMarkedClusterExpansion
    ℚ Cluster rationalJetDerivativeCalculus
supportIndexedJetExpansion clusters clusterJet support = record
  { Diff.SupportIndexedMarkedClusterExpansion.clusters = clusters
  ; Diff.SupportIndexedMarkedClusterExpansion.logPartition =
      jetClusterLogPartition clusters clusterJet
  ; Diff.SupportIndexedMarkedClusterExpansion.clusterTerm =
      λ cluster → evaluateJet (clusterJet cluster)
  ; Diff.SupportIndexedMarkedClusterExpansion.logPartitionExpansionExact =
      λ sourceLeft sourceRight → refl
  ; Diff.SupportIndexedMarkedClusterExpansion.supportLocality =
      jetSupportLocality support
  }

mixedDerivativeOfJetClusterTerm :
  ∀ {Cluster}
    (clusterJet : Cluster → TwoSourceJet)
    cluster →
  Diff.mixedDerivative rationalJetDerivativeCalculus
    (λ left right → evaluateJet (clusterJet cluster) left right)
  ≡ mixedCoefficient (clusterJet cluster)
mixedDerivativeOfJetClusterTerm clusterJet cluster =
  mixedFiniteDifferenceJet (clusterJet cluster)

mixedDerivativeJetExpansionIsTwoSupportMixedCoefficientSum :
  ∀ {Cluster}
    (clusters : List Cluster)
    (clusterJet : Cluster → TwoSourceJet)
    (support : ClusterJetSupport clusterJet) →
  Diff.mixedDerivative rationalJetDerivativeCalculus
    (Diff.logPartition
      (supportIndexedJetExpansion clusters clusterJet support))
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → mixedCoefficient (clusterJet cluster))
      (Diff.filterTwoSupport
        (touchesLeft support)
        (touchesRight support)
        clusters))
mixedDerivativeJetExpansionIsTwoSupportMixedCoefficientSum
    clusters clusterJet support =
  trans
    (Diff.mixedDerivativeSupportIndexedExpansionIsConnectingSum
      rationalJetDerivativeVanishing
      (supportIndexedJetExpansion clusters clusterJet support))
    (sumMixedJetCoefficients
      (Diff.filterTwoSupport
        (touchesLeft support)
        (touchesRight support)
        clusters))
  where
  sumMixedJetCoefficients :
    (items : List Cluster) →
    TwoMark.sumℚ
      (TwoMark.map
        (λ cluster →
          Diff.mixedDerivative rationalJetDerivativeCalculus
            (λ left right → evaluateJet (clusterJet cluster) left right))
        items)
    ≡
    TwoMark.sumℚ
      (TwoMark.map
        (λ cluster → mixedCoefficient (clusterJet cluster))
        items)
  sumMixedJetCoefficients [] = refl
  sumMixedJetCoefficients (cluster ∷ items)
    rewrite mixedFiniteDifferenceJet (clusterJet cluster)
          | sumMixedJetCoefficients items = refl

{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact where

------------------------------------------------------------------------
-- W1 analytic/combinatorial core.
--
-- A convergent source-dependent polymer expansion gives an identity
--
--   log Z(JL,JR) = sum_Y Phi_Y(JL,JR).
--
-- W1 additionally needs the two source derivatives to pass through that finite
-- (or already truncated/justified) cluster sum.  This module proves the exact
-- algebraic consequence once a mixed-derivative calculus supplies:
--
--   * extensional congruence of D_L D_R;
--   * finite-sum interchange.
--
-- The genuinely analytic Wilson payment remains the common source
-- neighbourhood / termwise-differentiation theorem that inhabits those laws on
-- the literal marked polymer family.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; cong)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark

record MixedSourceDerivativeCalculus (Source : Set) : Set₁ where
  field
    mixedDerivative :
      (Source → Source → ℚ) → ℚ

    mixedDerivativeCongruent :
      ∀ left right →
      (∀ sourceLeft sourceRight →
        left sourceLeft sourceRight ≡ right sourceLeft sourceRight) →
      mixedDerivative left ≡ mixedDerivative right

    mixedDerivativeFiniteSum :
      ∀ {Term : Set}
        (terms : List Term)
        (termValue : Term → Source → Source → ℚ) →
      mixedDerivative
        (λ sourceLeft sourceRight →
          TwoMark.sumℚ
            (TwoMark.map
              (λ term → termValue term sourceLeft sourceRight)
              terms))
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (λ term → mixedDerivative (termValue term))
          terms)

open MixedSourceDerivativeCalculus public

record SourceDependentClusterExpansion
    (Source Cluster : Set)
    (calculus : MixedSourceDerivativeCalculus Source)
    : Set₁ where
  field
    contributingClusters : List Cluster

    logPartition :
      Source → Source → ℚ

    clusterTerm :
      Cluster → Source → Source → ℚ

    logPartitionClusterExpansionExact :
      ∀ sourceLeft sourceRight →
      logPartition sourceLeft sourceRight
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster →
            clusterTerm cluster sourceLeft sourceRight)
          contributingClusters)

open SourceDependentClusterExpansion public

mixedDerivativeIsConnectedClusterDerivativeSum :
  ∀ {Source Cluster}
    {calculus : MixedSourceDerivativeCalculus Source}
    (expansion :
      SourceDependentClusterExpansion Source Cluster calculus) →
  mixedDerivative calculus (logPartition expansion)
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster →
        mixedDerivative calculus (clusterTerm expansion cluster))
      (contributingClusters expansion))
mixedDerivativeIsConnectedClusterDerivativeSum
    {calculus = calculus} expansion =
  trans
    (mixedDerivativeCongruent calculus
      (logPartition expansion)
      (λ sourceLeft sourceRight →
        TwoMark.sumℚ
          (TwoMark.map
            (λ cluster →
              clusterTerm expansion cluster sourceLeft sourceRight)
            (contributingClusters expansion)))
      (logPartitionClusterExpansionExact expansion))
    (mixedDerivativeFiniteSum calculus
      (contributingClusters expansion)
      (clusterTerm expansion))

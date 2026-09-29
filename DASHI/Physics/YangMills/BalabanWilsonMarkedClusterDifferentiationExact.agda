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

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; cong; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Base using (_++_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
import Data.Rational.Properties as ℚP
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


------------------------------------------------------------------------
-- Disconnected-term cancellation.
--
-- A mixed source derivative vanishes on a cluster term that is independent of
-- either source. The derivative implementation supplies those ordinary laws;
-- list cancellation is compiler algebra.
------------------------------------------------------------------------

record MixedSourceDerivativeVanishing
    {Source : Set}
    (calculus : MixedSourceDerivativeCalculus Source)
    : Set₁ where
  field
    leftIndependentDerivativeZero :
      ∀ term →
      (∀ left₁ left₂ right → term left₁ right ≡ term left₂ right) →
      mixedDerivative calculus term ≡ 0ℚ

    rightIndependentDerivativeZero :
      ∀ term →
      (∀ left right₁ right₂ → term left right₁ ≡ term left right₂) →
      mixedDerivative calculus term ≡ 0ℚ

open MixedSourceDerivativeVanishing public

data DisconnectedSourceDependence
    {Source : Set}
    (term : Source → Source → ℚ) : Set where
  leftIndependent :
    (∀ left₁ left₂ right → term left₁ right ≡ term left₂ right) →
    DisconnectedSourceDependence term
  rightIndependent :
    (∀ left right₁ right₂ → term left right₁ ≡ term left right₂) →
    DisconnectedSourceDependence term

disconnectedMixedDerivativeZero :
  ∀ {Source}
    {calculus : MixedSourceDerivativeCalculus Source} →
  MixedSourceDerivativeVanishing calculus →
  (term : Source → Source → ℚ) →
  DisconnectedSourceDependence term →
  mixedDerivative calculus term ≡ 0ℚ
disconnectedMixedDerivativeZero vanishing term (leftIndependent proof) =
  leftIndependentDerivativeZero vanishing term proof
disconnectedMixedDerivativeZero vanishing term (rightIndependent proof) =
  rightIndependentDerivativeZero vanishing term proof

sumZeroTerms :
  ∀ {A : Set}
    (items : List A)
    (value : A → ℚ) →
  (∀ item → value item ≡ 0ℚ) →
  TwoMark.sumℚ (TwoMark.map value items) ≡ 0ℚ
sumZeroTerms [] value pointwise = refl
sumZeroTerms (item ∷ items) value pointwise
  rewrite pointwise item
        | sumZeroTerms items value pointwise = refl

sumAppend :
  ∀ {A : Set}
    (left right : List A)
    (value : A → ℚ) →
  TwoMark.sumℚ (TwoMark.map value (left ++ right))
  ≡
  TwoMark.sumℚ (TwoMark.map value left)
    + TwoMark.sumℚ (TwoMark.map value right)
sumAppend [] right value = refl
sumAppend (item ∷ left) right value
  rewrite sumAppend left right value = refl

sumAppendRightZero :
  ∀ {A : Set}
    (left right : List A)
    (value : A → ℚ) →
  TwoMark.sumℚ (TwoMark.map value right) ≡ 0ℚ →
  TwoMark.sumℚ (TwoMark.map value (left ++ right))
  ≡
  TwoMark.sumℚ (TwoMark.map value left)
sumAppendRightZero left right value rightZero
  rewrite sumAppend left right value
        | rightZero
        | ℚP.+-identityʳ
            (TwoMark.sumℚ (TwoMark.map value left)) = refl

record FullMarkedClusterExpansion
    (Source Cluster : Set)
    (calculus : MixedSourceDerivativeCalculus Source)
    : Set₁ where
  field
    connectingClusters disconnectedClusters : List Cluster

    logPartition : Source → Source → ℚ
    clusterTerm : Cluster → Source → Source → ℚ

    logPartitionExpansionExact :
      ∀ sourceLeft sourceRight →
      logPartition sourceLeft sourceRight
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster →
            clusterTerm cluster sourceLeft sourceRight)
          (connectingClusters ++ disconnectedClusters))

    disconnectedSourceDependence :
      ∀ cluster →
      DisconnectedSourceDependence (clusterTerm cluster)

open FullMarkedClusterExpansion public

mixedDerivativeFullExpansionIsConnectingSum :
  ∀ {Source Cluster}
    {calculus : MixedSourceDerivativeCalculus Source}
    (vanishing : MixedSourceDerivativeVanishing calculus)
    (expansion : FullMarkedClusterExpansion Source Cluster calculus) →
  mixedDerivative calculus (logPartition expansion)
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → mixedDerivative calculus (clusterTerm expansion cluster))
      (connectingClusters expansion))
mixedDerivativeFullExpansionIsConnectingSum
    {calculus = calculus} vanishing expansion =
  let
    allClusters =
      connectingClusters expansion ++ disconnectedClusters expansion

    derivativeAll :
      mixedDerivative calculus (logPartition expansion)
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster →
            mixedDerivative calculus (clusterTerm expansion cluster))
          allClusters)
    derivativeAll =
      trans
        (mixedDerivativeCongruent calculus
          (logPartition expansion)
          (λ sourceLeft sourceRight →
            TwoMark.sumℚ
              (TwoMark.map
                (λ cluster →
                  clusterTerm expansion cluster sourceLeft sourceRight)
                allClusters))
          (logPartitionExpansionExact expansion))
        (mixedDerivativeFiniteSum calculus allClusters (clusterTerm expansion))

    disconnectedZero :
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster →
            mixedDerivative calculus (clusterTerm expansion cluster))
          (disconnectedClusters expansion))
      ≡ 0ℚ
    disconnectedZero =
      sumZeroTerms
        (disconnectedClusters expansion)
        (λ cluster →
          mixedDerivative calculus (clusterTerm expansion cluster))
        (λ cluster →
          disconnectedMixedDerivativeZero
            vanishing
            (clusterTerm expansion cluster)
            (disconnectedSourceDependence expansion cluster))
  in
  trans derivativeAll
    (sumAppendRightZero
      (connectingClusters expansion)
      (disconnectedClusters expansion)
      (λ cluster →
        mixedDerivative calculus (clusterTerm expansion cluster))
      disconnectedZero)


------------------------------------------------------------------------
-- Support-filtered connected family.
--
-- The physical source no longer has to pre-partition clusters into
-- "connecting" and "disconnected" lists.  It supplies literal support
-- incidence for each finite cluster and the ordinary locality fact that missing
-- one Wilson support makes that cluster term independent of that source.
-- The compiler filters the two-support family and cancels every other mixed
-- derivative.
------------------------------------------------------------------------

filterTwoSupport :
  ∀ {Cluster : Set} →
  (Cluster → Bool) →
  (Cluster → Bool) →
  List Cluster →
  List Cluster
filterTwoSupport touchesLeft touchesRight [] = []
filterTwoSupport touchesLeft touchesRight (cluster ∷ clusters)
  with touchesLeft cluster | touchesRight cluster
... | true | true =
  cluster ∷ filterTwoSupport touchesLeft touchesRight clusters
... | true | false =
  filterTwoSupport touchesLeft touchesRight clusters
... | false | true =
  filterTwoSupport touchesLeft touchesRight clusters
... | false | false =
  filterTwoSupport touchesLeft touchesRight clusters

record MarkedClusterSupportLocality
    {Source Cluster : Set}
    (clusterTerm : Cluster → Source → Source → ℚ) : Set₁ where
  field
    touchesLeft touchesRight : Cluster → Bool

    missingLeftMakesTermIndependent :
      ∀ cluster →
      touchesLeft cluster ≡ false →
      ∀ left₁ left₂ right →
      clusterTerm cluster left₁ right ≡
      clusterTerm cluster left₂ right

    missingRightMakesTermIndependent :
      ∀ cluster →
      touchesRight cluster ≡ false →
      ∀ left right₁ right₂ →
      clusterTerm cluster left right₁ ≡
      clusterTerm cluster left right₂

open MarkedClusterSupportLocality public

mixedDerivativeZeroWhenNotTwoSupport :
  ∀ {Source Cluster}
    {calculus : MixedSourceDerivativeCalculus Source}
    (vanishing : MixedSourceDerivativeVanishing calculus)
    {clusterTerm : Cluster → Source → Source → ℚ}
    (locality : MarkedClusterSupportLocality clusterTerm)
    cluster →
  touchesLeft locality cluster ≡ false →
  mixedDerivative calculus (clusterTerm cluster) ≡ 0ℚ
mixedDerivativeZeroWhenNotTwoSupport
    vanishing locality cluster leftMiss =
  leftIndependentDerivativeZero vanishing
    (clusterTerm cluster)
    (missingLeftMakesTermIndependent locality cluster leftMiss)

mixedDerivativeZeroWhenMissingRight :
  ∀ {Source Cluster}
    {calculus : MixedSourceDerivativeCalculus Source}
    (vanishing : MixedSourceDerivativeVanishing calculus)
    {clusterTerm : Cluster → Source → Source → ℚ}
    (locality : MarkedClusterSupportLocality clusterTerm)
    cluster →
  touchesRight locality cluster ≡ false →
  mixedDerivative calculus (clusterTerm cluster) ≡ 0ℚ
mixedDerivativeZeroWhenMissingRight
    vanishing locality cluster rightMiss =
  rightIndependentDerivativeZero vanishing
    (clusterTerm cluster)
    (missingRightMakesTermIndependent locality cluster rightMiss)

sumMixedDerivativeFiltersToTwoSupport :
  ∀ {Source Cluster}
    {calculus : MixedSourceDerivativeCalculus Source}
    (vanishing : MixedSourceDerivativeVanishing calculus)
    (clusters : List Cluster)
    (clusterTerm : Cluster → Source → Source → ℚ)
    (locality : MarkedClusterSupportLocality clusterTerm) →
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → mixedDerivative calculus (clusterTerm cluster))
      clusters)
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → mixedDerivative calculus (clusterTerm cluster))
      (filterTwoSupport
        (touchesLeft locality)
        (touchesRight locality)
        clusters))
sumMixedDerivativeFiltersToTwoSupport vanishing [] clusterTerm locality = refl
sumMixedDerivativeFiltersToTwoSupport
    {calculus = calculus}
    vanishing (cluster ∷ clusters) clusterTerm locality
  with touchesLeft locality cluster | touchesRight locality cluster
... | true | true
  rewrite
    sumMixedDerivativeFiltersToTwoSupport
      vanishing clusters clusterTerm locality = refl
... | true | false
  rewrite
    mixedDerivativeZeroWhenMissingRight
      vanishing locality cluster refl
  | ℚP.+-identityˡ
      (TwoMark.sumℚ
        (TwoMark.map
          (λ item → mixedDerivative calculus (clusterTerm item))
          clusters))
  | sumMixedDerivativeFiltersToTwoSupport
      vanishing clusters clusterTerm locality = refl
... | false | true
  rewrite
    mixedDerivativeZeroWhenNotTwoSupport
      vanishing locality cluster refl
  | ℚP.+-identityˡ
      (TwoMark.sumℚ
        (TwoMark.map
          (λ item → mixedDerivative calculus (clusterTerm item))
          clusters))
  | sumMixedDerivativeFiltersToTwoSupport
      vanishing clusters clusterTerm locality = refl
... | false | false
  rewrite
    mixedDerivativeZeroWhenNotTwoSupport
      vanishing locality cluster refl
  | ℚP.+-identityˡ
      (TwoMark.sumℚ
        (TwoMark.map
          (λ item → mixedDerivative calculus (clusterTerm item))
          clusters))
  | sumMixedDerivativeFiltersToTwoSupport
      vanishing clusters clusterTerm locality = refl

record SupportIndexedMarkedClusterExpansion
    (Source Cluster : Set)
    (calculus : MixedSourceDerivativeCalculus Source)
    : Set₁ where
  field
    clusters : List Cluster
    logPartition : Source → Source → ℚ
    clusterTerm : Cluster → Source → Source → ℚ

    logPartitionExpansionExact :
      ∀ sourceLeft sourceRight →
      logPartition sourceLeft sourceRight
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (λ cluster →
            clusterTerm cluster sourceLeft sourceRight)
          clusters)

    supportLocality :
      MarkedClusterSupportLocality clusterTerm

open SupportIndexedMarkedClusterExpansion public

mixedDerivativeSupportIndexedExpansionIsConnectingSum :
  ∀ {Source Cluster}
    {calculus : MixedSourceDerivativeCalculus Source}
    (vanishing : MixedSourceDerivativeVanishing calculus)
    (expansion :
      SupportIndexedMarkedClusterExpansion Source Cluster calculus) →
  mixedDerivative calculus (logPartition expansion)
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster →
        mixedDerivative calculus (clusterTerm expansion cluster))
      (filterTwoSupport
        (touchesLeft (supportLocality expansion))
        (touchesRight (supportLocality expansion))
        (clusters expansion)))
mixedDerivativeSupportIndexedExpansionIsConnectingSum
    {calculus = calculus} vanishing expansion =
  trans
    (trans
      (mixedDerivativeCongruent calculus
        (logPartition expansion)
        (λ sourceLeft sourceRight →
          TwoMark.sumℚ
            (TwoMark.map
              (λ cluster →
                clusterTerm expansion cluster sourceLeft sourceRight)
              (clusters expansion)))
        (logPartitionExpansionExact expansion))
      (mixedDerivativeFiniteSum calculus
        (clusters expansion)
        (clusterTerm expansion)))
    (sumMixedDerivativeFiltersToTwoSupport
      vanishing
      (clusters expansion)
      (clusterTerm expansion)
      (supportLocality expansion))

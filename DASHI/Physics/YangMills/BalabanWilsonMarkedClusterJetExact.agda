{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanWilsonMarkedClusterJetExact where

------------------------------------------------------------------------
-- BIVARIATE JET COMPILER FOR THE LITERAL TWO-WILSON MARKED EXPANSION
--
-- Only the coefficient of s*t in log Z is consumed by the mass-gap route.
-- Therefore W1 does not need a derivative oracle on arbitrary cluster
-- functions.  A source-native cluster theorem may instead expose the exact
-- bivariate Taylor jet of every marked cluster term.
--
-- The compiler below proves:
--
--   logJet = sum_Y clusterJet(Y)
--     => mixed(logJet) = sum_Y mixed(clusterJet(Y)),
--
-- and removes terms missing either Wilson support when their mixed coefficient
-- is zero.  This is finite coefficient algebra; analyticity remains only in the
-- theorem that constructs the jets from the actual Wilson-Gibbs/polymer model.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark

record TwoSourceJet : Set where
  constructor jet
  field
    constant left right mixed : ℚ

open TwoSourceJet public

zeroJet : TwoSourceJet
zeroJet = jet 0ℚ 0ℚ 0ℚ 0ℚ

addJet : TwoSourceJet → TwoSourceJet → TwoSourceJet
addJet first second =
  jet
    (constant first + constant second)
    (left first + left second)
    (right first + right second)
    (mixed first + mixed second)

sumJets : List TwoSourceJet → TwoSourceJet
sumJets [] = zeroJet
sumJets (value ∷ values) = addJet value (sumJets values)

mapJets :
  ∀ {A : Set} →
  (A → TwoSourceJet) →
  List A →
  List TwoSourceJet
mapJets function [] = []
mapJets function (value ∷ values) =
  function value ∷ mapJets function values

mixedOfSumJets :
  ∀ jets →
  mixed (sumJets jets)
  ≡ TwoMark.sumℚ (TwoMark.map mixed jets)
mixedOfSumJets [] = refl
mixedOfSumJets (value ∷ values)
  rewrite mixedOfSumJets values = refl

mixedOfMappedJetSum :
  ∀ {A : Set}
    (items : List A)
    (termJet : A → TwoSourceJet) →
  mixed (sumJets (mapJets termJet items))
  ≡
  TwoMark.sumℚ (TwoMark.map (λ item → mixed (termJet item)) items)
mixedOfMappedJetSum [] termJet = refl
mixedOfMappedJetSum (item ∷ items) termJet
  rewrite mixedOfMappedJetSum items termJet = refl

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

record JetSupportLocality
    {Cluster : Set}
    (clusterJet : Cluster → TwoSourceJet) : Set₁ where
  field
    touchesLeft touchesRight : Cluster → Bool

    mixedZeroWhenMissingLeft :
      ∀ cluster →
      touchesLeft cluster ≡ false →
      mixed (clusterJet cluster) ≡ 0ℚ

    mixedZeroWhenMissingRight :
      ∀ cluster →
      touchesRight cluster ≡ false →
      mixed (clusterJet cluster) ≡ 0ℚ

open JetSupportLocality public

sumMixedFiltersToTwoSupport :
  ∀ {Cluster : Set}
    (clusters : List Cluster)
    (clusterJet : Cluster → TwoSourceJet)
    (locality : JetSupportLocality clusterJet) →
  TwoMark.sumℚ
    (TwoMark.map (λ cluster → mixed (clusterJet cluster)) clusters)
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → mixed (clusterJet cluster))
      (filterTwoSupport
        (touchesLeft locality)
        (touchesRight locality)
        clusters))
sumMixedFiltersToTwoSupport [] clusterJet locality = refl
sumMixedFiltersToTwoSupport (cluster ∷ clusters) clusterJet locality
  with touchesLeft locality cluster | touchesRight locality cluster
... | true | true
  rewrite sumMixedFiltersToTwoSupport clusters clusterJet locality = refl
... | true | false
  rewrite mixedZeroWhenMissingRight locality cluster refl
        | ℚP.+-identityˡ
            (TwoMark.sumℚ
              (TwoMark.map (λ item → mixed (clusterJet item)) clusters))
        | sumMixedFiltersToTwoSupport clusters clusterJet locality = refl
... | false | true
  rewrite mixedZeroWhenMissingLeft locality cluster refl
        | ℚP.+-identityˡ
            (TwoMark.sumℚ
              (TwoMark.map (λ item → mixed (clusterJet item)) clusters))
        | sumMixedFiltersToTwoSupport clusters clusterJet locality = refl
... | false | false
  rewrite mixedZeroWhenMissingLeft locality cluster refl
        | ℚP.+-identityˡ
            (TwoMark.sumℚ
              (TwoMark.map (λ item → mixed (clusterJet item)) clusters))
        | sumMixedFiltersToTwoSupport clusters clusterJet locality = refl

record WilsonMarkedLogJetExpansion (Cluster : Set) : Set₁ where
  field
    clusters : List Cluster

    literalLogPartitionJet : TwoSourceJet
    clusterJet : Cluster → TwoSourceJet

    literalLogPartitionJetExpansion :
      literalLogPartitionJet
      ≡ sumJets (mapJets clusterJet clusters)

    supportLocality : JetSupportLocality clusterJet

open WilsonMarkedLogJetExpansion public

mixedLogJetIsTwoSupportClusterSum :
  ∀ {Cluster}
    (expansion : WilsonMarkedLogJetExpansion Cluster) →
  mixed (literalLogPartitionJet expansion)
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster → mixed (clusterJet expansion cluster))
      (filterTwoSupport
        (touchesLeft (supportLocality expansion))
        (touchesRight (supportLocality expansion))
        (clusters expansion)))
mixedLogJetIsTwoSupportClusterSum expansion =
  trans
    (cong mixed (literalLogPartitionJetExpansion expansion))
    (trans
      (mixedOfMappedJetSum
        (clusters expansion)
        (clusterJet expansion))
      (sumMixedFiltersToTwoSupport
        (clusters expansion)
        (clusterJet expansion)
        (supportLocality expansion)))

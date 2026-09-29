{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedPolymerExpansionExact where

------------------------------------------------------------------------
-- Literal two-Wilson marked polymer expansion from the published finite KP
-- theorem.
--
-- For each finite cutoff and Wilson pair, the physical source supplies one
-- source-parameterized polymer gas kpAt(s,t).  The cluster carrier is required
-- to be the same finite carrier throughout the common source neighbourhood.
-- Kotecky--Preiss then proves the logarithm/cluster identity pointwise in
-- (s,t).  This module packages those identities into the exact
-- SupportIndexedMarkedClusterExpansion consumed by W1.
--
-- No identification with Bałaban's printed bond-valued J is made here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; ∣_∣; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP
import DASHI.Physics.YangMills.BalabanEnumeratedMarkedKoteckyPreissExact as Enumerated
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterDifferentiationExact as Diff
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark

record TwoWilsonSourceParameterizedKP
    (Observable Source Polymer Cluster Volume : Set) : Set₂ where
  field
    volumeOfCutoff : Nat → Volume

    kpAt :
      Nat → Observable → Observable → Source → Source →
      KP.KoteckyPreissTwoWeightData Polymer ℚ Cluster Volume

    enumeratedAt :
      ∀ cutoff left right sourceLeft sourceRight →
      Enumerated.EnumeratedKPClusterFamily
        (kpAt cutoff left right sourceLeft sourceRight)

    publishedAt :
      ∀ cutoff left right sourceLeft sourceRight →
      KP.PublishedKoteckyPreissTwoWeightTheorem
        (kpAt cutoff left right sourceLeft sourceRight)

    conditionAt :
      ∀ cutoff left right sourceLeft sourceRight →
      KP.KoteckyPreissTwoWeightCondition
        (kpAt cutoff left right sourceLeft sourceRight)

    commonClusters :
      Nat → Observable → Observable → List Cluster

    clusterEnumerationSameAcrossSources :
      ∀ cutoff left right sourceLeft sourceRight →
      Enumerated.clusters
        (enumeratedAt cutoff left right sourceLeft sourceRight)
        (volumeOfCutoff cutoff)
      ≡ commonClusters cutoff left right

    touchesLeft touchesRight :
      Nat → Observable → Observable → Cluster → Bool

    clusterFunctionalMissingLeftIndependent :
      ∀ cutoff left right cluster →
      touchesLeft cutoff left right cluster ≡ false →
      ∀ sourceLeft₁ sourceLeft₂ sourceRight →
      KP.clusterFunctional
        (kpAt cutoff left right sourceLeft₁ sourceRight)
        cluster
      ≡
      KP.clusterFunctional
        (kpAt cutoff left right sourceLeft₂ sourceRight)
        cluster

    clusterFunctionalMissingRightIndependent :
      ∀ cutoff left right cluster →
      touchesRight cutoff left right cluster ≡ false →
      ∀ sourceLeft sourceRight₁ sourceRight₂ →
      KP.clusterFunctional
        (kpAt cutoff left right sourceLeft sourceRight₁)
        cluster
      ≡
      KP.clusterFunctional
        (kpAt cutoff left right sourceLeft sourceRight₂)
        cluster

open TwoWilsonSourceParameterizedKP public

markedLogPartition :
  ∀ {Observable Source Polymer Cluster Volume} →
  TwoWilsonSourceParameterizedKP Observable Source Polymer Cluster Volume →
  Nat → Observable → Observable → Source → Source → ℚ
markedLogPartition family cutoff left right sourceLeft sourceRight =
  let kp = kpAt family cutoff left right sourceLeft sourceRight in
  KP.logarithm kp
    (KP.partitionFunction kp (volumeOfCutoff family cutoff))

markedClusterTerm :
  ∀ {Observable Source Polymer Cluster Volume} →
  TwoWilsonSourceParameterizedKP Observable Source Polymer Cluster Volume →
  Nat → Observable → Observable → Cluster → Source → Source → ℚ
markedClusterTerm family cutoff left right cluster sourceLeft sourceRight =
  KP.clusterFunctional
    (kpAt family cutoff left right sourceLeft sourceRight)
    cluster

pointwiseMarkedKPConclusion :
  ∀ {Observable Source Polymer Cluster Volume}
    (family :
      TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume)
    cutoff left right sourceLeft sourceRight →
  KP.KoteckyPreissTwoWeightConclusion
    (kpAt family cutoff left right sourceLeft sourceRight)
pointwiseMarkedKPConclusion family cutoff left right sourceLeft sourceRight =
  KP.conclusionFromCondition
    (publishedAt family cutoff left right sourceLeft sourceRight)
    (conditionAt family cutoff left right sourceLeft sourceRight)

markedLogPartitionExpansionExact :
  ∀ {Observable Source Polymer Cluster Volume}
    (family :
      TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume)
    cutoff left right sourceLeft sourceRight →
  markedLogPartition family cutoff left right sourceLeft sourceRight
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster →
        markedClusterTerm family cutoff left right cluster sourceLeft sourceRight)
      (commonClusters family cutoff left right))
markedLogPartitionExpansionExact family cutoff left right sourceLeft sourceRight =
  let
    kp = kpAt family cutoff left right sourceLeft sourceRight
    enumerated = enumeratedAt family cutoff left right sourceLeft sourceRight
    conclusion =
      pointwiseMarkedKPConclusion
        family cutoff left right sourceLeft sourceRight

    sourceExpansion =
      Enumerated.enumeratedLogPartitionExpansion
        enumerated conclusion (volumeOfCutoff family cutoff)

    clustersEqual =
      clusterEnumerationSameAcrossSources
        family cutoff left right sourceLeft sourceRight
  in
  trans sourceExpansion
    (cong
      (λ clusters →
        TwoMark.sumℚ
          (TwoMark.map
            (λ cluster →
              markedClusterTerm family cutoff left right cluster
                sourceLeft sourceRight)
            clusters))
      clustersEqual)

supportIndexedMarkedExpansionFromKP :
  ∀ {Observable Source Polymer Cluster Volume}
    (family :
      TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume)
    (derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source)
    cutoff left right →
  Diff.SupportIndexedMarkedClusterExpansion
    Source Cluster
    (derivativeCalculus cutoff left right)
supportIndexedMarkedExpansionFromKP
    family derivativeCalculus cutoff left right = record
  { Diff.SupportIndexedMarkedClusterExpansion.clusters =
      commonClusters family cutoff left right
  ; Diff.SupportIndexedMarkedClusterExpansion.logPartition =
      markedLogPartition family cutoff left right
  ; Diff.SupportIndexedMarkedClusterExpansion.clusterTerm =
      markedClusterTerm family cutoff left right
  ; Diff.SupportIndexedMarkedClusterExpansion.logPartitionExpansionExact =
      markedLogPartitionExpansionExact family cutoff left right
  ; Diff.SupportIndexedMarkedClusterExpansion.supportLocality = record
      { Diff.MarkedClusterSupportLocality.touchesLeft =
          touchesLeft family cutoff left right
      ; Diff.MarkedClusterSupportLocality.touchesRight =
          touchesRight family cutoff left right
      ; Diff.MarkedClusterSupportLocality.missingLeftMakesTermIndependent =
          clusterFunctionalMissingLeftIndependent family cutoff left right
      ; Diff.MarkedClusterSupportLocality.missingRightMakesTermIndependent =
          clusterFunctionalMissingRightIndependent family cutoff left right
      }
  }


------------------------------------------------------------------------
-- Differentiable two-Wilson KP family.
--
-- The pointwise KP theorem above supplies the source-dependent log-partition
-- expansion.  The only additional calculus needed for W1 is a mixed derivative
-- on the common source neighbourhood, its ordinary vanishing laws, and the
-- identification of the physical normalized Wilson response with the mixed
-- derivative of this very same marked log partition.
------------------------------------------------------------------------

record DifferentiableTwoWilsonKP
    {Observable Source Polymer Cluster Volume : Set}
    (family :
      TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume)
    : Set₂ where
  field
    derivativeCalculus :
      Nat → Observable → Observable →
      Diff.MixedSourceDerivativeCalculus Source

    derivativeVanishing :
      ∀ cutoff left right →
      Diff.MixedSourceDerivativeVanishing
        (derivativeCalculus cutoff left right)

open DifferentiableTwoWilsonKP public

supportIndexedExpansion :
  ∀ {Observable Source Polymer Cluster Volume}
    {family :
      TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume}
    (differentiable : DifferentiableTwoWilsonKP family) →
  ∀ cutoff left right →
  Diff.SupportIndexedMarkedClusterExpansion
    Source Cluster
    (derivativeCalculus differentiable cutoff left right)
supportIndexedExpansion {family = family} differentiable =
  supportIndexedMarkedExpansionFromKP
    family
    (derivativeCalculus differentiable)

twoWilsonMixedDerivativeIsTwoSupportClusterSum :
  ∀ {Observable Source Polymer Cluster Volume}
    {family :
      TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume}
    (differentiable : DifferentiableTwoWilsonKP family)
    cutoff left right →
  Diff.mixedDerivative
    (derivativeCalculus differentiable cutoff left right)
    (markedLogPartition family cutoff left right)
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster →
        Diff.mixedDerivative
          (derivativeCalculus differentiable cutoff left right)
          (markedClusterTerm family cutoff left right cluster))
      (Diff.filterTwoSupport
        (touchesLeft family cutoff left right)
        (touchesRight family cutoff left right)
        (commonClusters family cutoff left right)))
twoWilsonMixedDerivativeIsTwoSupportClusterSum
    {family = family} differentiable cutoff left right =
  Diff.mixedDerivativeSupportIndexedExpansionIsConnectingSum
    (derivativeVanishing differentiable cutoff left right)
    (supportIndexedExpansion differentiable cutoff left right)

------------------------------------------------------------------------
-- W3 source-native charge attachment.
--
-- CMP116 supplies the differentiated spatial estimate; KP supplies the cluster
-- carrier and exact log expansion.  This record joins them without identifying
-- a Wilson cluster with a historical generic extensionActivity.
------------------------------------------------------------------------

record TwoWilsonCMP116ClusterCharge
    {Observable Source Polymer Cluster Volume : Set}
    {family :
      TwoWilsonSourceParameterizedKP
        Observable Source Polymer Cluster Volume}
    (differentiable : DifferentiableTwoWilsonKP family)
    : Set₂ where
  field
    shellCharge :
      Nat → Observable → Observable → Cluster → ℚ

    pointwiseDifferentiatedClusterBelowCharge :
      ∀ cutoff left right cluster →
      ∣ Diff.mixedDerivative
          (derivativeCalculus differentiable cutoff left right)
          (markedClusterTerm family cutoff left right cluster) ∣
      ≤ shellCharge cutoff left right cluster

open TwoWilsonCMP116ClusterCharge public

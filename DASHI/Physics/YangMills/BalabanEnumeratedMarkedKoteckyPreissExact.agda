{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanEnumeratedMarkedKoteckyPreissExact where

------------------------------------------------------------------------
-- Enumerated finite marked Kotecky--Preiss specialization.
--
-- The existing primary KP ABI stores its cluster-expansion sum as one abstract
-- scalar.  W1 needs the actual finite cluster carrier so that support incidence,
-- source locality and the two-mark filter are visible to Agda.
--
-- This module keeps the published KP theorem as the source of
--
--   log Z = cluster expansion,
--
-- but requires an explicit finite cluster enumeration and proves the list-form
-- identity consumed by the Wilson marked differentiation compiler.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP

record EnumeratedKPClusterFamily
    {Polymer Cluster FiniteVolume : Set}
    (kp : KP.KoteckyPreissTwoWeightData
      Polymer ℚ Cluster FiniteVolume) : Set₁ where
  field
    clusters : FiniteVolume → List Cluster

    clusterExpansionSumIsEnumeration :
      ∀ volume →
      KP.clusterExpansionSum kp volume
      ≡
      TwoMark.sumℚ
        (TwoMark.map
          (KP.clusterFunctional kp)
          (clusters volume))

open EnumeratedKPClusterFamily public

enumeratedLogPartitionExpansion :
  ∀ {Polymer Cluster FiniteVolume}
    {kp : KP.KoteckyPreissTwoWeightData
      Polymer ℚ Cluster FiniteVolume}
    (enumerated : EnumeratedKPClusterFamily kp)
    (conclusion : KP.KoteckyPreissTwoWeightConclusion kp)
    volume →
  KP.logarithm kp (KP.partitionFunction kp volume)
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (KP.clusterFunctional kp)
      (clusters enumerated volume))
enumeratedLogPartitionExpansion {kp = kp} enumerated conclusion volume =
  let
    open import Relation.Binary.PropositionalEquality using (trans)
  in
  trans
    (KP.logarithmClusterExpansion conclusion volume)
    (clusterExpansionSumIsEnumeration enumerated volume)

record PublishedEnumeratedKPTheorem
    {Polymer Cluster FiniteVolume : Set}
    (kp : KP.KoteckyPreissTwoWeightData
      Polymer ℚ Cluster FiniteVolume)
    (enumerated : EnumeratedKPClusterFamily kp) : Set₁ where
  field
    published :
      KP.PublishedKoteckyPreissTwoWeightTheorem kp

open PublishedEnumeratedKPTheorem public

enumeratedConclusionFromCondition :
  ∀ {Polymer Cluster FiniteVolume}
    {kp : KP.KoteckyPreissTwoWeightData
      Polymer ℚ Cluster FiniteVolume}
    {enumerated : EnumeratedKPClusterFamily kp} →
  PublishedEnumeratedKPTheorem kp enumerated →
  KP.KoteckyPreissTwoWeightCondition kp →
  KP.KoteckyPreissTwoWeightConclusion kp
enumeratedConclusionFromCondition theorem condition =
  KP.conclusionFromCondition (published theorem) condition

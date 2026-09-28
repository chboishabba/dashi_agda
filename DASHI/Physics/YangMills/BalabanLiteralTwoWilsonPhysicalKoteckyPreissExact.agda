{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonPhysicalKoteckyPreissExact where

------------------------------------------------------------------------
-- Literal two-Wilson source family from the physical terminal two-weight KP
-- package.
--
-- The marked-polymer layer previously asked the caller for an opaque
-- pointwise KoteckyPreissTwoWeightCondition.  The repository already has the
-- source-faithful producer of exactly that condition:
--
--   PhysicalTerminalTwoWeightKPPackage
--     -> RootedTerminalToTwoWeightKPIdentification
--     -> KoteckyPreissTwoWeightCondition.
--
-- This module composes the two.  The genuine physical payment is therefore the
-- same-object identification of the literal polymer activity/incompatibility
-- sum with the terminal rooted-shell carrier; the KP condition itself is
-- compiled.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanClayT5KoteckyPreissTwoWeightPrimaryExact as KP
import DASHI.Physics.YangMills.BalabanClayT5PhysicalTwoWeightKoteckyPreissExact as PhysicalKP
import DASHI.Physics.YangMills.BalabanEnumeratedMarkedKoteckyPreissExact as Enumerated
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonMarkedPolymerExpansionExact as Marked
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark

record LiteralTwoWilsonPhysicalKoteckyPreissFamily
    (Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set)
    : Set₂ where
  field
    volumeOfCutoff : Nat → FiniteVolume

    physicalAt :
      Nat → Observable → Observable → Source → Source →
      PhysicalKP.PhysicalTerminalTwoWeightKPPackage
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume

    enumeratedAt :
      ∀ cutoff left right sourceLeft sourceRight →
      Enumerated.EnumeratedKPClusterFamily
        (PhysicalKP.kpData
          (physicalAt cutoff left right sourceLeft sourceRight))

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
        (PhysicalKP.kpData
          (physicalAt cutoff left right sourceLeft₁ sourceRight))
        cluster
      ≡
      KP.clusterFunctional
        (PhysicalKP.kpData
          (physicalAt cutoff left right sourceLeft₂ sourceRight))
        cluster

    clusterFunctionalMissingRightIndependent :
      ∀ cutoff left right cluster →
      touchesRight cutoff left right cluster ≡ false →
      ∀ sourceLeft sourceRight₁ sourceRight₂ →
      KP.clusterFunctional
        (PhysicalKP.kpData
          (physicalAt cutoff left right sourceLeft sourceRight₁))
        cluster
      ≡
      KP.clusterFunctional
        (PhysicalKP.kpData
          (physicalAt cutoff left right sourceLeft sourceRight₂))
        cluster

open LiteralTwoWilsonPhysicalKoteckyPreissFamily public

asTwoWilsonSourceParameterizedKP :
  ∀ {Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume} →
  LiteralTwoWilsonPhysicalKoteckyPreissFamily
    Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume →
  Marked.TwoWilsonSourceParameterizedKP
    Observable Source Polymer Cluster FiniteVolume
asTwoWilsonSourceParameterizedKP family = record
  { Marked.TwoWilsonSourceParameterizedKP.volumeOfCutoff =
      volumeOfCutoff family
  ; Marked.TwoWilsonSourceParameterizedKP.kpAt =
      λ cutoff left right sourceLeft sourceRight →
        PhysicalKP.kpData
          (physicalAt family cutoff left right sourceLeft sourceRight)
  ; Marked.TwoWilsonSourceParameterizedKP.enumeratedAt =
      enumeratedAt family
  ; Marked.TwoWilsonSourceParameterizedKP.publishedAt =
      λ cutoff left right sourceLeft sourceRight →
        PhysicalKP.publishedKP
          (physicalAt family cutoff left right sourceLeft sourceRight)
  ; Marked.TwoWilsonSourceParameterizedKP.conditionAt =
      λ cutoff left right sourceLeft sourceRight →
        PhysicalKP.physicalTerminalTwoWeightKPCondition
          (physicalAt family cutoff left right sourceLeft sourceRight)
  ; Marked.TwoWilsonSourceParameterizedKP.commonClusters =
      commonClusters family
  ; Marked.TwoWilsonSourceParameterizedKP.clusterEnumerationSameAcrossSources =
      clusterEnumerationSameAcrossSources family
  ; Marked.TwoWilsonSourceParameterizedKP.touchesLeft =
      touchesLeft family
  ; Marked.TwoWilsonSourceParameterizedKP.touchesRight =
      touchesRight family
  ; Marked.TwoWilsonSourceParameterizedKP.clusterFunctionalMissingLeftIndependent =
      clusterFunctionalMissingLeftIndependent family
  ; Marked.TwoWilsonSourceParameterizedKP.clusterFunctionalMissingRightIndependent =
      clusterFunctionalMissingRightIndependent family
  }

literalPhysicalMarkedLogPartitionExpansionExact :
  ∀ {Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume}
    (family :
      LiteralTwoWilsonPhysicalKoteckyPreissFamily
        Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume)
    cutoff left right sourceLeft sourceRight →
  Marked.markedLogPartition
    (asTwoWilsonSourceParameterizedKP family)
    cutoff left right sourceLeft sourceRight
  ≡
  TwoMark.sumℚ
    (TwoMark.map
      (λ cluster →
        KP.clusterFunctional
          (PhysicalKP.kpData
            (physicalAt family cutoff left right sourceLeft sourceRight))
          cluster)
      (commonClusters family cutoff left right))
literalPhysicalMarkedLogPartitionExpansionExact
    family cutoff left right sourceLeft sourceRight =
  Marked.markedLogPartitionExpansionExact
    (asTwoWilsonSourceParameterizedKP family)
    cutoff left right sourceLeft sourceRight

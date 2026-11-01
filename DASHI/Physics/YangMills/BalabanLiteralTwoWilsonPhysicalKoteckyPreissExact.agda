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
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonPhysicalPolymerIdentificationExact as Identified
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstKPDataExact as SourceFirst
import DASHI.Physics.YangMills.BalabanClayT5PublishedTerminalCriterionReuseExact as Terminal

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


------------------------------------------------------------------------
-- Preferred source-first family.
--
-- Each source point supplies the concrete physical-polymer same-object theorem,
-- not a preassembled PhysicalTerminalTwoWeightKPPackage.  The latter is
-- compiler output through Identified.asPhysicalTerminalTwoWeightKPPackage.
------------------------------------------------------------------------

record LiteralTwoWilsonIdentifiedKoteckyPreissFamily
    (Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set)
    (PhysicalIncompatible : Polymer → Polymer → Set)
    : Set₂ where
  field
    volumeOfCutoff : Nat → FiniteVolume

    identifiedAt :
      Nat → Observable → Observable → Source → Source →
      Identified.LiteralTwoWilsonPhysicalPolymerIdentification
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible

    enumeratedAt :
      ∀ cutoff left right sourceLeft sourceRight →
      Enumerated.EnumeratedKPClusterFamily
        (Identified.kpData
          (identifiedAt cutoff left right sourceLeft sourceRight))

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
        (Identified.kpData
          (identifiedAt cutoff left right sourceLeft₁ sourceRight))
        cluster
      ≡
      KP.clusterFunctional
        (Identified.kpData
          (identifiedAt cutoff left right sourceLeft₂ sourceRight))
        cluster

    clusterFunctionalMissingRightIndependent :
      ∀ cutoff left right cluster →
      touchesRight cutoff left right cluster ≡ false →
      ∀ sourceLeft sourceRight₁ sourceRight₂ →
      KP.clusterFunctional
        (Identified.kpData
          (identifiedAt cutoff left right sourceLeft sourceRight₁))
        cluster
      ≡
      KP.clusterFunctional
        (Identified.kpData
          (identifiedAt cutoff left right sourceLeft sourceRight₂))
        cluster

open LiteralTwoWilsonIdentifiedKoteckyPreissFamily public

identifiedFamilyAsPhysicalFamily :
  ∀ {Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible} →
  LiteralTwoWilsonIdentifiedKoteckyPreissFamily
    Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible →
  LiteralTwoWilsonPhysicalKoteckyPreissFamily
    Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume
identifiedFamilyAsPhysicalFamily family = record
  { LiteralTwoWilsonPhysicalKoteckyPreissFamily.volumeOfCutoff =
      volumeOfCutoff family
  ; LiteralTwoWilsonPhysicalKoteckyPreissFamily.physicalAt =
      λ cutoff left right sourceLeft sourceRight →
        Identified.asPhysicalTerminalTwoWeightKPPackage
          (identifiedAt family cutoff left right sourceLeft sourceRight)
  ; LiteralTwoWilsonPhysicalKoteckyPreissFamily.enumeratedAt =
      enumeratedAt family
  ; LiteralTwoWilsonPhysicalKoteckyPreissFamily.commonClusters =
      commonClusters family
  ; LiteralTwoWilsonPhysicalKoteckyPreissFamily.clusterEnumerationSameAcrossSources =
      clusterEnumerationSameAcrossSources family
  ; LiteralTwoWilsonPhysicalKoteckyPreissFamily.touchesLeft =
      touchesLeft family
  ; LiteralTwoWilsonPhysicalKoteckyPreissFamily.touchesRight =
      touchesRight family
  ; LiteralTwoWilsonPhysicalKoteckyPreissFamily.clusterFunctionalMissingLeftIndependent =
      clusterFunctionalMissingLeftIndependent family
  ; LiteralTwoWilsonPhysicalKoteckyPreissFamily.clusterFunctionalMissingRightIndependent =
      clusterFunctionalMissingRightIndependent family
  }

identifiedFamilyAsTwoWilsonSourceParameterizedKP :
  ∀ {Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible} →
  LiteralTwoWilsonIdentifiedKoteckyPreissFamily
    Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible →
  Marked.TwoWilsonSourceParameterizedKP
    Observable Source Polymer Cluster FiniteVolume
identifiedFamilyAsTwoWilsonSourceParameterizedKP family =
  asTwoWilsonSourceParameterizedKP
    (identifiedFamilyAsPhysicalFamily family)

identifiedFamilyKPCondition :
  ∀ {Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    (family :
      LiteralTwoWilsonIdentifiedKoteckyPreissFamily
        Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible)
    cutoff left right sourceLeft sourceRight →
  KP.KoteckyPreissTwoWeightCondition
    (Identified.kpData
      (identifiedAt family cutoff left right sourceLeft sourceRight))
identifiedFamilyKPCondition family cutoff left right sourceLeft sourceRight =
  Identified.literalPhysicalKPCondition
    (identifiedAt family cutoff left right sourceLeft sourceRight)


------------------------------------------------------------------------
-- Strong preferred source-first family.
--
-- The previous preferred family still accepted an already assembled
-- LiteralTwoWilsonPhysicalPolymerIdentification at every source point.  That
-- record is now compiler output.  The caller supplies only the literal
-- terminal gas, the source-first analytic KP data/meaning, and the published
-- theorem on that exact datum.
------------------------------------------------------------------------

record LiteralTwoWilsonSourceFirstKoteckyPreissFamily
    (Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume : Set)
    (PhysicalIncompatible : Polymer → Polymer → Set)
    : Set₂ where
  field
    volumeOfCutoff : Nat → FiniteVolume
    anchor : Polymer → Link

    physicalTerminalAt :
      Nat → Observable → Observable → Source → Source →
      Terminal.PhysicalTerminalRootedSumIdentification
        Scale ShellVolume Root Polymer Link

    sourceAt :
      ∀ cutoff left right sourceLeft sourceRight →
      SourceFirst.LiteralTerminalKPAnalyticData
        Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible
        (physicalTerminalAt cutoff left right sourceLeft sourceRight)
        anchor

    meaningAt :
      ∀ cutoff left right sourceLeft sourceRight →
      SourceFirst.LiteralTerminalKPAnalyticMeaning
        (sourceAt cutoff left right sourceLeft sourceRight)

    publishedAt :
      ∀ cutoff left right sourceLeft sourceRight →
      SourceFirst.PublishedLiteralTerminalKP
        (sourceAt cutoff left right sourceLeft sourceRight)
        (meaningAt cutoff left right sourceLeft sourceRight)

    enumeratedAt :
      ∀ cutoff left right sourceLeft sourceRight →
      Enumerated.EnumeratedKPClusterFamily
        (SourceFirst.literalTerminalKPData
          (sourceAt cutoff left right sourceLeft sourceRight)
          (meaningAt cutoff left right sourceLeft sourceRight))

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
        (SourceFirst.literalTerminalKPData
          (sourceAt cutoff left right sourceLeft₁ sourceRight)
          (meaningAt cutoff left right sourceLeft₁ sourceRight))
        cluster
      ≡
      KP.clusterFunctional
        (SourceFirst.literalTerminalKPData
          (sourceAt cutoff left right sourceLeft₂ sourceRight)
          (meaningAt cutoff left right sourceLeft₂ sourceRight))
        cluster

    clusterFunctionalMissingRightIndependent :
      ∀ cutoff left right cluster →
      touchesRight cutoff left right cluster ≡ false →
      ∀ sourceLeft sourceRight₁ sourceRight₂ →
      KP.clusterFunctional
        (SourceFirst.literalTerminalKPData
          (sourceAt cutoff left right sourceLeft sourceRight₁)
          (meaningAt cutoff left right sourceLeft sourceRight₁))
        cluster
      ≡
      KP.clusterFunctional
        (SourceFirst.literalTerminalKPData
          (sourceAt cutoff left right sourceLeft sourceRight₂)
          (meaningAt cutoff left right sourceLeft sourceRight₂))
        cluster

open LiteralTwoWilsonSourceFirstKoteckyPreissFamily public

sourceFirstIdentifiedAt :
  ∀ {Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible}
    (family :
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily
        Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible)
    cutoff left right sourceLeft sourceRight →
  Identified.LiteralTwoWilsonPhysicalPolymerIdentification
    Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible
sourceFirstIdentifiedAt family cutoff left right sourceLeft sourceRight =
  SourceFirst.sourceFirstPhysicalPolymerIdentification
    (sourceAt family cutoff left right sourceLeft sourceRight)
    (meaningAt family cutoff left right sourceLeft sourceRight)
    (publishedAt family cutoff left right sourceLeft sourceRight)

sourceFirstAsIdentifiedFamily :
  ∀ {Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible} →
  LiteralTwoWilsonSourceFirstKoteckyPreissFamily
    Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible →
  LiteralTwoWilsonIdentifiedKoteckyPreissFamily
    Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible
sourceFirstAsIdentifiedFamily family = record
  { LiteralTwoWilsonIdentifiedKoteckyPreissFamily.volumeOfCutoff =
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily.volumeOfCutoff family
  ; LiteralTwoWilsonIdentifiedKoteckyPreissFamily.identifiedAt =
      sourceFirstIdentifiedAt family
  ; LiteralTwoWilsonIdentifiedKoteckyPreissFamily.enumeratedAt =
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily.enumeratedAt family
  ; LiteralTwoWilsonIdentifiedKoteckyPreissFamily.commonClusters =
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily.commonClusters family
  ; LiteralTwoWilsonIdentifiedKoteckyPreissFamily.clusterEnumerationSameAcrossSources =
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily.clusterEnumerationSameAcrossSources family
  ; LiteralTwoWilsonIdentifiedKoteckyPreissFamily.touchesLeft =
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily.touchesLeft family
  ; LiteralTwoWilsonIdentifiedKoteckyPreissFamily.touchesRight =
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily.touchesRight family
  ; LiteralTwoWilsonIdentifiedKoteckyPreissFamily.clusterFunctionalMissingLeftIndependent =
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily.clusterFunctionalMissingLeftIndependent family
  ; LiteralTwoWilsonIdentifiedKoteckyPreissFamily.clusterFunctionalMissingRightIndependent =
      LiteralTwoWilsonSourceFirstKoteckyPreissFamily.clusterFunctionalMissingRightIndependent family
  }

sourceFirstAsTwoWilsonSourceParameterizedKP :
  ∀ {Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume PhysicalIncompatible} →
  LiteralTwoWilsonSourceFirstKoteckyPreissFamily
    Observable Source Scale ShellVolume Root Polymer Link Cluster FiniteVolume
    PhysicalIncompatible →
  Marked.TwoWilsonSourceParameterizedKP
    Observable Source Polymer Cluster FiniteVolume
sourceFirstAsTwoWilsonSourceParameterizedKP family =
  identifiedFamilyAsTwoWilsonSourceParameterizedKP
    (sourceFirstAsIdentifiedFamily family)

independentPhysicalPolymerIdentificationSelectionRequired : Bool
independentPhysicalPolymerIdentificationSelectionRequired = false

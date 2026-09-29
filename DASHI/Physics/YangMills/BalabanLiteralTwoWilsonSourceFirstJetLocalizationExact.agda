{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact where

------------------------------------------------------------------------
-- H1 SOURCE-FIRST WILSON JET LOCALIZATION
--
-- Eliminate the last free jet-family selection in
-- BalabanLiteralWilsonMarkedJetLocalizationSourceExact.
--
-- Every marked jet below is produced by the source-first normalized Wilson
-- jet expansion, hence:
--
--   * its cluster list is the SAME source-first KP common enumeration;
--   * every cluster jet is certified as the bidegree-(1,1) germ of the ACTUAL
--     source-first KP cluster functional;
--   * the sum of those literal cluster germs is the exact normalized
--     finite-moment log jet.
--
-- W3 is then stated directly on these same jets and the existing physical
-- TraversalShellData.  No independent W1 jet source survives this adapter.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; ∣_∣; _≤_)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanClayT5TwoMarkedConnectedClusterTailExact as TwoMark
import DASHI.Physics.YangMills.YangMillsRationalAbsoluteCovarianceExtensionRound575Exact as R575
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonMixedLogCovarianceRound573Exact as R573
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonPhysicalKoteckyPreissExact as PhysicalKP
import DASHI.Physics.YangMills.BalabanLiteralTwoWilsonSourceFirstNormalizedJetExact as SourceJet
import DASHI.Physics.YangMills.BalabanWilsonMarkedClusterJetExact as Jet
import DASHI.Physics.YangMills.BalabanLiteralWilsonMarkedJetLocalizationSourceExact as JetLocalization
import DASHI.Physics.YangMills.YangMillsSourceFirstWilsonCovarianceRound556Exact as R556
open import DASHI.Physics.YangMills.CompactLieProofLevel

record SourceFirstLiteralWilsonJetLocalization
    {Measure Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume
      ShellScale ShellRoot : Set}
    {PhysicalIncompatible : Polymer → Polymer → Set}
    (family :
      PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily
        Observable ℚ Scale ShellVolume Root Polymer Link Cluster FiniteVolume
        PhysicalIncompatible)
    (dataSet :
      Gram.PhysicalMeasureConvergenceData Measure Observable ℚ)
    (laws :
      R575.RationalCovarianceContinuityLaws dataSet)
    : Set₂ where
  field
    normalizedJetAt :
      ∀ cutoff left right →
      SourceJet.SourceFirstNormalizedWilsonJetExpansion
        family dataSet laws cutoff left right

    shellData :
      Shell.TraversalShellData ShellScale FiniteVolume ShellRoot

    scaleOfCutoff : Nat → ShellScale

    physicalDistance : Observable → Observable → Nat
    connectingRoot : Nat → Observable → Observable → ShellRoot

    ConnectingClusterMeetsBothSupports :
      Nat → Observable → Observable → Set

    shellCharge :
      Nat → Observable → Observable → Cluster → ℚ

    pointwiseLiteralWilsonJetLocalization :
      ∀ cutoff left right cluster →
      ∣
        Jet.mixed
          (SourceJet.clusterJet
            (normalizedJetAt cutoff left right)
            cluster)
      ∣
      ≤ shellCharge cutoff left right cluster

    localizedLiteralShellChargeSum :
      ∀ cutoff left right →
      let source = normalizedJetAt cutoff left right
          locality = SourceJet.supportLocality source
      in
      TwoMark.sumℚ
        (TwoMark.map
          (shellCharge cutoff left right)
          (Jet.filterTwoSupport
            (Jet.touchesLeft locality)
            (Jet.touchesRight locality)
            (PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily.commonClusters
              family cutoff left right)))
      ≤
      Shell.rootedShell shellData
        (scaleOfCutoff cutoff)
        (PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily.volumeOfCutoff
          family cutoff)
        (connectingRoot cutoff left right)
        (physicalDistance left right)

open SourceFirstLiteralWilsonJetLocalization public

markedJetExpansionAt :
  ∀ {Measure Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume
      ShellScale ShellRoot PhysicalIncompatible family dataSet laws}
    (source :
      SourceFirstLiteralWilsonJetLocalization
        {Measure = Measure}
        {Observable = Observable}
        {Scale = Scale}
        {ShellVolume = ShellVolume}
        {Root = Root}
        {Polymer = Polymer}
        {Link = Link}
        {Cluster = Cluster}
        {FiniteVolume = FiniteVolume}
        {ShellScale = ShellScale}
        {ShellRoot = ShellRoot}
        {PhysicalIncompatible = PhysicalIncompatible}
        family dataSet laws)
    cutoff left right →
  Jet.NormalizedWilsonMarkedLogJetExpansion
    {Cluster = Cluster}
    (R573.r278MomentAlgebra
      (R575.rationalAbsoluteCovarianceExtension laws)
      (Gram.measureSequence dataSet cutoff))
    left right
markedJetExpansionAt source cutoff left right =
  SourceJet.asNormalizedWilsonMarkedLogJetExpansion
    (normalizedJetAt source cutoff left right)

asDirectLiteralWilsonMarkedJetLocalizationSource :
  ∀ {Measure Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume
      ShellScale ShellRoot PhysicalIncompatible family dataSet laws} →
  SourceFirstLiteralWilsonJetLocalization
    {Measure = Measure}
    {Observable = Observable}
    {Scale = Scale}
    {ShellVolume = ShellVolume}
    {Root = Root}
    {Polymer = Polymer}
    {Link = Link}
    {Cluster = Cluster}
    {FiniteVolume = FiniteVolume}
    {ShellScale = ShellScale}
    {ShellRoot = ShellRoot}
    {PhysicalIncompatible = PhysicalIncompatible}
    family dataSet laws →
  JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource
    {Measure = Measure}
    {Observable = Observable}
    {Cluster = Cluster}
    {Scale = ShellScale}
    {Volume = FiniteVolume}
    {Root = ShellRoot}
    dataSet laws
asDirectLiteralWilsonMarkedJetLocalizationSource
    {family = family} source = record
  { JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.markedJetExpansion =
      markedJetExpansionAt source
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.shellData =
      shellData source
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.scaleOfCutoff =
      scaleOfCutoff source
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.volumeOfCutoff =
      PhysicalKP.LiteralTwoWilsonSourceFirstKoteckyPreissFamily.volumeOfCutoff
        family
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.physicalDistance =
      physicalDistance source
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.connectingRoot =
      connectingRoot source
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.ConnectingClusterMeetsBothSupports =
      ConnectingClusterMeetsBothSupports source
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.shellCharge =
      shellCharge source
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.pointwiseWilsonJetLocalization =
      pointwiseLiteralWilsonJetLocalization source
  ; JetLocalization.DirectLiteralWilsonMarkedJetLocalizationSource.localizedShellChargeSum =
      λ cutoff left right →
        localizedLiteralShellChargeSum source cutoff left right
  }

sourceFirstLiteralWilsonJetsCompileToR556 :
  ∀ {Measure Observable Scale ShellVolume Root Polymer Link Cluster FiniteVolume
      ShellScale ShellRoot PhysicalIncompatible family dataSet laws}
    (source :
      SourceFirstLiteralWilsonJetLocalization
        {Measure = Measure}
        {Observable = Observable}
        {Scale = Scale}
        {ShellVolume = ShellVolume}
        {Root = Root}
        {Polymer = Polymer}
        {Link = Link}
        {Cluster = Cluster}
        {FiniteVolume = FiniteVolume}
        {ShellScale = ShellScale}
        {ShellRoot = ShellRoot}
        {PhysicalIncompatible = PhysicalIncompatible}
        family dataSet laws)
    (semantics :
      JetLocalization.WilsonJetDownstreamSemantics dataSet) →
  R556.IndexedSourceFirstWilsonCovarianceData
    {Measure = Measure}
    {Observable = Observable}
    {Scale = ShellScale}
    {Volume = FiniteVolume}
    {Root = ShellRoot}
    dataSet
    (R575.rationalAbsoluteCovarianceExtension laws)
sourceFirstLiteralWilsonJetsCompileToR556 source semantics =
  JetLocalization.directLiteralWilsonMarkedJetsCompileToR556
    (asDirectLiteralWilsonMarkedJetLocalizationSource source)
    semantics

independentNormalizedJetFamilySelectionRequired : Bool
independentNormalizedJetFamilySelectionRequired = false

sourceFirstLiteralWilsonJetLocalizationCompilerLevel : ProofLevel
sourceFirstLiteralWilsonJetLocalizationCompilerLevel = machineChecked

-- Exact live H1 source payments on this route.
literalSourceFirstClusterBidegree11GermLevel : ProofLevel
literalSourceFirstClusterBidegree11GermLevel =
  SourceJet.sourceFirstClusterJetGermIdentificationLevel

literalNormalizedPhysicalLogJetIsKPClusterJetSumLevel : ProofLevel
literalNormalizedPhysicalLogJetIsKPClusterJetSumLevel =
  SourceJet.sourceFirstNormalizedPhysicalLogJetIdentificationLevel

literalPointwiseWilsonJetLocalizationLevel : ProofLevel
literalPointwiseWilsonJetLocalizationLevel = conditional

literalLocalizedWilsonShellChargeSumLevel : ProofLevel
literalLocalizedWilsonShellChargeSumLevel = conditional
